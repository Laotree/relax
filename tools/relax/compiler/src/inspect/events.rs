//! Events: what an agent must hear about without asking (DESIGN.md §2.1, BRIEF "no human in the
//! loop"): panics (parked at the panic point), hangs, deadlocks, memory growth. Each event is one
//! compact JSON line with a sequence number and drill-down commands. `watch` blocks until the next
//! one and returns it (an agent's background task then exits: its notification), `events
//! follow=1` streams them (one line each), and `relax run --agent` prints them on stderr too.
//! Repeats of the same event (kind + key) within 30 s are counted, not sent again.
//!
//! Panic parking: a panic in JIT code on a program thread waits at the panic point (its stack
//! intact for `stacks`) while a watcher is attached or under `--agent`, until a client resumes it
//! or the wait times out; then it unwinds as usual. With nobody watching, the first panic at a site
//! parks briefly (RELAX_PANIC_PARK seconds, default 2) and says how to attach.

use super::{json_str, now_ms, Out, Req};
use std::collections::VecDeque;
use std::sync::atomic::{AtomicU32, AtomicU64, Ordering::{Relaxed, SeqCst}};
use std::sync::{Condvar, Mutex};

pub struct Event {
    pub seq: u64,
    pub kind: &'static str,
    key: String,
    /// the whole event as one JSON object
    pub json: String,
    at: std::time::Instant,
}

const KEEP: usize = 256;
static EVENTS: Mutex<VecDeque<Event>> = Mutex::new(VecDeque::new());
static NEW: Condvar = Condvar::new();
static SEQ: AtomicU64 = AtomicU64::new(0);
/// sessions in `watch` / `events follow=1` now
pub static WATCHERS: AtomicU32 = AtomicU32::new(0);

pub const KINDS: &[&str] = &["panic", "hang", "deadlock", "mem", "spike", "rtstall", "scripterr", "patchrefused"];

/// Records an event (`fields`: the kind-specific JSON members, without braces). Returns its seq,
/// or 0 when it repeated one sent in the last 30 s.
pub fn emit(kind: &'static str, key: &str, fields: &str) -> u64 {
    let mut q = EVENTS.lock().unwrap_or_else(|e| e.into_inner());
    if let Some(e) = q.iter().rev().find(|e| e.kind == kind && e.key == key) {
        if e.at.elapsed().as_secs() < 30 {
            return 0;
        }
    }
    let seq = SEQ.fetch_add(1, SeqCst) + 1;
    let json = format!(
        "{{\"event\":\"{}\",\"seq\":{},\"pid\":{},\"app\":{},\"at_ms\":{},{}}}",
        kind,
        seq,
        std::process::id(),
        json_str(&super::APP.lock().unwrap_or_else(|e| e.into_inner())),
        now_ms(),
        fields
    );
    if super::AGENT.load(Relaxed) {
        eprintln!("relax-event: {}", json);
    }
    q.push_back(Event { seq, kind, key: key.to_string(), json, at: std::time::Instant::now() });
    while q.len() > KEEP {
        q.pop_front();
    }
    NEW.notify_all();
    seq
}

fn wanted(on: &Option<Vec<String>>, kind: &str) -> bool {
    on.as_ref().map_or(true, |v| v.iter().any(|k| k == kind))
}

fn kinds(req: &Req) -> Option<Vec<String>> {
    req.get("on").map(|s| s.split(',').map(|x| x.trim().to_string()).filter(|x| !x.is_empty()).collect())
}

/// `watch [on=..] [since=<seq>] [timeout_s=N]`: the first event after `since` (default: now; a
/// panic parked now always counts), as one line.
pub fn cmd_watch(req: &Req, out: &mut Out) {
    let on = kinds(req);
    let parked_since = PARKED.lock().unwrap_or_else(|e| e.into_inner()).iter().map(|p| p.seq).min().map_or(u64::MAX, |s| s - 1);
    let since = req.get("since").and_then(|s| s.parse().ok()).unwrap_or_else(|| SEQ.load(SeqCst).min(parked_since));
    let timeout = req.num("timeout_s", 0);
    let t0 = std::time::Instant::now();
    WATCHERS.fetch_add(1, SeqCst);
    let mut q = EVENTS.lock().unwrap_or_else(|e| e.into_inner());
    let found = loop {
        if let Some(e) = q.iter().find(|e| e.seq > since && wanted(&on, e.kind)) {
            break Some((e.seq, e.json.clone()));
        }
        if timeout > 0 && t0.elapsed().as_secs() >= timeout {
            break None;
        }
        q = NEW.wait_timeout(q, std::time::Duration::from_millis(500)).unwrap_or_else(|e| e.into_inner()).0;
    };
    drop(q);
    WATCHERS.fetch_sub(1, SeqCst);
    match found {
        Some((seq, json)) => out.line(&format!("{},\"rearm\":\"watch since={}\"}}", &json[..json.len() - 1], seq)),
        None => out.line(&format!("{{\"event\":\"none\",\"waited_s\":{},\"rearm\":\"watch since={}\"}}", timeout, since)),
    }
}

/// `events [since=<seq>] [follow=1] [on=..]`: the kept events after `since` (default: the last
/// 20), then with follow=1 each new one as it comes, until the client goes away.
pub fn cmd_events(req: &Req, out: &mut Out) {
    let on = kinds(req);
    let follow = req.get("follow") == Some("1");
    let mut since = req.get("since").and_then(|s| s.parse().ok()).unwrap_or_else(|| SEQ.load(SeqCst).saturating_sub(20));
    out.measured("events", "event queue", &[]);
    if follow {
        // a stream is unbounded by design
        out.limit = usize::MAX;
        WATCHERS.fetch_add(1, SeqCst);
    }
    loop {
        let batch: Vec<(u64, String)> = {
            let q = EVENTS.lock().unwrap_or_else(|e| e.into_inner());
            q.iter().filter(|e| e.seq > since && wanted(&on, e.kind)).map(|e| (e.seq, e.json.clone())).collect()
        };
        for (seq, j) in &batch {
            out.line(j);
            since = *seq;
        }
        if !follow || !out.flush() {
            break;
        }
        let q = EVENTS.lock().unwrap_or_else(|e| e.into_inner());
        if q.back().map_or(true, |e| e.seq <= since) {
            let _ = NEW.wait_timeout(q, std::time::Duration::from_secs(5));
        }
        // a heartbeat-free stream: a closed client is noticed at the next write
    }
    if follow {
        WATCHERS.fetch_sub(1, SeqCst);
    }
}

// ------------------------------------------------------------------ parked panics

struct Parked {
    id: u64,
    seq: u64,
    /// 0 waiting, 1 resume as a panic
    decision: AtomicU32,
}

static PARKED: Mutex<Vec<std::sync::Arc<Parked>>> = Mutex::new(Vec::new());
static RESUME: Condvar = Condvar::new();
static PANIC_IDS: AtomicU64 = AtomicU64::new(0);
/// sites that parked already with nobody watching (the next panic there does not wait again)
static SITES_SEEN: Mutex<Vec<(u64, String)>> = Mutex::new(Vec::new());

fn park_secs_unwatched() -> u64 {
    std::env::var("RELAX_PANIC_PARK").ok().and_then(|v| v.parse().ok()).unwrap_or(2)
}

/// A panic is about to unwind on this (program) thread: park it if someone may want to look
/// (jit.rs raise_with; not on the owner, not without a recovery point).
pub fn on_panic(info: &crate::jit::PanicInfo) {
    if !super::STARTED.load(Relaxed) || crate::owner::is_owner() {
        return;
    }
    let watched = WATCHERS.load(SeqCst) > 0 || super::AGENT.load(Relaxed);
    let key = format!("{}|{}|{}", info.site, info.location, info.message);
    if !watched {
        let mut seen = SITES_SEEN.lock().unwrap_or_else(|e| e.into_inner());
        if park_secs_unwatched() == 0 || seen.iter().any(|s| s.1 == key) {
            return;
        }
        seen.push((info.site, key.clone()));
    }
    let id = PANIC_IDS.fetch_add(1, SeqCst) + 1;
    let mut partial = Vec::new();
    let top: Vec<u64> = info.frames.iter().copied().take(12).collect();
    // panic frames are lookup pcs already (collect_frames subtracts one); symbolise wants the
    // first as is and the rest as return addresses
    let as_raw: Vec<u64> = top.iter().enumerate().map(|(i, &p)| if i == 0 { p } else { p + 1 }).collect();
    let frames = super::symbolise(&[as_raw], &mut partial).pop().unwrap_or_default();
    let location = if info.location.is_empty() { panic_site(info.site) } else { info.location.clone() };
    let fr: Vec<String> = frames.iter().map(super::frame_json).collect();
    let me = crate::os::thread::current();
    let thread = if me == crate::jit::MAIN_TID.load(Relaxed) { "main".to_string() } else { crate::os::thread::name(me) };
    let wait_s = if watched { 600 } else { park_secs_unwatched() };
    let fields = format!(
        "\"id\":\"P{}\",\"kind\":{},\"message\":{},\"location\":{},\"thread\":{},\"frames\":[{}],\"parked_s\":{},\"more\":[\"stacks\",\"why-hung\",\"resume P{} panic\"]",
        id,
        json_str(&info.kind),
        json_str(&super::short(&info.message, 400)),
        json_str(&location),
        json_str(&thread),
        fr.join(","),
        wait_s,
        id
    );
    let mut list = PARKED.lock().unwrap_or_else(|e| e.into_inner());
    let seq = emit("panic", &format!("P{}", id), &fields);
    let p = std::sync::Arc::new(Parked { id, seq, decision: AtomicU32::new(0) });
    list.push(p.clone());
    if !watched {
        eprintln!(
            "relax: panic parked on thread {} ({}) for {} s -- attach: relax inspect {} panics (resume P{} panic)",
            thread,
            super::short(&info.message, 120),
            wait_s,
            std::process::id(),
            id
        );
    }
    let t0 = std::time::Instant::now();
    while p.decision.load(SeqCst) == 0 && t0.elapsed().as_secs() < wait_s {
        // an unwatched park ends early once nobody could still attach in time
        list = RESUME.wait_timeout(list, std::time::Duration::from_millis(200)).unwrap_or_else(|e| e.into_inner()).0;
    }
    list.retain(|x| x.id != id);
}

/// "file:line:col" of a compiler-known panic site.
fn panic_site(site: u64) -> String {
    let up = crate::jit::current_unit();
    if up.is_null() || site == u64::MAX {
        return String::new();
    }
    crate::owner::call_within(crate::owner::Class::Job, 300, move || {
        let u = unsafe { &*up };
        let s = u.sites.lock().unwrap_or_else(|e| e.into_inner()).get(site as usize).map(|st| (st.file, st.pos));
        s.map(|(f, p)| u.pos_str(f, p)).unwrap_or_default()
    })
    .unwrap_or_default()
}

pub fn cmd_panics(out: &mut Out) {
    let list = PARKED.lock().unwrap_or_else(|e| e.into_inner());
    out.measured("parked panics", "event queue", &[]);
    let q = EVENTS.lock().unwrap_or_else(|e| e.into_inner());
    for p in list.iter() {
        if let Some(e) = q.iter().find(|e| e.seq == p.seq) {
            out.line(&e.json);
        } else {
            out.line(&format!("{{\"id\":\"P{}\"}}", p.id));
        }
    }
}

/// `resume <Pn> panic`: the parked panic unwinds as usual.
pub fn cmd_resume(req: &Req, out: &mut Out) {
    let Some(id) = req.pos.first().and_then(|s| s.trim_start_matches('P').parse::<u64>().ok()) else {
        out.err("usage: resume <panic id> panic");
        return;
    };
    let how = req.pos.get(1).map(String::as_str).unwrap_or("panic");
    if how != "panic" {
        out.err("only `panic` is available yet (retry / restart / return come with instrumented builds)");
        return;
    }
    let list = PARKED.lock().unwrap_or_else(|e| e.into_inner());
    match list.iter().find(|p| p.id == id) {
        Some(p) => {
            p.decision.store(1, SeqCst);
            RESUME.notify_all();
            out.line(&format!("{{\"resumed\":\"P{}\",\"as\":\"panic\"}}", id));
        }
        None => out.err(&format!("no parked panic P{}", id)),
    }
}

// ------------------------------------------------------------------ detectors

/// The detector thread: hangs (the main thread blocked in a registry wait past its threshold),
/// deadlocks (a wait cycle seen twice in a row), memory growth (RSS). Four checks a second, each
/// a registry scan and one resident-size read: nothing the program pays for.
pub fn start() {
    let _ = std::thread::Builder::new().name("relax-inspect-watch".into()).spawn(|| {
        let hang_ms: u64 = std::env::var("RELAX_INSPECT_HANG_MS").ok().and_then(|v| v.parse().ok()).unwrap_or(3000);
        let mut last_cycle: Vec<u64> = Vec::new();
        let mut base_rss = 0u64;
        let mut tick = 0u64;
        let (mut marked_main, mut marked_present) = (false, false);
        loop {
            std::thread::sleep(std::time::Duration::from_millis(250));
            tick += 1;
            let waits = crate::waits::snapshot();
            let main = crate::jit::MAIN_TID.load(Relaxed);
            let now = crate::clock::wall_ns();
            // the main thread waiting: on the owner after the first present (a compile stall),
            // on a lock / condvar / join any time
            if let Some(w) = waits.iter().find(|w| w.thread == main && main != 0) {
                let ms = now.saturating_sub(w.since_ns) / 1_000_000;
                let present = crate::jit::FIRST_PRESENT.load(Relaxed);
                let relevant = match w.kind {
                    crate::waits::Kind::Owner => present,
                    crate::waits::Kind::Futex => w.label != "park" && w.label != "condvar" || ms > hang_ms * 4,
                    crate::waits::Kind::None => false,
                    _ => true,
                };
                if relevant && ms >= hang_ms {
                    let mut list = super::threads::list();
                    super::name_handles(&mut list);
                    let what = super::wait_text(w, &list);
                    emit("hang", &format!("main|{:?}|{:#x}", w.kind, w.object), &format!("\"thread\":\"main\",\"blocked_ms\":{},\"waits\":{},\"more\":[\"why-hung\",\"stacks thread=main\"]", ms, json_str(&what)));
                }
            }
            // a cycle among registry waits (thread -> holder handle)
            let cycle = super::hang::registry_cycle(&waits);
            if !cycle.is_empty() && cycle == last_cycle {
                let mut list = super::threads::list();
                super::name_handles(&mut list);
                let names: Vec<String> = cycle.iter().map(|h| json_str(&super::thread_label(*h, &list))).collect();
                let mut key = cycle.clone();
                key.sort_unstable();
                emit("deadlock", &format!("{:?}", key), &format!("\"cycle\":[{}],\"more\":[\"why-hung\"]", names.join(",")));
            }
            last_cycle = cycle;
            super::heap::expire();
            // the memory timeline and its phase markers
            let rss = crate::memstat::resident();
            super::mem::tick(tick, rss);
            if !marked_main && main != 0 {
                marked_main = true;
                super::mem::mark("main");
            }
            if !marked_present && crate::jit::FIRST_PRESENT.load(Relaxed) {
                marked_present = true;
                super::mem::mark("first present");
            }
            // memory: resident size against the level 5 s after the first present
            if tick % 8 == 0 && crate::jit::FIRST_PRESENT.load(Relaxed) {
                if base_rss == 0 {
                    base_rss = rss;
                } else if rss > base_rss + (base_rss / 2).max(512 << 20) {
                    emit("mem", "rss", &format!("\"rss_mb\":{},\"from_mb\":{},\"more\":[\"memory\"]", rss >> 20, base_rss >> 20));
                    base_rss = rss;
                }
            }
        }
    });
}
