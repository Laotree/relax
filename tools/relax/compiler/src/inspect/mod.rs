//! relax inspect: a running program answers questions about itself (local/agent_state/fast-rust/
//! inspect/DESIGN.md). One thread per `relax run` listens on a Unix socket next to a discovery file
//! in the temp dir; a client (`relax inspect <pid|app|all> <command>`, or any agent speaking the
//! line protocol) sends one request per line and reads JSON lines back, ending with an `end` line.
//!
//! The basics never need the owner thread: thread lists and stacks come from the OS and the code
//! tables, waits from the lock-free wait registry, events from this module's own queue. Only names
//! and lines of JIT frames ask the owner (Job class: served inside its pumps too), with a short
//! timeout after which the reply says what it could not resolve.

pub mod client;
#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
pub mod cfi;
pub mod events;
mod hang;
pub mod heap;
pub mod instrument;
pub mod patches;
pub mod probes;
pub mod mem;
mod prof;
pub mod timeline;
mod symbols;
pub mod threads;

#[cfg(not(all(target_os = "linux", target_arch = "x86_64")))]
pub mod cfi {
    //! (Linux x86_64 only: other targets walk host frames by their frame pointers)
    pub fn refresh() {}
}

use std::sync::atomic::{AtomicBool, Ordering::Relaxed};
use std::sync::Mutex;

/// The inspect thread runs (a socket is listening).
static STARTED: AtomicBool = AtomicBool::new(false);
/// `relax run --agent`: panics park, events also go to stderr.
pub static AGENT: AtomicBool = AtomicBool::new(false);
/// os id of the inspect threads (not captured: they are the ones asking)
static SERVER_TIDS: Mutex<Vec<u64>> = Mutex::new(Vec::new());
/// one capture at a time (the Linux handshake has one slot)
static CAPTURE: Mutex<()> = Mutex::new(());
static APP: Mutex<String> = Mutex::new(String::new());

pub use makepad_inspect_serve::{json_str, now_ms, paths, Out, Req};

/// Starts the inspect thread for program `app` (once per process; RELAX_INSPECT=0: off).
pub fn start(app: &str) {
    if std::env::var("RELAX_INSPECT").map_or(false, |v| v == "0") || STARTED.swap(true, Relaxed) {
        return;
    }
    *APP.lock().unwrap() = app.to_string();
    let pid = std::process::id();
    let log = crate::tui::session_log_path().map(|p| p.display().to_string()).unwrap_or_default();
    let extra = format!(",\"session_log\":{},\"relax\":{},\"agent\":{}", json_str(&log), json_str(crate::jit::PROVENANCE), AGENT.load(Relaxed));
    let host = makepad_inspect_serve::Host {
        dispatch,
        thread_enter: || {
            SERVER_TIDS.lock().unwrap().push(threads::self_os_id());
            heap::exclude_this_thread();
        },
        thread_exit: || {
            let me = threads::self_os_id();
            SERVER_TIDS.lock().unwrap().retain(|t| *t != me);
        },
    };
    let sock = match makepad_inspect_serve::listen(app, &extra, host) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("relax-inspect: cannot listen on {}: {}", paths(pid).0.display(), e);
            return;
        }
    };
    eprintln!("relax-inspect: pid {} app {} socket {} (relax inspect {} help)", pid, app, sock.display(), pid);
    events::start();
    if AGENT.load(Relaxed) {
        timeline::set_frame_watch(true);
    }
    heap::start_from_env();
}

/// The commands: (name, arguments, what it answers).
pub const COMMANDS: &[(&str, &str, &str)] = &[
    ("why-hung", "[probe_ms=200]", "is it stuck and why: verdict (deadlock / blocked / busy / idle), the wait chain or cycle, stacks of the threads in it"),
    ("why-slow", "[s=3]", "where the time goes: ranked findings -- the main thread's CPU split (program / compiles / Relax runtime / system), its hot fns, the owner's service, other busy threads"),
    ("prof", "[s=3] [hz=200] [threads=all|main|owner|program|compiler|<name>] [n=15] [save=1]", "sampling CPU profile of JIT and host frames: per-thread CPU, activity split, top fns by self time with their hottest line, inclusive fns; save=1 writes folded stacks"),
    ("timeline", "start [max_s=30] | stop | frames [n=30] | frame <n|slowest> | save", "dataflow timeline: record UI phases, owner service, waits and wakes; per frame the critical path, work vs critical path vs wall, longest waits and who ended them; save = Chrome trace JSON"),
    ("watch", "[on=panic,hang,...] [since=<seq>] [timeout_s=N]", "block until the next event (panic, hang, ...) and answer it as one JSON line; re-arm with since=<seq>"),
    ("events", "[follow=1] [since=<seq>] [on=...]", "the recent events (follow=1: stream one JSON line per new event)"),
    ("panics", "", "panics parked now, waiting for a decision"),
    ("resume", "<panic id> panic|retry|restart|return <v>[,<v>]", "decide a parked panic: unwind as usual, re-run the retry boundary's unit, restart the restartable fn, or make it return the values"),
    ("memory", "[compiler=1] [n=24]", "where the memory is and why: RSS by mapping kind, malloc in use vs held free, Relax's own parts, findings, growth since the last `memory`"),
    ("diff", "<snap a> <snap b|now>", "memory growth between two snapshots, largest first"),
    ("mem", "snap <name> | timeline [from_ms= to_ms=]", "keep a named memory snapshot; resident size over time with phase markers and the peak's phase"),
    ("heap", "start [rate=65536] [ttl_s=600] | top [by=live|alloc|freed|peak] | snap <name> | diff <a> <b|now> | path H<id> | stop | status", "program heap by allocation stack (JIT-patched allocator hooks, byte-sampled): live, allocated, freed; growth and leaks between snapshots"),
    ("top", "by=time|alloc|bytes|live [s=3] [n=15]", "the top functions by CPU time (prof) or allocation sites by allocated / live bytes (heap)"),
    ("frame", "<n|slowest>", "one frame of the last timeline: UI phases, critical path, waits and who ended them (alias of timeline frame)"),
    ("path", "<H<n>|R<n>>", "the full stack of a heap site id"),
    ("count", "<fn> [time=1]", "exact call counts (and inclusive time) of every slot of a fn: its code is rebuilt with probes and installed as a probe group G<n>"),
    ("break", "<fn>|<file>:<line>", "breakpoint: a hit parks the thread at the call (stack intact) and raises a `break` event K<n>"),
    ("restartable", "<fn>", "a panic through the fn can be resumed with `restart` (the fn runs again from its entry with its original arguments) or `return <value>` (the call returns the value; integer-class returns)"),
    ("probe", "add <fn|file:line> <probe.rs|code> [mutate=1] | list | read P<n> | rm <P<n>|all>", "injected Rust probes: your `fn probe(<the hooked fn's params>)` runs at the hook; std::relax::probe::{emit, count, hist, sample, pause} record for it"),
    ("probes", "", "installed probes with hits and time, parked breakpoints, pause state"),
    ("rm", "<G<n>|all>", "removes probe groups: the code they replaced comes back (no recompile)"),
    ("continue", "[K<n>|all]", "lets parked breakpoint hits go"),
    ("pause", "", "stops the program's threads (Relax's and inspect's keep running); stacks work while paused"),
    ("resume", "", "after pause: the program runs again (`resume P<n> panic` releases a parked panic)"),
    ("gpu", "[top [by=bytes|owner|site|churn]|idle [s=30]|snap <name>|diff <a> <b|now>|path G<id>]", "where the GPU memory is (native makepad apps: MAKEPAD_INSPECT=1): totals by kind and owner against the device, automatic findings; top / idle / snap / diff / path"),
    ("vms", "", "every live Splash VM: label, thread, heap objects / strings / arrays and bytes, GC runs and time, errors, evaluations"),
    ("threads", "", "every thread: name, role, state, CPU time, what it waits on"),
    ("stacks", "[thread=<name|tid|main|owner|all>] [depth=12]", "symbolised stacks (identical stacks folded)"),
    ("waits", "", "the wait registry: who waits for what, held by whom"),
    ("owner", "", "the owner thread: what it serves, for whom, queue"),
    ("help", "[<cmd>|schema]", "this list; `help schema`: a JSON tool definition for agents"),
];

fn dispatch(req: &Req, out: &mut Out) {
    match req.cmd.as_str() {
        "help" => help(req, out),
        "ping" => out.line(&format!("{{\"pid\":{},\"app\":{},\"ms\":{}}}", std::process::id(), json_str(&APP.lock().unwrap()), now_ms())),
        "threads" => cmd_threads(out),
        "stacks" => cmd_stacks(req, out),
        "waits" => cmd_waits(out),
        "owner" => cmd_owner(out),
        "why-hung" | "hang" => hang::why_hung(req, out),
        "memory" => mem::cmd_memory(req, out),
        "prof" => prof::cmd_prof(req, out),
        "timeline" => timeline::cmd_timeline(req, out),
        // question-shaped aliases (DESIGN.md §2.1)
        "frame" => timeline::cmd_timeline(&shifted(req, "frame"), out),
        "frames" => timeline::cmd_timeline(&shifted(req, "frames"), out),
        "top" => match req.get("by").unwrap_or("time") {
            "time" | "cpu" => prof::cmd_prof(req, out),
            "alloc" | "bytes" | "live" | "churn" => heap::cmd_heap(&shifted(&with_by(req), "top"), out),
            b => out.err(&format!("top by={}: time | alloc | bytes | live | churn", b)),
        },
        "path" => match req.pos.first().map(|p| p.chars().next().unwrap_or(' ')) {
            Some('H') | Some('R') => heap::cmd_heap(&shifted(req, "path"), out),
            _ => out.err("path <H<n>|R<n>>: heap stacks (frame ids: `frame <n>`)"),
        },
        "why-slow" => prof::cmd_why_slow(req, out),
        "mem" => mem::cmd_mem(req, out),
        "diff" => mem::cmd_diff(req, out),
        "heap" => heap::cmd_heap(req, out),
        "vms" => cmd_vms(out),
        // the program's GPU ledger (makepad-platform, MAKEPAD_INSPECT=1) answers on its own socket
        "gpu" => {
            if !makepad_inspect_serve::forward(req, out) {
                out.err("no GPU ledger in this program (a makepad-platform app under relax run, or a native app started with MAKEPAD_INSPECT=1, answers it)");
            }
        }
        "probe" => probes::cmd(req, out),
        "watch" => events::cmd_watch(req, out),
        "events" => events::cmd_events(req, out),
        "panics" => events::cmd_panics(out),
        "resume" if !req.pos.is_empty() => events::cmd_resume(req, out),
        "count" | "break" | "restartable" | "probes" | "rm" | "continue" | "pause" | "resume" => instrument::cmd(req, out),
        "" => out.err("empty request"),
        c => out.err(&format!("unknown command `{}` (try `help`)", c)),
    }
}

/// `req` with `word` put in front of its positional words (an alias for a subcommand).
fn shifted(req: &Req, word: &str) -> Req {
    let mut pos = vec![word.to_string()];
    pos.extend(req.pos.iter().cloned());
    Req { cmd: req.cmd.clone(), pos, kv: req.kv.clone() }
}

/// `top by=bytes|alloc` speaks heap's words (alloc = allocated bytes, bytes / live = live bytes).
fn with_by(req: &Req) -> Req {
    let mut kv: Vec<(String, String)> = req.kv.iter().filter(|x| x.0 != "by").cloned().collect();
    let by = match req.get("by") {
        Some("alloc") => "alloc",
        Some("churn") => "freed",
        _ => "live",
    };
    kv.push(("by".into(), by.into()));
    Req { cmd: req.cmd.clone(), pos: req.pos.clone(), kv }
}

fn help(req: &Req, out: &mut Out) {
    if req.pos.first().map(String::as_str) == Some("schema") {
        out.line(&schema());
        return;
    }
    out.measured("commands", "static", &[]);
    for (name, args, what) in COMMANDS {
        if let Some(w) = req.pos.first() {
            if w != name {
                continue;
            }
        }
        out.line(&format!("{{\"cmd\":{},\"args\":{},\"answers\":{}}}", json_str(name), json_str(args), json_str(what)));
    }
}

/// A tool definition for agent / MCP-style clients: one tool, `relax_inspect`, whose `command`
/// is one line of this protocol.
pub fn schema() -> String {
    let cmds: Vec<String> = COMMANDS.iter().map(|(n, a, w)| format!("{} {} -- {}", n, a, w)).collect();
    format!(
        "{{\"name\":\"relax_inspect\",\"description\":{},\"input_schema\":{{\"type\":\"object\",\"properties\":{{\"target\":{{\"type\":\"string\",\"description\":\"pid, app name, or all\"}},\"command\":{{\"type\":\"string\",\"description\":\"one request line, e.g. `why-hung` or `stacks thread=main`\"}}}},\"required\":[\"target\",\"command\"]}}}}",
        json_str(&format!("Ask a running relax app about itself. Run as `relax inspect <target> <command>`. Commands:\n{}", cmds.join("\n")))
    )
}

// ------------------------------------------------------------------ threads and stacks

/// What a thread is to Relax (its role), from its name.
fn role(name: &str, os_id: u64, handle: u64) -> &'static str {
    let main = crate::jit::MAIN_TID.load(Relaxed);
    if handle != 0 && handle == main {
        return "main";
    }
    if handle != 0 && handle == crate::owner::owner_tid() {
        return "owner";
    }
    let _ = os_id;
    match name {
        n if n.starts_with("relax-inspect") => "inspect",
        n if n.starts_with("relax-spec") || n.starts_with("relax-O2") || n.starts_with("relax-o3") || n.starts_with("relax-ahead") || n == "gandalf" || n.starts_with("relax-check") => "compiler",
        n if n.starts_with("relax-") => "relax",
        _ => "program",
    }
}

/// The threads with their stacks, captured now (the inspect threads themselves left out).
pub struct Captured {
    pub t: threads::Thread,
    pub frames: Vec<u64>,
    pub lr: u64,
    pub sp: u64,
    pub err: Option<&'static str>,
}

pub fn capture_all(want: &dyn Fn(&threads::Thread) -> bool) -> Vec<Captured> {
    cfi::refresh();
    let _g = CAPTURE.lock().unwrap_or_else(|e| e.into_inner());
    let skip = SERVER_TIDS.lock().unwrap().clone();
    let mut out = Vec::new();
    let mut raw = threads::Raw::new();
    let mut list = threads::list();
    name_handles(&mut list);
    for t in list {
        if skip.contains(&t.os_id) || !want(&t) {
            continue;
        }
        let r = threads::capture(&t, &mut raw);
        let mut t = t;
        if t.handle == 0 && raw.handle != 0 {
            t.handle = raw.handle;
        }
        out.push(Captured { frames: raw.frames().to_vec(), lr: raw.lr, sp: raw.sp, err: r.err(), t });
    }
    out
}

/// Fills in the pthread handles the OS listing lacks (Linux) for the threads Relax names by handle:
/// main, the owner, and every thread in or named by the wait registry.
pub fn name_handles(list: &mut [threads::Thread]) {
    if list.iter().all(|t| t.handle != 0) {
        return;
    }
    let mut hs: Vec<u64> = vec![crate::jit::MAIN_TID.load(Relaxed), crate::owner::owner_tid()];
    for w in crate::waits::snapshot() {
        hs.push(w.thread);
        if w.kind != crate::waits::Kind::Futex {
            hs.push(w.holder);
        }
    }
    hs.extend(crate::waits::threads());
    hs.sort_unstable();
    hs.dedup();
    for h in hs {
        if let Some(tid) = threads::tid_of_handle(h) {
            if let Some(t) = list.iter_mut().find(|t| t.os_id == tid && t.handle == 0) {
                t.handle = h;
            }
        }
    }
}

/// A symbolised frame.
#[derive(Clone)]
pub struct Frame {
    pub pc: u64,
    /// fn name (JIT: the slot's name; host: the demangled symbol)
    pub name: String,
    /// file:line:col for JIT frames
    pub at: String,
    /// "jit" (with its tier) or the host image's file name
    pub module: String,
}

/// Names for raw pcs: JIT frames by the unit (one owner Job request; on timeout `slot#id+off`),
/// host frames by the images' symbol tables. `lookup` pcs are return addresses except the first.
pub fn symbolise(frames: &[Vec<u64>], partial: &mut Vec<String>) -> Vec<Vec<Frame>> {
    symbolise_within(frames, partial, 1000)
}

/// `symbolise`, waiting at most `ms` for the owner (why-hung asks briefly: the owner may be the
/// thing that hangs).
pub fn symbolise_within(frames: &[Vec<u64>], partial: &mut Vec<String>, ms: u64) -> Vec<Vec<Frame>> {
    let mut jit_pcs: Vec<u64> = Vec::new();
    for f in frames {
        for (i, &pc) in f.iter().enumerate() {
            let look = if i == 0 { pc } else { pc.wrapping_sub(1) };
            if crate::jit::in_jit_code(look) {
                jit_pcs.push(look);
            }
        }
    }
    jit_pcs.sort_unstable();
    jit_pcs.dedup();
    let names = jit_names(&jit_pcs, partial, ms);
    frames
        .iter()
        .map(|f| {
            f.iter()
                .enumerate()
                .map(|(i, &pc)| {
                    let look = if i == 0 { pc } else { pc.wrapping_sub(1) };
                    if let Ok(k) = jit_pcs.binary_search(&look) {
                        let (name, at, tier) = names[k].clone();
                        Frame { pc, name, at, module: tier }
                    } else {
                        match symbols::host_symbol(look) {
                            Some((name, module, _)) => Frame { pc, name, at: String::new(), module },
                            None => Frame { pc, name: format!("{:#x}", pc), at: String::new(), module: "?".into() },
                        }
                    }
                })
                .collect()
        })
        .collect()
}

/// (name, file:line:col, tier) of JIT pcs.
fn jit_names(pcs: &[u64], partial: &mut Vec<String>, ms: u64) -> Vec<(String, String, String)> {
    let up = crate::jit::current_unit();
    if pcs.is_empty() || up.is_null() {
        return pcs.iter().map(|pc| (format!("jit {:#x}", pc), String::new(), "jit".into())).collect();
    }
    let pcs_v = pcs.to_vec();
    let r = crate::owner::call_within(crate::owner::Class::Job, ms, move || {
        let u = unsafe { &*up };
        pcs_v
            .iter()
            .map(|&pc| match u.pc_to_src(pc) {
                Some((id, at)) => {
                    let f = &u.fns[id as usize];
                    let cur = pc >= f.code && pc < f.code + f.code_len as u64;
                    let tier = if !cur && f.retired.iter().any(|r| pc >= r.0 && pc < r.0 + r.1 as u64) {
                        "jit/retired"
                    } else if !cur {
                        "jit/old"
                    } else if f.o3.load(Relaxed) {
                        "jit/O3"
                    } else {
                        "jit"
                    };
                    (display_name(u, id, 0), at, tier.to_string())
                }
                None => (format!("jit {:#x}", pc), String::new(), "jit".into()),
            })
            .collect::<Vec<_>>()
    });
    match r {
        Some(v) => v,
        None => {
            partial.push(format!("jit names: owner busy ({})", crate::owner::serving_note()));
            // the code index is a leaf lock: slot ids without the owner
            let u = unsafe { &*up };
            pcs.iter()
                .map(|&pc| match u.code.try_read().ok().and_then(|t| t.entry_at(pc)) {
                    Some((start, _, id)) => (format!("slot#{}+{:#x}", id, pc - start), String::new(), "jit".into()),
                    None => (format!("jit {:#x}", pc), String::new(), "jit".into()),
                })
                .collect()
        }
    }
}

/// A slot's name as source spells it: `std::thread::JoinHandle::join` style paths with the generic
/// arguments (types printed without hashes), closures named by the fn they are in (on the owner).
fn display_name(u: &crate::jit::Unit, id: u32, depth: u32) -> String {
    let f = &u.fns[id as usize];
    match &f.key {
        crate::jit::FnKey::Inst(d, args) => {
            let mut s = u.prog.def_path(*d).replace("::::", "::");
            if !args.is_empty() {
                let a: Vec<String> = args.iter().map(|t| crate::typeck::ty_to_string(false, &u.prog, &u.tcx, u.tcx.tys.erase_regions(*t))).collect();
                s.push('<');
                s.push_str(&short(&a.join(", "), 120));
                s.push('>');
            }
            s
        }
        crate::jit::FnKey::Closure(_, _, p) if depth < 8 && (*p as usize) < u.fns.len() => format!("{{closure}} in {}", display_name(u, *p, depth + 1)),
        _ => f.name.clone(),
    }
}

/// One frame as a short JSON object.
pub fn frame_json(f: &Frame) -> String {
    if f.at.is_empty() {
        format!("{{\"fn\":{},\"in\":{}}}", json_str(&short(&f.name, 140)), json_str(&f.module))
    } else {
        format!("{{\"fn\":{},\"at\":{},\"in\":{}}}", json_str(&short(&f.name, 140)), json_str(&f.at), json_str(&f.module))
    }
}

pub fn short(s: &str, n: usize) -> String {
    if s.len() <= n {
        return s.to_string();
    }
    let mut k = n;
    while !s.is_char_boundary(k) {
        k -= 1;
    }
    format!("{}..", &s[..k])
}

/// The thread a registry handle names, as a short label.
pub fn thread_label(handle: u64, threads: &[threads::Thread]) -> String {
    if handle == 0 {
        return "?".into();
    }
    match threads.iter().find(|t| t.handle == handle) {
        Some(t) => format!("{} (T{})", if t.name.is_empty() { "-" } else { &t.name }, t.os_id),
        None => format!("thread {:#x}", handle),
    }
}

/// The thread whose stack holds the page a mutex holder tag names (Relax std's RawMutex tag:
/// `((sp >> 12) << 1 | 1) & 0x7fff_ffff`).
pub fn holder_of_tag(tag: u64, caps: &[Captured]) -> Option<usize> {
    if tag == 0 {
        return None;
    }
    let page = (tag >> 1) & 0x3fff_ffff;
    caps.iter().position(|c| {
        let (lo, hi) = if c.t.stack.1 != 0 { c.t.stack } else { (c.sp, c.sp + (8 << 20)) };
        lo != 0 && (lo >> 12..=hi >> 12).any(|p| p & 0x3fff_ffff == page)
    })
}

fn cmd_threads(out: &mut Out) {
    let mut list = threads::list();
    name_handles(&mut list);
    let waits = crate::waits::snapshot();
    out.measured("threads", "os+registry", &[]);
    for t in &list {
        let w = waits.iter().find(|w| w.thread == t.handle && t.handle != 0);
        let wait = match w {
            Some(w) => format!(",\"waits\":{}", json_str(&wait_text(w, &list))),
            None => String::new(),
        };
        out.line(&format!(
            "{{\"id\":\"T{}\",\"name\":{},\"role\":\"{}\",\"state\":\"{}\",\"cpu_ms\":{}{}}}",
            t.os_id,
            json_str(&t.name),
            role(&t.name, t.os_id, t.handle),
            t.state,
            t.cpu_ns / 1_000_000,
            wait
        ));
    }
}

pub fn wait_text(w: &crate::waits::Wait, list: &[threads::Thread]) -> String {
    let ms = crate::clock::wall_ns().saturating_sub(w.since_ns) / 1_000_000;
    let kind = crate::waits::KIND_NAMES[w.kind as usize];
    match w.kind {
        crate::waits::Kind::Futex => format!("{} {:#x} for {} ms", if w.label.is_empty() { "futex" } else { w.label }, w.object, ms),
        crate::waits::Kind::Owner => format!("owner ({} request) for {} ms; owner serves {}", w.label, ms, crate::owner::serving_note()),
        _ => format!("{} held by {} for {} ms", kind, thread_label(w.holder, list), ms),
    }
}

fn pick_threads(sel: &str) -> Box<dyn Fn(&threads::Thread) -> bool> {
    let sel = sel.to_string();
    Box::new(move |t: &threads::Thread| match sel.as_str() {
        "all" | "" => true,
        "main" => t.handle != 0 && t.handle == crate::jit::MAIN_TID.load(Relaxed) || t.os_id == std::process::id() as u64,
        "owner" => t.handle != 0 && t.handle == crate::owner::owner_tid(),
        s => s.trim_start_matches('T').parse::<u64>().map_or(false, |id| id == t.os_id) || t.name.starts_with(s),
    })
}

fn cmd_stacks(req: &Req, out: &mut Out) {
    let sel = req.get("thread").or(req.pos.first().map(String::as_str)).unwrap_or("all");
    let depth = req.num("depth", 12) as usize;
    let caps = capture_all(&*pick_threads(sel));
    let mut partial = Vec::new();
    let frames: Vec<Vec<u64>> = caps.iter().map(|c| c.frames.iter().copied().take(depth.max(1) + 1).collect()).collect();
    let syms = symbolise(&frames, &mut partial);
    out.measured(&format!("stacks of {} thread(s), captured now", caps.len()), "os capture (no owner)", &partial);
    // identical stacks folded
    let mut groups: Vec<(Vec<String>, Vec<usize>)> = Vec::new();
    for (i, s) in syms.iter().enumerate() {
        let key: Vec<String> = s.iter().take(depth).map(frame_json).collect();
        match groups.iter_mut().find(|g| g.0 == key) {
            Some(g) => g.1.push(i),
            None => groups.push((key, vec![i])),
        }
    }
    for (key, members) in &groups {
        let names: Vec<String> = members.iter().map(|&i| json_str(&format!("{} (T{})", caps[i].t.name, caps[i].t.os_id))).collect();
        let c = &caps[members[0]];
        let mut err = c.err.map(|e| format!(",\"err\":{}", json_str(e))).unwrap_or_default();
        if c.t.handle != 0 && instrument::stopped(&c.t) {
            err.push_str(&script_stack_field("script", c.t.handle));
        }
        out.line(&format!("{{\"threads\":[{}],\"state\":\"{}\",\"frames\":[{}]{}}}", names.join(","), c.t.state, key.join(","), err));
    }
}

fn cmd_waits(out: &mut Out) {
    let mut list = threads::list();
    name_handles(&mut list);
    let waits = crate::waits::snapshot();
    out.measured("wait registry", "registry (no owner)", &[]);
    for w in &waits {
        if w.kind == crate::waits::Kind::None {
            continue;
        }
        out.line(&format!("{{\"thread\":{},\"waits\":{}}}", json_str(&thread_label(w.thread, &list)), json_str(&wait_text(w, &list))));
    }
}

fn cmd_owner(out: &mut Out) {
    out.measured("owner thread", "owner counters (no owner)", &[]);
    out.line(&format!("{{\"serving\":{},\"queued\":{}}}", json_str(&crate::owner::serving_note()), crate::owner::queued_note()));
}

// ------------------------------------------------------------------ Splash VMs

/// The Splash VM registry's summaries (makepad-script, compiled into the relax binary: its
/// main.rs sets the provider; relax-compiler cannot depend on the script crate).
static VM_PROVIDER: std::sync::Mutex<Option<fn() -> Vec<String>>> = std::sync::Mutex::new(None);

pub fn set_vm_provider(f: fn() -> Vec<String>) {
    *VM_PROVIDER.lock().unwrap_or_else(|e| e.into_inner()) = Some(f);
}

/// One JSON object per live Splash VM (empty when the script crate is not in this binary).
pub fn vm_summaries() -> Vec<String> {
    let f = *VM_PROVIDER.lock().unwrap_or_else(|e| e.into_inner());
    f.map(|f| f()).unwrap_or_default()
}

/// The Splash script stack of a thread (makepad-script, set by main.rs): only valid for a thread
/// that is stopped (parked at a panic or breakpoint, or paused).
static SCRIPT_STACK_PROVIDER: std::sync::Mutex<Option<fn(u64, usize) -> Option<Vec<String>>>> = std::sync::Mutex::new(None);

pub fn set_script_stack_provider(f: fn(u64, usize) -> Option<Vec<String>>) {
    *SCRIPT_STACK_PROVIDER.lock().unwrap_or_else(|e| e.into_inner()) = Some(f);
}

/// The script frames (innermost first, at most 16) of the VM that the thread with pthread handle
/// `thread` is evaluating; None when it is in no VM. The caller guarantees the thread is stopped.
pub fn script_stack(thread: u64) -> Option<Vec<String>> {
    let f = (*SCRIPT_STACK_PROVIDER.lock().unwrap_or_else(|e| e.into_inner()))?;
    f(thread, 16)
}

/// `,"<key>":[...]` for a stopped thread inside a VM, else an empty string.
pub fn script_stack_field(key: &str, thread: u64) -> String {
    match script_stack(thread) {
        Some(v) if !v.is_empty() => format!(",\"{}\":[{}]", key, v.iter().map(|s| json_str(s)).collect::<Vec<_>>().join(",")),
        _ => String::new(),
    }
}

/// A Splash script error (makepad-script's error hook): an agent's `scripterr` event.
pub fn script_error_event(line: &str) {
    events::emit("scripterr", line, &format!("\"error\":{},\"more\":[\"vms\"]", json_str(&short(line, 400))));
}

fn cmd_vms(out: &mut Out) {
    let v = vm_summaries();
    out.measured(&format!("{} live Splash VM(s): heap counts and GC as of their last evaluation / collection", v.len()), "script VM registry (atomics)", &[]);
    for l in v {
        out.line(&l);
    }
}

// ------------------------------------------------------------------ program wait entries

/// Relax std's sync/raw.rs and sys/posix.rs: a program thread blocks on a futex (kind: 1 mutex, 2
/// condvar, 3 read lock, 4 write lock, 5 park, 6 once; holder: a mutex holder's tag) or joins a
/// thread (kind 7; holder: its pthread handle).
pub extern "C" fn relax_wait_enter(kind: u32, addr: usize, holder: usize) {
    if kind == 7 {
        // a join: the holder is the joined thread's pthread handle
        crate::waits::enter(crate::waits::Kind::Join, 0, holder as u64, "join");
        return;
    }
    const LABELS: [&str; 7] = ["futex", "mutex", "condvar", "rwlock read", "rwlock write", "park", "once"];
    crate::waits::enter(crate::waits::Kind::Futex, addr as u64, holder as u64, LABELS.get(kind as usize).copied().unwrap_or("futex"));
}

pub extern "C" fn relax_wait_leave() {
    crate::waits::leave();
}

