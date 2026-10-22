//! Field watches (`writes`): "who set this field to 1.0?" in one query. `writes Type::field`
//! finds the compiled fns whose bodies assign the field (`x.field = v`, `x.field op= v`, through
//! any autoderef), lowers them again with a hit after each such write (lower.rs watch_write) and
//! installs them as watch W<n>; every write then records its site (fn, file:line), the value
//! written and the field's address. Writers inlined into other code are rebuilt to call them.
//! Not seen: writes through a `&mut` to the field handed elsewhere (`f(&mut x.field)`), struct
//! literals and whole-struct assignments, raw pointer writes (the answer says so).

use super::{json_str, now_ms, short, Out, Req};
use relax_session::sync::Mutex;
use std::collections::VecDeque;
use std::sync::atomic::{AtomicU64, Ordering::{Relaxed, SeqCst}};
use std::sync::Arc;

include!("../rt_abi.rs");

struct Site {
    slot: u32,
    pos: u64,
    n: u64,
    last: String,
}

pub(super) struct Watch {
    id: u32,
    what: String,
    on: std::sync::atomic::AtomicBool,
    hits: AtomicU64,
    sites: Mutex<Vec<Site>>,
    /// (ms, site position, value, field address), oldest first
    recent: Mutex<VecDeque<(u64, u64, String, u64)>>,
}

const RECENT: usize = 512;

static WATCHES: Mutex<Vec<Arc<Watch>>> = Mutex::new(Vec::new());
static NEXT: AtomicU64 = AtomicU64::new(1);

fn watch_at(i: u64) -> Option<Arc<Watch>> {
    WATCHES.lock().unwrap_or_else(|e| e.into_inner()).get(i as usize).cloned()
}

fn value_text(addr: u64, ks: u64) -> String {
    let (kind, size) = (ks >> 32, (ks & 0xffff_ffff) as usize);
    if addr == 0 {
        return "?".into();
    }
    unsafe {
        let p = addr as *const u8;
        match (kind, size) {
            (1, _) => format!("{}", std::ptr::read_unaligned(p as *const f32)),
            (2, _) => format!("{}", std::ptr::read_unaligned(p as *const f64)),
            (3, _) => format!("{}", *p != 0),
            (4, 1) => format!("{}", *(p as *const i8)),
            (4, 2) => format!("{}", std::ptr::read_unaligned(p as *const i16)),
            (4, 4) => format!("{}", std::ptr::read_unaligned(p as *const i32)),
            (4, _) => format!("{}", std::ptr::read_unaligned(p as *const i64)),
            (5, 1) => format!("{}", *p),
            (5, 2) => format!("{}", std::ptr::read_unaligned(p as *const u16)),
            (5, 4) => format!("{}", std::ptr::read_unaligned(p as *const u32)),
            (5, _) => format!("{}", std::ptr::read_unaligned(p as *const u64)),
            (_, n) => {
                let b = std::slice::from_raw_parts(p, n.min(32));
                let mut s = format!("{} bytes:", n);
                for x in b {
                    s.push_str(&format!(" {:02x}", x));
                }
                s
            }
        }
    }
}

rt_fn! {
/// A watched field was written at `pos`: its new value is at `addr` (`ks`: kind << 32 | size).
fn rt_watch_hit(idx: u64, addr: u64, ks: u64, pos: u64) {
    let _k = crate::zone_alloc::kept();
    let Some(w) = watch_at(idx) else { return };
    if !w.on.load(Relaxed) {
        return;
    }
    w.hits.fetch_add(1, Relaxed);
    let v = value_text(addr, ks);
    {
        let mut s = w.sites.lock().unwrap_or_else(|e| e.into_inner());
        match s.iter_mut().find(|x| x.pos == pos) {
            Some(x) => {
                x.n += 1;
                if x.last != v {
                    x.last = v.clone();
                }
            }
            None => s.push(Site { slot: u32::MAX, pos, n: 1, last: v.clone() }),
        }
    }
    let mut r = w.recent.lock().unwrap_or_else(|e| e.into_inner());
    if r.len() >= RECENT {
        r.pop_front();
    }
    r.push_back((now_ms(), pos, v, addr));
}
}

/// The relowering of `slot` for watch `idx` instrumented the writes at `watched` (patches::rebuild).
pub(super) fn note_sites(idx: u64, slot: u32, watched: &[(u32, u64)]) {
    let _k = crate::zone_alloc::kept();
    let Some(w) = watch_at(idx) else { return };
    let mut s = w.sites.lock().unwrap_or_else(|e| e.into_inner());
    for &(sl, pos) in watched.iter().filter(|x| x.0 == slot) {
        match s.iter_mut().find(|x| x.pos == pos) {
            Some(x) => x.slot = sl,
            None => s.push(Site { slot: sl, pos, n: 0, last: String::new() }),
        }
    }
}

pub(crate) fn scan_kept(a: &mut crate::jit::zone_scan::Acc) {
    let Ok(ws) = WATCHES.try_lock() else { return };
    a.field("inspect.watches");
    a.vec(&ws);
    for w in ws.iter() {
        a.arc(w);
        a.string(&w.what);
        if let Ok(s) = w.sites.try_lock() {
            a.vec(&s);
            for x in s.iter() {
                a.string(&x.last);
            }
        }
        if let Ok(r) = w.recent.try_lock() {
            let (x, y) = r.as_slices();
            if r.capacity() > 0 {
                a.ptr(if x.is_empty() { y.as_ptr() } else { x.as_ptr() });
            }
            for e in r.iter() {
                a.string(&e.2);
            }
        }
    }
}

/// Is `t` (bytes after `.field`) an assignment: `=` (not `==`) or a compound `op=`?
fn assigns(t: &[u8]) -> bool {
    let mut k = 0;
    while k < t.len() && (t[k] == b' ' || t[k] == b'\t' || t[k] == b'\n' || t[k] == b'\r') {
        k += 1;
    }
    match t.get(k) {
        Some(b'=') => t.get(k + 1) != Some(&b'='),
        Some(b'+' | b'-' | b'*' | b'/' | b'%' | b'|' | b'&' | b'^') => t.get(k + 1) == Some(&b'='),
        Some(b'<') => t.get(k + 1) == Some(&b'<') && t.get(k + 2) == Some(&b'='),
        Some(b'>') => t.get(k + 1) == Some(&b'>') && t.get(k + 2) == Some(&b'='),
        _ => false,
    }
}

/// The structs a `Type::field` query names: (struct, field index, `krate::path::Type::field`).
fn fields_named(u: &crate::jit::Unit, query: &str) -> Result<Vec<(crate::program::DefId, u32, String)>, String> {
    let Some((ty, field)) = query.rsplit_once("::") else { return Err(format!("`{}`: name a field as `Type::field` (or `krate::path::Type::field`)", query)) };
    let mut out = Vec::new();
    let mut near: Vec<String> = Vec::new();
    for (def, adt) in u.tcx.adts.iter() {
        if adt.is_enum || adt.variants.is_empty() {
            continue;
        }
        let path = u.prog.def_path(*def);
        if !(path == ty || path.ends_with(&format!("::{}", ty.trim_start_matches("crate::")))) {
            continue;
        }
        match adt.variants[0].fields.iter().position(|f| u.prog.syms.str(f.name) == field) {
            Some(fi) => out.push((*def, fi as u32, format!("{}::{}", path, field))),
            None => near.push(format!("{} has {}", path, adt.variants[0].fields.iter().map(|f| u.prog.syms.str(f.name).to_string()).collect::<Vec<_>>().join(", "))),
        }
        if out.len() >= 4 {
            break;
        }
    }
    if out.is_empty() {
        return Err(if near.is_empty() { format!("no struct `{}` is loaded", ty) } else { format!("no field `{}`: {}", field, near.join("; ")) });
    }
    Ok(out)
}

fn add(query: &str) -> Result<(Arc<Watch>, Vec<String>), String> {
    let up = crate::jit::current_unit();
    if up.is_null() {
        return Err("no running unit".into());
    }
    let q = query.to_string();
    let r = crate::owner::call_within(crate::owner::Class::App, 60_000, move || -> Result<(Arc<Watch>, Vec<String>), String> {
        let u = unsafe { &*up };
        let fields = fields_named(u, &q)?;
        let fname = q.rsplit("::").next().unwrap_or("").to_string();
        let needle = format!(".{}", fname);
        // candidate writers: the lines of the loaded sources that assign `.field`, and the
        // compiled fns spanning them (the same lookup as `probe add file:line`)
        let mut cands: Vec<u32> = Vec::new();
        let nb = needle.as_bytes();
        let mut seen_paths: Vec<&str> = Vec::new();
        for fi in (0..u.prog.files.len()).rev() {
            let path = u.prog.file_paths[fi].as_str();
            if seen_paths.contains(&path) {
                continue;
            }
            seen_paths.push(path);
            let file = &u.prog.files[fi];
            let text = file.bytes(0, file.src_len);
            let mut k = 0;
            while k + nb.len() <= text.len() {
                if &text[k..k + nb.len()] == nb && text.get(k + nb.len()).map_or(true, |c| !(c.is_ascii_alphanumeric() || *c == b'_')) && assigns(&text[k + nb.len()..]) {
                    let line = 1 + text[..k].iter().filter(|&&c| c == b'\n').count();
                    for (slot, _, _) in super::instrument::find_all(u, &format!("{}:{}", path, line), 8) {
                        if !cands.contains(&slot) {
                            cands.push(slot);
                        }
                    }
                }
                k += 1;
            }
            if cands.len() >= 64 {
                break;
            }
        }
        let _kept = crate::zone_alloc::kept();
        let id = NEXT.fetch_add(1, SeqCst) as u32;
        let what = fields.iter().map(|f| f.2.clone()).collect::<Vec<_>>().join(", ");
        let w = Arc::new(Watch { id, what, on: std::sync::atomic::AtomicBool::new(true), hits: AtomicU64::new(0), sites: Mutex::new(Vec::new()), recent: Mutex::new(VecDeque::new()) });
        let idx = {
            let mut ws = WATCHES.lock().unwrap_or_else(|e| e.into_inner());
            ws.push(w.clone());
            ws.len() as u64 - 1
        };
        let owner = super::patches::Owner::Watch(id);
        let mut notes = vec![format!("{} compiled fn(s) assign `.{}` in their text: {}", cands.len(), fname, cands.iter().take(8).map(|c| short(&u.fns[*c as usize].name, 80)).collect::<Vec<_>>().join(", "))];
        let mut ok: Vec<(u32, Option<u32>)> = Vec::new();
        for slot in cands {
            for (adt, fi, _) in &fields {
                let field = Arc::new(crate::lower::WatchField { slot, adt: *adt, field: *fi, idx, hit: rt_watch_hit as *const () as u64 });
                let r = unsafe { super::patches::add(up, slot, owner, super::patches::Edit::Watch { field }) };
                let u = unsafe { &*up };
                match r {
                    Ok(true) => {
                        if !ok.iter().any(|x| x.0 == slot) {
                            ok.push((slot, None));
                        }
                    }
                    Ok(false) => notes.push(format!("{}: relowered, no write of {} found (another struct's field of that name?)", short(&u.fns[slot as usize].name, 120), q)),
                    Err(e) => notes.push(format!("{}: not watched: {}", short(&u.fns[slot as usize].name, 120), e)),
                }
            }
        }
        if !ok.is_empty() {
            notes.extend(unsafe { super::codever::cover_inliners(up, owner, &ok, false) });
        }
        Ok((w, notes))
    });
    r.unwrap_or_else(|| Err(format!("the owner did not take the request in 60 s ({})", crate::owner::serving_note())))
}

fn site_text(u: &crate::jit::Unit, pos: u64) -> String {
    match super::codever::pos_line(u, pos) {
        Some((f, l)) => format!("{}:{}", u.prog.file_paths.get(f as usize).map(|p| p.to_string()).unwrap_or_default(), l),
        None => "?".into(),
    }
}

/// `writes <Type::field>` | `writes` (list) | `writes W<n> [n=20]` | `writes rm <W<n>|all>`
pub fn cmd(req: &Req, out: &mut Out) {
    let first = req.pos.first().map(String::as_str).unwrap_or("");
    let up = crate::jit::current_unit();
    match first {
        "" | "list" => {
            out.measured("field watches", "watch tables", &[]);
            let ws = WATCHES.lock().unwrap_or_else(|e| e.into_inner()).clone();
            let mut any = false;
            for w in ws.iter().filter(|w| w.on.load(Relaxed)) {
                any = true;
                out.line(&format!("{{\"watch\":\"W{}\",\"field\":{},\"writes\":{},\"sites\":{}}}", w.id, json_str(&w.what), w.hits.load(Relaxed), w.sites.lock().unwrap_or_else(|e| e.into_inner()).len()));
            }
            if !any {
                out.line("{\"note\":\"no field watches; add one: writes Type::field\"}");
            }
        }
        "rm" => {
            let which = req.pos.get(1).map(String::as_str).unwrap_or("all");
            let ids: Vec<u32> = WATCHES.lock().unwrap_or_else(|e| e.into_inner()).iter().filter(|w| w.on.load(Relaxed) && (which == "all" || which.trim_start_matches('W').parse::<u32>().ok() == Some(w.id))).map(|w| w.id).collect();
            for w in WATCHES.lock().unwrap_or_else(|e| e.into_inner()).iter().filter(|w| ids.contains(&w.id)) {
                w.on.store(false, SeqCst);
            }
            let n = ids.len();
            let _ = crate::owner::call_within(crate::owner::Class::App, 20_000, move || {
                for id in ids {
                    unsafe { super::patches::remove_owner(up, super::patches::Owner::Watch(id)) };
                }
            });
            out.line(&format!("{{\"removed\":{}}}", n));
        }
        w if w.starts_with('W') && w[1..].parse::<u32>().is_ok() => {
            let id = w[1..].parse::<u32>().unwrap_or(0);
            let Some(w) = WATCHES.lock().unwrap_or_else(|e| e.into_inner()).iter().find(|x| x.id == id).cloned() else {
                out.err(&format!("no watch W{} (list: writes)", id));
                return;
            };
            let n = req.get("n").and_then(|v| v.parse::<usize>().ok()).unwrap_or(12).clamp(1, RECENT);
            read(up, &w, n, out);
        }
        q => match add(q) {
            Ok((w, notes)) => {
                out.measured(&format!("watch W{} on {}", w.id, w.what), "owner: relowered writers", &[]);
                read(up, &w, 0, out);
                out.line(&format!("{{\"notes\":[{}],\"not_seen\":\"writes through a &mut handed elsewhere, struct literals, whole-struct assignments, raw pointers\"}}", notes.iter().map(|n| json_str(n)).collect::<Vec<_>>().join(",")));
            }
            Err(e) => out.err(&e),
        },
    }
}

fn read(up: *mut crate::jit::Unit, w: &Watch, n: usize, out: &mut Out) {
    let sites: Vec<(u32, u64, u64, String)> = w.sites.lock().unwrap_or_else(|e| e.into_inner()).iter().map(|s| (s.slot, s.pos, s.n, s.last.clone())).collect();
    let recent: Vec<(u64, u64, String, u64)> = w.recent.lock().unwrap_or_else(|e| e.into_inner()).iter().rev().take(n).rev().cloned().collect();
    let kept = w.recent.lock().unwrap_or_else(|e| e.into_inner()).len();
    let now = now_ms();
    let w_id = w.id;
    let w_what = w.what.clone();
    let hits = w.hits.load(Relaxed);
    // names and lines resolve on the owner (the unit's tables)
    let rows = crate::owner::call_within(crate::owner::Class::Job, 10_000, move || {
        let u = unsafe { &*up };
        let mut rows = vec![format!("{{\"watch\":\"W{}\",\"field\":{},\"writes\":{},\"writer_sites\":{}}}", w_id, json_str(&w_what), hits, sites.len())];
        let mut ss = sites.clone();
        ss.sort_by(|a, b| b.2.cmp(&a.2));
        for (slot, pos, n, last) in ss {
            let f = if slot != u32::MAX && (slot as usize) < u.fns.len() { u.fns[slot as usize].name.to_string() } else { String::new() };
            rows.push(format!("{{\"site\":{},\"fn\":{},\"writes\":{},\"last_value\":{}}}", json_str(&site_text(u, pos)), json_str(&short(&f, 140)), n, json_str(&last)));
        }
        for (t, pos, v, addr) in recent {
            rows.push(format!("{{\"write\":{},\"at\":{},\"addr\":\"{:#x}\",\"ago_ms\":{}}}", json_str(&v), json_str(&site_text(u, pos)), addr, now.saturating_sub(t)));
        }
        if kept > n && n > 0 {
            rows.push(format!("{{\"writes_not_shown\":{}}}", kept - n));
        }
        rows
    });
    match rows {
        Some(r) => {
            for l in r {
                out.line(&l);
            }
        }
        None => out.err("the owner did not answer in 10 s"),
    }
}
