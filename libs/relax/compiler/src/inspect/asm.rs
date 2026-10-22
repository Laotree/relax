//! `asm <fn> [vs=rustc]` and `asm top vs=rustc`: the JIT's machine code of a fn in the running
//! process next to rustc's code of the same fn in a native build, aligned by source line, with
//! what each instruction costs here (CPU samples, PGO block counts) and a short diff summary
//! first: the excess instructions, where they are (hot loops, lines), and what they are (spill
//! traffic, kept bounds checks, calls rustc inlined, loops rustc vectorised). AI agents that
//! optimise the JIT read this; the answer follows local/agent_state/relax-campaign/profproto.md §5
//! (answer first, markdown tables, drill-down handles at the end).
//!
//! Both sides are decoded by the same decoder (relax_backend::asm::dis), so they are spelled and
//! classified alike. Ours: the slot's code bodies from the code tables (installed first), its pc
//! map (offset -> source position, inline stack) and its PGO counts. rustc's: the fn's symbol in
//! a native build (`native=<binary>`, built with line tables only: the same machine code as the
//! plain release build), its DWARF line table and inline tree (inspect::natbin).

use super::natbin::NativeBin;
use super::{short, Out, Req};
use relax_backend::asm::dis::{self, Class, Insn};
use relax_backend::asm::Arch;
use std::collections::HashMap;

// ------------------------------------------------------------------ one side

/// A source line code is attributed to.
#[derive(Clone)]
struct Line {
    /// the alignment key: normalised path + line (`core/slice/mod.rs:1234`, `src/view.rs:242`)
    key: String,
    /// for display: file name + line (`view.rs:242`)
    show: String,
}

/// One side's code of the fn, decoded, with per-instruction source and costs.
struct Side {
    /// "ours O3 fresh" / "rustc"
    label: String,
    name: String,
    addr: u64,
    insns: Vec<Insn>,
    /// per instruction: index into `lines` (u32::MAX: no line)
    at: Vec<u32>,
    /// per instruction: the innermost inlined fn it comes from ("" = the fn's own code) and depth
    inl: Vec<(String, u8)>,
    /// per instruction: the callee a direct call goes to (named)
    callee: Vec<Option<String>>,
    /// per instruction: samples (weighted: events for hardware events) with this pc innermost
    samples: Vec<u64>,
    /// per call instruction: samples whose return address is right after it (time in the callee)
    below: Vec<u64>,
    /// per instruction: PGO executions of its line (ours, counted builds)
    count: Vec<Option<u64>>,
    lines: Vec<Line>,
    /// per instruction: the check it guards when it is a conditional branch to a panic
    check: Vec<Option<&'static str>>,
    /// per call instruction (ours): the O3 remark on why it stayed a call
    why: Vec<Option<String>>,
}

impl Side {
    fn new(label: String, name: String, addr: u64, insns: Vec<Insn>) -> Side {
        let n = insns.len();
        Side { label, name, addr, insns, at: vec![u32::MAX; n], inl: vec![(String::new(), 0); n], callee: vec![None; n], samples: vec![0; n], below: vec![0; n], count: vec![None; n], lines: Vec::new(), check: vec![None; n], why: vec![None; n] }
    }

    fn line_index(&mut self, idx: &mut HashMap<String, u32>, key: String, show: String) -> u32 {
        if let Some(&k) = idx.get(&key) {
            return k;
        }
        let k = self.lines.len() as u32;
        idx.insert(key.clone(), k);
        self.lines.push(Line { key, show });
        k
    }

    fn total_samples(&self) -> u64 {
        self.samples.iter().sum()
    }

    /// The instruction at absolute address `a`.
    fn at_addr(&self, a: u64) -> Option<usize> {
        let off = a.checked_sub(self.addr)? as u32;
        self.insns.binary_search_by_key(&off, |i| i.off).ok()
    }

    /// Marks conditional branches that lead to a panic call within a few instructions (on the
    /// taken or the fall-through path): bounds, overflow and unwrap checks.
    fn find_checks(&mut self) {
        let leads_to = |s: &Side, mut k: usize| -> Option<&'static str> {
            for _ in 0..12 {
                let i = s.insns.get(k)?;
                if matches!(i.class, Class::Call) {
                    if let Some(c) = s.callee[k].as_deref().and_then(check_kind) {
                        return Some(c);
                    }
                }
                if matches!(i.class, Class::Ret | Class::IndirectBranch | Class::Trap) {
                    return None;
                }
                if i.class == Class::Branch {
                    k = s.at_addr(i.target?)?;
                    continue;
                }
                k += 1;
            }
            None
        };
        for k in 0..self.insns.len() {
            if self.insns[k].class != Class::CondBranch {
                continue;
            }
            let taken = self.insns[k].target.and_then(|t| self.at_addr(t)).and_then(|t| leads_to(self, t));
            self.check[k] = taken.or_else(|| leads_to(self, k + 1));
        }
    }

    /// Loops: (first, last instruction) of every backward branch's range, innermost (shortest) first.
    fn loops(&self) -> Vec<(usize, usize)> {
        let mut v = Vec::new();
        for (k, i) in self.insns.iter().enumerate() {
            if !matches!(i.class, Class::CondBranch | Class::Branch) {
                continue;
            }
            if let Some(h) = i.target.filter(|t| *t <= self.addr + i.off as u64).and_then(|t| self.at_addr(t)) {
                v.push((h, k));
            }
        }
        v.sort_by_key(|&(a, b)| (b - a, a));
        v.dedup();
        v
    }

    /// Weight of instruction k for ranking: samples when there are any, else PGO executions,
    /// else 1 (static).
    fn weight(&self, k: usize, by_samples: bool, by_count: bool) -> f64 {
        if by_samples {
            self.samples[k] as f64
        } else if by_count {
            self.count[k].unwrap_or(0) as f64
        } else {
            1.0
        }
    }
}

/// Which check a panic entry point reports.
fn check_kind(callee: &str) -> Option<&'static str> {
    let n = callee;
    if n.contains("panic_bounds_check") || n.contains("index_len_fail") || n.contains("slice_index_fail") || n.contains("slice_index_order_fail") || n.contains("str_index_overflow_fail") {
        Some("bounds")
    } else if n.contains("overflow") && n.contains("panic") {
        Some("overflow")
    } else if n.contains("unwrap_failed") || n.contains("expect_failed") || n.contains("option::unwrap") {
        Some("unwrap")
    } else if n.contains("panicking::panic") || n.contains("panic_fmt") || n.contains("begin_panic") || n.contains("panic_nounwind") || n.contains("assert_failed") {
        Some("panic")
    } else {
        None
    }
}

/// The alignment key of a source path: std sources by crate-relative path (rustc's
/// `/rustc/<hash>/library/core/src/x.rs` and Relax's `.../std/core/x.rs` both `core/x.rs`),
/// everything else by its last three components.
fn path_key(path: &str) -> String {
    let p = path.replace('\\', "/");
    if let Some(i) = p.find("/library/") {
        let rest = &p[i + 9..];
        return match rest.split_once('/') {
            Some((krate, tail)) => format!("{}/{}", krate, tail.strip_prefix("src/").unwrap_or(tail)),
            None => rest.to_string(),
        };
    }
    if let Some(i) = p.find("/compiler/std/") {
        return p[i + 14..].to_string();
    }
    let parts: Vec<&str> = p.rsplit('/').take(3).collect();
    parts.into_iter().rev().collect::<Vec<_>>().join("/")
}

fn file_name(path: &str) -> &str {
    path.rsplit(['/', '\\']).next().unwrap_or(path)
}

/// A fn path without generic arguments, with `<T as Trait>::f` as `T::f` and the legacy hash
/// gone: the form both sides' names are compared in.
pub(crate) fn plain_name(n: &str) -> String {
    let mut out = String::with_capacity(n.len());
    let mut depth = 0i32;
    let b = n.as_bytes();
    let mut k = 0;
    while k < b.len() {
        let c = b[k] as char;
        if c == '<' {
            // `<T as Trait>::` at depth 0: keep T
            if depth == 0 && (k == 0 || n[..k].ends_with("::") || n[..k].ends_with(' ')) {
                if let Some(end) = matching_angle(n, k) {
                    let inner = &n[k + 1..end];
                    let ty = inner.split(" as ").next().unwrap_or(inner);
                    out.push_str(&plain_name(ty));
                    k = end + 1;
                    continue;
                }
            }
            depth += 1;
        } else if c == '>' {
            depth -= 1;
        } else if depth == 0 {
            out.push(c);
        }
        k += 1;
    }
    let out = out.replace("::::", "::");
    match out.rsplit_once("::h") {
        Some((a, h)) if h.len() == 16 && h.bytes().all(|c| c.is_ascii_hexdigit()) => a.to_string(),
        _ => out,
    }
}

fn matching_angle(s: &str, open: usize) -> Option<usize> {
    let mut d = 0;
    for (k, c) in s[open..].char_indices() {
        match c {
            '<' => d += 1,
            '>' => {
                d -= 1;
                if d == 0 {
                    return Some(open + k);
                }
            }
            _ => {}
        }
    }
    None
}

/// The last two path segments of a plain name (`Vec::push`): how callees are matched across
/// sides (crate paths differ between the JIT's std and rustc's).
fn callee_key(n: &str) -> String {
    let p = plain_name(n);
    let segs: Vec<&str> = p.rsplit("::").take(2).collect();
    segs.into_iter().rev().collect::<Vec<_>>().join("::")
}

// ------------------------------------------------------------------ our side (on the owner)

/// The code bodies of the fn the query names: one Side per body, built on the owner.
fn our_sides(q: &str, max: usize) -> Result<(Vec<(u32, Side)>, Vec<String>), String> {
    let up = crate::jit::current_unit();
    if up.is_null() {
        return Err("no running unit (asm reads JIT code of a `makepad run` process)".into());
    }
    let q = q.to_string();
    let r = crate::owner::call_within(crate::owner::Class::Job, 10_000, move || -> Result<(Vec<(u32, Side)>, Vec<String>), String> {
        let u = unsafe { &*up };
        let found: Vec<u32> = match q.strip_prefix('@').and_then(|s| s.parse::<u32>().ok()) {
            Some(id) if (id as usize) < u.fns.len() => vec![id],
            Some(id) => return Err(format!("no slot @{} (have @0..@{})", id, u.fns.len().saturating_sub(1))),
            None => super::instrument::find_all(u, &q, max).into_iter().map(|x| x.0).collect(),
        };
        if found.is_empty() {
            return Err(format!("no fn matches `{}`; try: top by=time (hot fns), or a longer path like `krate::Type::method`", q));
        }
        let mut sides = Vec::new();
        let mut notes = Vec::new();
        let mut res = super::codever::Resolver::new();
        for id in found {
            let f = &u.fns[id as usize];
            let bodies = super::codever::bodies(u, id);
            if bodies.is_empty() {
                let into = &f.history().inlined_into;
                if !into.is_empty() {
                    let names: Vec<String> = into.iter().take(4).map(|c| format!("`{}` (@{})", short(&u.fns[*c as usize].name, 80), c)).collect();
                    notes.push(format!("@{} {} has no code of its own: it runs inlined into {}", id, short(&f.name, 80), names.join(", ")));
                }
                continue;
            }
            let pgo: Option<HashMap<(u32, u32), u64>> = u.pgo_counts(id).map(|v| {
                let mut m = HashMap::new();
                for (p, c) in v {
                    if let Some(fl) = super::codever::pos_line(u, p) {
                        let e = m.entry(fl).or_insert(0u64);
                        *e = (*e).max(c);
                    }
                }
                m
            });
            let rem = super::remarks::inline_of(id);
            for b in bodies {
                let kind = super::codever::kind_at(u, b.start);
                let label = format!("ours {} {}{}", kind.tier_name(), kind.origin_name(), if b.state == "installed" { String::new() } else { format!(" ({})", b.state) });
                let code = unsafe { std::slice::from_raw_parts(b.start as *const u8, b.len as usize) };
                let insns = dis::decode(Arch::host(), code, b.start);
                let mut s = Side::new(label, super::display_name(u, id, 0), b.start, insns);
                let entries: Vec<(u32, u64)> = b.map.entries().into_iter().filter(|e| e.0 < b.len).collect();
                let mut idx = HashMap::new();
                let mut pos_cache: HashMap<u64, (u32, (String, u8), Option<u64>)> = HashMap::new();
                let mut e = 0;
                for k in 0..s.insns.len() {
                    let off = s.insns[k].off;
                    while e + 1 < entries.len() && entries[e + 1].0 <= off {
                        e += 1;
                    }
                    let Some(&(eo, p)) = entries.get(e) else { continue };
                    if eo > off {
                        continue;
                    }
                    if !pos_cache.contains_key(&p) {
                        let (li, cnt) = match super::codever::pos_line(u, p) {
                            Some((file, line)) => {
                                let path = u.prog.file_paths.get(file as usize).cloned().unwrap_or_default();
                                let li = s.line_index(&mut idx, format!("{}:{}", path_key(&path), line), format!("{}:{}", file_name(&path), line));
                                (li, pgo.as_ref().and_then(|m| m.get(&(file, line)).copied()))
                            }
                            None => (u32::MAX, None),
                        };
                        let inl = res.inline_stack(u, id, b.map, p).map_or((String::new(), 0), |i| (i.name, (i.stack.len().saturating_sub(1)).min(255) as u8));
                        pos_cache.insert(p, (li, inl, cnt));
                    }
                    let (li, inl, cnt) = pos_cache[&p].clone();
                    if matches!(s.insns[k].class, Class::Call | Class::IndirectCall) {
                        s.why[k] = rem.iter().find(|r| r.pos == p).map(|r| r.describe());
                    }
                    s.at[k] = li;
                    s.inl[k] = inl;
                    s.count[k] = cnt;
                }
                // call targets: JIT slots (by their thunk or code), host fns (symbol tables)
                let code_tab = u.code.read().unwrap_or_else(|e| e.into_inner());
                for k in 0..s.insns.len() {
                    if s.insns[k].class != Class::Call {
                        continue;
                    }
                    let Some(t) = s.insns[k].target else { continue };
                    let name = match u.slots.find(0, t) {
                        Some((c, 0)) if (c as usize) < u.fns.len() => Some(super::display_name(u, c, 0)),
                        _ => match code_tab.entry_at(t) {
                            Some((_, _, c)) => Some(super::display_name(u, c, 0)),
                            None => super::symbols::host_symbol(t).map(|x| x.0),
                        },
                    };
                    s.callee[k] = name;
                }
                drop(code_tab);
                s.find_checks();
                sides.push((id, s));
            }
        }
        Ok((sides, notes))
    });
    r.unwrap_or_else(|| Err(format!("the owner did not answer in 10 s ({})", crate::owner::serving_note())))
}

// ------------------------------------------------------------------ rustc's side

static NATIVE: relax_session::sync::Mutex<Option<(String, std::time::SystemTime, NativeBin)>> = relax_session::sync::Mutex::new(None);
/// the native binary of the last `asm ... native=<path>` (kept for later questions)
static NATIVE_PATH: relax_session::sync::Mutex<String> = relax_session::sync::Mutex::new(String::new());

fn native_path(req: &Req) -> Result<String, String> {
    if let Some(p) = req.get("native") {
        *NATIVE_PATH.lock().unwrap() = p.to_string();
        return Ok(p.to_string());
    }
    let p = NATIVE_PATH.lock().unwrap().clone();
    if !p.is_empty() {
        return Ok(p);
    }
    if let Ok(p) = std::env::var("MAKEPAD_INSPECT_NATIVE") {
        if !p.is_empty() {
            return Ok(p);
        }
    }
    auto_native(req.get("build") != Some("0"))
}

/// The pid and log of a native build this process started.
static BUILDING: relax_session::sync::Mutex<Option<(std::process::Child, String)>> = relax_session::sync::Mutex::new(None);

/// The running package's own rustc release build (the workspace's release profile, line tables
/// added: the same machine code), in `<workspace>/target/relax-native`; started in the background
/// when there is none yet (`build=0`: never).
fn auto_native(build: bool) -> Result<String, String> {
    let how = "pass native=<binary> (kept for later asks) or set MAKEPAD_INSPECT_NATIVE";
    let Some((krate, dir)) = crate::run::root_package() else {
        return Err(format!("no native build to compare with (the program's package is unknown); {}", how));
    };
    let mut ws = std::path::PathBuf::from(&dir);
    let mut cur = ws.clone();
    loop {
        if std::fs::read_to_string(cur.join("Cargo.toml")).map_or(false, |t| t.contains("[workspace]")) {
            ws = cur.clone();
            break;
        }
        if !cur.pop() {
            break;
        }
    }
    let target = ws.join("target").join("relax-native");
    let names = [krate.replace('_', "-"), krate.clone()];
    let mut g = BUILDING.lock().unwrap();
    if let Some((child, log)) = g.as_mut() {
        match child.try_wait() {
            Ok(None) => return Err(format!("the native baseline build is still running (pid {}, log {}); ask again when it is done", child.id(), log)),
            Ok(Some(st)) if !st.success() => {
                let log = log.clone();
                *g = None;
                let tail = std::fs::read_to_string(&log).map(|t| t.lines().rev().take(6).collect::<Vec<_>>().into_iter().rev().collect::<Vec<_>>().join(" / ")).unwrap_or_default();
                return Err(format!("the native baseline build failed (log {}): {}; {}", log, short(&tail, 400), how));
            }
            _ => *g = None,
        }
    }
    for n in &names {
        let p = target.join("release").join(n);
        if p.is_file() {
            return Ok(p.to_string_lossy().into_owned());
        }
    }
    if !build {
        return Err(format!("no native build in {}; {}", target.display(), how));
    }
    let log = target.join("relax-native-build.log").to_string_lossy().into_owned();
    let _ = std::fs::create_dir_all(&target);
    let f = std::fs::File::create(&log).map_err(|e| format!("cannot write {}: {}", log, e))?;
    let f2 = f.try_clone().map_err(|e| e.to_string())?;
    let mut cmd = std::process::Command::new("nice");
    cmd.args(["-n", "15", "cargo", "build", "--release", "-j", "4", "--manifest-path"])
        .arg(std::path::Path::new(&dir).join("Cargo.toml"))
        .arg("--target-dir")
        .arg(&target)
        .env("CARGO_INCREMENTAL", "0")
        .env("CARGO_PROFILE_RELEASE_DEBUG", "line-tables-only")
        .env("CARGO_PROFILE_RELEASE_SPLIT_DEBUGINFO", "packed")
        .env_remove("RUSTC_WRAPPER")
        .env_remove("RUSTFLAGS")
        .stdin(std::process::Stdio::null())
        .stdout(f)
        .stderr(f2);
    for (k, _) in std::env::vars_os() {
        if k.to_string_lossy().starts_with("MAKEPAD_RUN_") {
            cmd.env_remove(&k);
        }
    }
    let child = cmd.spawn().map_err(|e| format!("cannot start cargo for the native baseline: {}; {}", e, how))?;
    let pid = child.id();
    *g = Some((child, log.clone()));
    Err(format!("building the native baseline of `{}` now (cargo build --release, line tables only, -j4, nice; pid {}, log {}); ask again when it is done", krate, pid, log))
}

/// Runs `f` with the native binary at `path` (read once, again when the file changes).
fn with_native<R>(path: &str, f: impl FnOnce(&NativeBin) -> R) -> Result<R, String> {
    let mtime = std::fs::metadata(path).and_then(|m| m.modified()).map_err(|e| format!("cannot read {}: {}", path, e))?;
    let mut g = NATIVE.lock().unwrap();
    if !matches!(&*g, Some((p, t, _)) if p == path && *t == mtime) {
        *g = Some((path.to_string(), mtime, NativeBin::open(path)?));
    }
    Ok(f(&g.as_ref().unwrap().2))
}

/// rustc's code of the fn named `ours` (a JIT display name): the symbol of the same path, the
/// instance whose generic arguments match, else the one closest in size; and how many others.
fn rustc_side(nb: &NativeBin, ours: &str, our_bytes: usize) -> Result<(Side, usize), String> {
    let plain = plain_name(ours);
    let mut cands = nb.find(&plain);
    if cands.is_empty() {
        // a trait method: rustc names it `<T as Trait>::m`, the query form is `T::m`
        let tail = callee_key(ours);
        cands = nb.find(&tail);
    }
    if cands.is_empty() {
        return Err(format!("rustc has no symbol for `{}` in {} (it inlined every call, or the path differs); try: asm <its caller> vs=rustc", short(&plain, 100), file_name(&nb.path)));
    }
    let squash = |s: &str| s.replace(' ', "");
    let exact: Vec<_> = cands.iter().filter(|c| squash(&c.name) == squash(ours)).collect();
    let pick = if let Some(c) = exact.first() {
        **c
    } else {
        *cands.iter().min_by_key(|c| (c.size as i64 - our_bytes as i64).unsigned_abs()).unwrap()
    };
    let code = nb.code(pick);
    let insns = dis::decode(nb.arch, code, pick.addr);
    let mut s = Side::new("rustc".into(), pick.name.clone(), pick.addr, insns);
    // lines
    let rows = nb.lines(pick.addr, pick.addr + pick.size);
    let mut idx = HashMap::new();
    let mut r = 0;
    for k in 0..s.insns.len() {
        let a = pick.addr + s.insns[k].off as u64;
        while r + 1 < rows.len() && rows[r + 1].addr <= a {
            r += 1;
        }
        if let Some(row) = rows.get(r).filter(|row| row.addr <= a && row.line != 0) {
            let path = nb.file(row.file);
            s.at[k] = s.line_index(&mut idx, format!("{}:{}", path_key(&path), row.line), format!("{}:{}", file_name(&path), row.line));
        }
    }
    // inline levels: the deepest inlined call covering each instruction
    let inl = nb.inlined(pick.addr, pick.addr + pick.size);
    for k in 0..s.insns.len() {
        let a = pick.addr + s.insns[k].off as u64;
        if let Some(c) = inl.iter().filter(|c| c.ranges.iter().any(|&(lo, hi)| a >= lo && a < hi)).max_by_key(|c| c.depth) {
            s.inl[k] = (c.name.clone(), c.depth.min(255) as u8);
        }
    }
    for k in 0..s.insns.len() {
        if s.insns[k].class == Class::Call {
            s.callee[k] = s.insns[k].target.and_then(|t| nb.fn_at(t)).map(|f| f.name.clone());
        }
    }
    s.find_checks();
    Ok((s, cands.len() - 1))
}

// ------------------------------------------------------------------ samples

/// CPU samples of every program thread for `secs` (0: none): innermost pcs and the return
/// address above them.
fn sample(secs: f64, hz: u64, ev: super::prof::Ev, out: &Out) -> (Vec<(u64, u64, u64)>, f64, Vec<String>, super::prof::Ev) {
    if secs <= 0.0 {
        return (Vec::new(), 0.0, Vec::new(), ev);
    }
    let gone = out.gone();
    let run = super::prof::collect_ev(secs, hz, ev, &|_| true, &*gone);
    let v = run.samples.iter().filter_map(|s| s.frames.first().map(|&pc| (pc, s.frames.get(1).copied().unwrap_or(0), s.weight.max(1)))).collect();
    (v, run.secs, run.notes, run.ev)
}

fn attach_samples(s: &mut Side, pcs: &[(u64, u64, u64)]) {
    let lo = s.addr;
    let hi = s.addr + s.insns.last().map_or(0, |i| i.off as u64 + i.len as u64);
    let find = |s: &Side, pc: u64| -> Option<usize> {
        let off = pc.checked_sub(lo)? as u32;
        let k = s.insns.partition_point(|i| i.off <= off);
        k.checked_sub(1)
    };
    for &(pc, ret, w) in pcs {
        if pc >= lo && pc < hi {
            if let Some(k) = find(s, pc) {
                s.samples[k] += w;
            }
        } else if ret > lo && ret <= hi {
            // the call right before the return address
            if let Some(k) = find(s, ret - 1) {
                s.below[k] += w;
            }
        }
    }
}

// ------------------------------------------------------------------ comparison

/// Instruction classes as short tags for mixes: `3sld 2sst 4alu 1jcc`.
fn tag(c: Class) -> &'static str {
    match c {
        Class::Load => "ld",
        Class::Store => "st",
        Class::StackLoad => "sld",
        Class::StackStore => "sst",
        Class::PushPop => "pp",
        Class::MovReg => "mov",
        Class::MovImm => "imm",
        Class::Addr => "lea",
        Class::Alu => "alu",
        Class::Mul => "mul",
        Class::Div => "div",
        Class::Cmp => "cmp",
        Class::Select => "sel",
        Class::Fp => "fp",
        Class::Vector => "vec",
        Class::CondBranch => "jcc",
        Class::Branch => "jmp",
        Class::IndirectBranch => "ijmp",
        Class::Call => "call",
        Class::IndirectCall => "icall",
        Class::Ret => "ret",
        Class::Atomic => "atom",
        Class::Trap => "trap",
        Class::Nop => "nop",
        Class::Other => "oth",
        Class::Unknown => "?",
    }
}

const LEGEND: &str = "legend: sld/sst = stack-frame loads/stores (spills, reloads, slots), ld/st = other memory, mov = reg copies, imm = constants, lea = address math, jcc = cond branches, vec = packed SIMD, chk = branches to a panic (bounds/overflow/unwrap)";

#[derive(Default, Clone)]
struct Tally {
    n: u32,
    by: HashMap<Class, u32>,
    checks: u32,
    calls: Vec<String>,
}

impl Tally {
    fn add(&mut self, s: &Side, k: usize) {
        self.n += 1;
        *self.by.entry(s.insns[k].class).or_default() += 1;
        if s.check[k].is_some() {
            self.checks += 1;
        }
        if s.insns[k].class == Class::Call {
            if let Some(c) = &s.callee[k] {
                self.calls.push(c.clone());
            }
        }
    }
    fn get(&self, c: Class) -> u32 {
        self.by.get(&c).copied().unwrap_or(0)
    }
    fn spill(&self) -> u32 {
        self.get(Class::StackLoad) + self.get(Class::StackStore) + self.get(Class::PushPop)
    }
    fn mix(&self) -> String {
        let mut v: Vec<(Class, u32)> = self.by.iter().map(|(c, n)| (*c, *n)).collect();
        v.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(&b.0)));
        let mut s: Vec<String> = v.iter().take(6).map(|(c, n)| format!("{}{}", n, tag(*c))).collect();
        if self.checks > 0 {
            s.push(format!("{}chk", self.checks));
        }
        s.join(" ")
    }
}

/// Per-line join of the two sides: line key -> (ours, rustc).
struct Joined {
    keys: Vec<String>,
    show: Vec<String>,
    ours: Vec<Tally>,
    theirs: Vec<Tally>,
    /// samples / PGO count of the line (ours)
    samples: Vec<u64>,
    count: Vec<u64>,
    /// first instruction index of the line on our side (code order)
    first: Vec<usize>,
}

fn join(a: &Side, b: Option<&Side>) -> Joined {
    let mut j = Joined { keys: Vec::new(), show: Vec::new(), ours: Vec::new(), theirs: Vec::new(), samples: Vec::new(), count: Vec::new(), first: Vec::new() };
    let mut idx: HashMap<String, usize> = HashMap::new();
    let mut slot = |j: &mut Joined, key: &str, show: &str, first: usize| -> usize {
        if let Some(&k) = idx.get(key) {
            return k;
        }
        let k = j.keys.len();
        idx.insert(key.to_string(), k);
        j.keys.push(key.to_string());
        j.show.push(show.to_string());
        j.ours.push(Tally::default());
        j.theirs.push(Tally::default());
        j.samples.push(0);
        j.count.push(0);
        j.first.push(first);
        k
    };
    for k in 0..a.insns.len() {
        let (key, show) = match a.lines.get(a.at[k] as usize) {
            Some(l) => (l.key.as_str(), l.show.as_str()),
            None => ("?", "(no line)"),
        };
        let x = slot(&mut j, key, show, k);
        j.ours[x].add(a, k);
        j.samples[x] += a.samples[k];
        j.count[x] = j.count[x].max(a.count[k].unwrap_or(0));
    }
    if let Some(b) = b {
        for k in 0..b.insns.len() {
            let (key, show) = match b.lines.get(b.at[k] as usize) {
                Some(l) => (l.key.as_str(), l.show.as_str()),
                None => ("?", "(no line)"),
            };
            let x = slot(&mut j, key, show, usize::MAX);
            j.theirs[x].add(b, k);
        }
    }
    j
}

fn pct(a: u64, t: u64) -> String {
    if t == 0 {
        "-".into()
    } else {
        let p = a as f64 * 100.0 / t as f64;
        if p >= 10.0 {
            format!("{:.0}", p)
        } else {
            format!("{:.1}", p)
        }
    }
}

/// What sample totals count, for headers.
fn ev_unit(ev: super::prof::Ev) -> &'static str {
    match ev {
        super::prof::Ev::Cpu => "samples",
        e => e.name(),
    }
}

fn count_str(c: u64) -> String {
    match c {
        0 => "-".into(),
        c if c >= 10_000_000 => format!("{:.0}M", c as f64 / 1e6),
        c if c >= 1_000_000 => format!("{:.1}M", c as f64 / 1e6),
        c if c >= 10_000 => format!("{:.0}k", c as f64 / 1e3),
        c => c.to_string(),
    }
}

/// The ranked findings of the comparison: (weight, text).
fn findings(a: &Side, b: &Side, j: &Joined) -> Vec<(f64, String)> {
    let by_samples = a.total_samples() > 0;
    let by_count = !by_samples && a.count.iter().any(|c| c.unwrap_or(0) > 0);
    let tot_w: f64 = (0..a.insns.len()).map(|k| a.weight(k, by_samples, by_count)).sum::<f64>().max(1.0);
    let mut out: Vec<(f64, String)> = Vec::new();
    // hot loops: our innermost loops by weight, compared on the lines they hold
    let loops = a.loops();
    let mut seen_lines: Vec<std::collections::HashSet<String>> = Vec::new();
    let mut ranked: Vec<(f64, usize, usize)> = loops.iter().map(|&(h, t)| ((h..=t).map(|k| a.weight(k, by_samples, by_count)).sum::<f64>(), h, t)).collect();
    ranked.sort_by(|x, y| y.0.partial_cmp(&x.0).unwrap_or(std::cmp::Ordering::Equal));
    for &(w, h, t) in ranked.iter().take(6) {
        let keys: std::collections::HashSet<String> = (h..=t).filter_map(|k| a.lines.get(a.at[k] as usize).map(|l| l.key.clone())).collect();
        // a loop whose lines an earlier (hotter, inner) loop already covered adds nothing
        if keys.is_empty() || seen_lines.iter().any(|s| keys.is_subset(s)) {
            continue;
        }
        seen_lines.push(keys.clone());
        let mut ours = Tally::default();
        for k in h..=t {
            ours.add(a, k);
        }
        let mut theirs = Tally::default();
        for k in 0..b.insns.len() {
            if b.lines.get(b.at[k] as usize).map_or(false, |l| keys.contains(&l.key)) {
                theirs.add(b, k);
            }
        }
        let head = a.lines.get(a.at[h] as usize).map_or("(no line)".to_string(), |l| l.show.clone());
        let share = w * 100.0 / tot_w;
        let mut what = Vec::new();
        let d_sp = ours.spill() as i64 - theirs.spill() as i64;
        if d_sp > 0 {
            what.push(format!("+{} stack loads/stores (spills/reloads: ours {}, rustc {})", d_sp, ours.spill(), theirs.spill()));
        }
        let d_mov = (ours.get(Class::MovReg) + ours.get(Class::MovImm)) as i64 - (theirs.get(Class::MovReg) + theirs.get(Class::MovImm)) as i64;
        if d_mov > 1 {
            what.push(format!("+{} moves", d_mov));
        }
        let d_br = (ours.get(Class::CondBranch) + ours.get(Class::Branch)) as i64 - (theirs.get(Class::CondBranch) + theirs.get(Class::Branch)) as i64;
        if d_br > 0 {
            what.push(format!("+{} branches", d_br));
        }
        if ours.checks > theirs.checks {
            what.push(format!("{} check(s) rustc does not have ({} vs {})", ours.checks - theirs.checks, ours.checks, theirs.checks));
        }
        if theirs.get(Class::Vector) > 0 && ours.get(Class::Vector) == 0 {
            what.push(format!("not vectorised (rustc: {} vector instr)", theirs.get(Class::Vector)));
        }
        let ours_calls: Vec<String> = ours.calls.iter().map(|c| callee_key(c)).collect();
        let their_calls: std::collections::HashSet<String> = theirs.calls.iter().map(|c| callee_key(c)).collect();
        let mut extra_calls: Vec<String> = ours_calls.iter().filter(|c| !their_calls.contains(*c) && check_kind(c).is_none()).cloned().collect();
        extra_calls.sort();
        extra_calls.dedup();
        if !extra_calls.is_empty() {
            what.push(format!("calls rustc has not: {}", extra_calls.iter().take(4).map(|c| format!("`{}`", c)).collect::<Vec<_>>().join(", ")));
        }
        let d = ours.n as i64 - theirs.n as i64;
        let text = format!("loop at {} ({}% of {}): ours {} instr vs rustc {} on its lines ({:+}){}{}", head, pct(w as u64, tot_w as u64), if by_samples { "samples" } else if by_count { "PGO count" } else { "code" }, ours.n, theirs.n, d, if what.is_empty() { "" } else { "; " }, what.join("; "));
        out.push((share * (d.max(0) as f64 + 1.0), text));
    }
    // calls not inlined (whole fn): our direct calls to fns rustc's code never calls
    let their_calls: std::collections::HashSet<String> = b.callee.iter().flatten().map(|c| callee_key(c)).collect();
    let mut calls: HashMap<String, (u32, u64, Vec<String>, String, Option<String>)> = HashMap::new();
    for k in 0..a.insns.len() {
        let Some(c) = &a.callee[k] else { continue };
        if check_kind(c).is_some() || their_calls.contains(&callee_key(c)) {
            continue;
        }
        let e = calls.entry(callee_key(c)).or_insert((0, 0, Vec::new(), c.clone(), None));
        e.0 += 1;
        if e.4.is_none() {
            e.4 = a.why[k].clone();
        }
        e.1 += a.below[k] + a.count[k].unwrap_or(0) * u64::from(!by_samples);
        if let Some(l) = a.lines.get(a.at[k] as usize) {
            if !e.2.contains(&l.show) {
                e.2.push(l.show.clone());
            }
        }
    }
    let tot_s = a.total_samples().max(1);
    for (key, (n, w, lines, full, why)) in calls {
        let share = if by_samples { w as f64 * 100.0 / tot_s as f64 } else { 0.0 };
        out.push((
            share + 0.5 * n as f64,
            format!(
                "call to `{}` not inlined ({} site(s) at {}){}; rustc inlined it or has no such call; why: {}",
                short(&plain_name(&full), 90),
                n,
                lines.iter().take(3).cloned().collect::<Vec<_>>().join(", "),
                if by_samples && w > 0 { format!(", {}% of samples below it", pct(w, tot_s)) } else { String::new() },
                why.unwrap_or_else(|| "no O3 remark (not an O3 build, a cold path, or a call made after inlining: lowering / runtime helper)".into())
            ),
        ));
        let _ = key;
    }
    // checks kept, per line
    for x in 0..j.keys.len() {
        if j.ours[x].checks > j.theirs[x].checks && j.keys[x] != "?" {
            let kinds: Vec<&str> = (0..a.insns.len()).filter(|&k| a.at[k] != u32::MAX && a.lines[a.at[k] as usize].key == j.keys[x]).filter_map(|k| a.check[k]).collect();
            let mut kinds = kinds;
            kinds.sort();
            kinds.dedup();
            let w = if by_samples { j.samples[x] as f64 * 100.0 / tot_s as f64 } else { 0.0 };
            out.push((w + 0.3, format!("{} check kept at {} (ours {}, rustc {})", kinds.join("/"), j.show[x], j.ours[x].checks, j.theirs[x].checks)));
        }
    }
    out.sort_by(|x, y| y.0.partial_cmp(&x.0).unwrap_or(std::cmp::Ordering::Equal).then(x.1.cmp(&y.1)));
    out
}

// ------------------------------------------------------------------ rendering

fn listing_row(s: &Side, k: usize, show_cost: bool) -> String {
    let i = &s.insns[k];
    let mut t = i.text();
    if let Some(c) = &s.callee[k] {
        t = format!("{} ; {}", i.mnem, short(&plain_name(c), 60));
    }
    if let Some(c) = s.check[k] {
        t.push_str(&format!(" ; {} check", c));
    }
    if let Some(w) = &s.why[k] {
        t.push_str(&format!(" ; kept: {}", short(w, 70)));
    }
    if matches!(i.class, Class::StackLoad | Class::StackStore) {
        t.push_str(" ·stack");
    }
    if !s.inl[k].0.is_empty() {
        t.push_str(&format!(" ·in {}", short(&plain_name(&s.inl[k].0), 40)));
    }
    if show_cost && (s.samples[k] > 0 || s.below[k] > 0) {
        format!("{:>4}{} {}", s.samples[k], if s.below[k] > 0 { format!("(+{})", s.below[k]) } else { String::new() }, t)
    } else {
        t
    }
}

/// `asm <fn|@slot> [vs=rustc] [native=<bin>] [s=2] [hz=1000] [view=summary|lines|listing|ours] [line=<n>] [n=12]`
/// and `asm top [vs=rustc] [s=3] [n=15]`.
pub fn cmd_asm(req: &Req, out: &mut Out) {
    let Some(q) = req.pos.first().cloned() else {
        out.err("usage: asm <fn|@slot> [vs=rustc native=<binary>] [s=2] [view=summary|lines|listing|ours] [line=<n>]  |  asm top vs=rustc [s=3]");
        return;
    };
    if q == "top" {
        return cmd_top(req, out);
    }
    let secs = req.get("s").and_then(|v| v.parse::<f64>().ok()).unwrap_or(2.0).clamp(0.0, 30.0);
    let hz = req.num("hz", 1000).clamp(10, 4000);
    let ev = match super::prof::Ev::parse(req.get("ev").unwrap_or("cpu")) {
        Ok(e) => e,
        Err(e) => return out.err(&e),
    };
    let vs = req.get("vs").map_or(req.get("native").is_some(), |v| v == "rustc");
    let view = req.get("view").unwrap_or("summary");
    let n = req.num("n", 12) as usize;
    // ranges first (cheap), then samples, then the code again if it changed while sampling
    let (mut sides, mut notes) = match our_sides(&q, 32) {
        Ok(x) => x,
        Err(e) => return out.err(&e),
    };
    if sides.is_empty() {
        notes.insert(0, format!("`{}` has no JIT code body", q));
        return out.err(&notes.join("; "));
    }
    let starts: Vec<u64> = sides.iter().map(|s| s.1.addr).collect();
    let (pcs, took, mut snotes, ev) = sample(secs, hz, ev, out);
    if out.cancelled() {
        return;
    }
    if let Ok((again, _)) = our_sides(&q, 32) {
        if again.iter().map(|s| s.1.addr).collect::<Vec<_>>() != starts {
            snotes.push("the fn's code changed while sampling (a tier-up installed): samples in the new code are not counted; ask again".into());
            sides = again;
        }
    }
    for (_, s) in sides.iter_mut() {
        attach_samples(s, &pcs);
    }
    // the body to show: the one with the most samples, else the installed one with the most code
    sides.sort_by_key(|(_, s)| (std::cmp::Reverse(s.total_samples()), !s.label.ends_with(')') as u8 ^ 1, std::cmp::Reverse(s.insns.len())));
    let others = sides.len() - 1;
    let others_samples: u64 = sides[1..].iter().map(|s| s.1.total_samples()).sum();
    let (slot, a) = sides.swap_remove(0);
    let b = if vs {
        match native_path(req).and_then(|p| with_native(&p, |nb| rustc_side(nb, &a.name, a.insns.last().map_or(0, |i| i.off as usize + i.len as usize))).and_then(|r| r)) {
            Ok((s, more)) => {
                if more > 0 {
                    notes.push(format!("rustc has {} more instance(s) of the name; picked the closest in size", more));
                }
                Some(s)
            }
            Err(e) => {
                notes.push(e);
                None
            }
        }
    } else {
        None
    };
    render(out, slot, &a, b.as_ref(), view, req.get("line"), n, took, hz, ev, &pcs, others, others_samples, &notes, &snotes, &q);
}

#[allow(clippy::too_many_arguments)]
fn render(out: &mut Out, slot: u32, a: &Side, b: Option<&Side>, view: &str, line: Option<&str>, n: usize, took: f64, hz: u64, ev: super::prof::Ev, pcs: &[(u64, u64, u64)], others: usize, others_samples: u64, notes: &[String], snotes: &[String], q: &str) {
    let bytes = |s: &Side| s.insns.last().map_or(0, |i| i.off + i.len as u32);
    let ts = a.total_samples();
    let unknown = a.insns.iter().filter(|i| i.class == Class::Unknown).count() + b.map_or(0, |b| b.insns.iter().filter(|i| i.class == Class::Unknown).count());
    let j = join(a, b);
    // line 1: the finding
    let head = match b {
        Some(b) => {
            let d = a.insns.len() as i64 - b.insns.len() as i64;
            format!(
                "`{}`: ours {} instr ({}, {} B) vs rustc {} ({} B): {:+} ({:+.0}%){}",
                short(&a.name, 100),
                a.insns.len(),
                a.label.trim_start_matches("ours "),
                bytes(a),
                b.insns.len(),
                bytes(b),
                d,
                d as f64 * 100.0 / b.insns.len().max(1) as f64,
                if ts > 0 { format!("; {} {} in it ({:.1} s)", count_str(ts), ev_unit(ev), took) } else { String::new() }
            )
        }
        None => format!("`{}`: {} instr ({}, {} B){}", short(&a.name, 100), a.insns.len(), a.label.trim_start_matches("ours "), bytes(a), if ts > 0 { format!("; {} {} in it ({:.1} s at {} Hz)", count_str(ts), ev_unit(ev), took, hz) } else { String::new() }),
    };
    out.always(&head);
    let fnd = b.map(|b| findings(a, b, &j)).unwrap_or_default();
    if view == "summary" || view == "lines" {
        for (_, f) in fnd.iter().take(if view == "summary" { 6 } else { 3 }) {
            out.line(&format!("- {}", f));
        }
        if fnd.len() > 6 && view == "summary" {
            out.line(&format!("- +{} more findings (view=lines)", fnd.len() - 6));
        }
    }
    if view == "summary" {
        if let Some(b) = b {
            // class totals
            let mut ta = Tally::default();
            (0..a.insns.len()).for_each(|k| ta.add(a, k));
            let mut tb = Tally::default();
            (0..b.insns.len()).for_each(|k| tb.add(b, k));
            out.line("");
            out.line("| class | ours | rustc | Δ |");
            out.line("|---|---:|---:|---:|");
            let mut classes: Vec<Class> = ta.by.keys().chain(tb.by.keys()).copied().collect();
            classes.sort();
            classes.dedup();
            classes.sort_by_key(|c| std::cmp::Reverse((ta.get(*c) as i64 - tb.get(*c) as i64).abs()));
            for c in classes.iter().take(10) {
                out.line(&format!("| {} | {} | {} | {:+} |", c.name(), ta.get(*c), tb.get(*c), ta.get(*c) as i64 - tb.get(*c) as i64));
            }
            if classes.len() > 10 {
                out.line(&format!("| +{} classes | | | |", classes.len() - 10));
            }
            out.line(&format!("| checks (to panics) | {} | {} | {:+} |", ta.checks, tb.checks, ta.checks as i64 - tb.checks as i64));
        }
    }
    if view == "summary" || view == "lines" {
        // hottest lines (by samples, else PGO count, else excess)
        let mut order: Vec<usize> = (0..j.keys.len()).collect();
        let excess = |x: usize| j.ours[x].n as i64 - j.theirs[x].n as i64;
        order.sort_by_key(|&x| (std::cmp::Reverse(j.samples[x]), std::cmp::Reverse(j.count[x]), std::cmp::Reverse(excess(x))));
        let rows = if view == "lines" { order.len() } else { n.min(order.len()) };
        out.line("");
        if b.is_some() {
            out.line(&format!("| line | {} % | PGO count | ours | rustc | Δ | ours mix | rustc mix |", ev_unit(ev)));
            out.line("|---|---:|---:|---:|---:|---:|---|---|");
        } else {
            out.line(&format!("| line | {} % | PGO count | instr | mix |", ev_unit(ev)));
            out.line("|---|---:|---:|---:|---|");
        }
        for &x in order.iter().take(rows) {
            if b.is_some() {
                out.line(&format!("| {} | {} | {} | {} | {} | {:+} | {} | {} |", j.show[x], pct(j.samples[x], ts), count_str(j.count[x]), j.ours[x].n, j.theirs[x].n, excess(x), j.ours[x].mix(), j.theirs[x].mix()));
            } else {
                out.line(&format!("| {} | {} | {} | {} | {} |", j.show[x], pct(j.samples[x], ts), count_str(j.count[x]), j.ours[x].n, j.ours[x].mix()));
            }
        }
        if order.len() > rows {
            let rest: u64 = order[rows..].iter().map(|&x| j.samples[x]).sum();
            out.line(&format!("+{} more lines ({}% of samples): view=lines", order.len() - rows, pct(rest, ts)));
        }
        out.line(LEGEND);
    }
    if view == "listing" || view == "ours" {
        // per line, in our code order: our instructions, then rustc's at that line
        let want: Option<u32> = line.and_then(|l| l.rsplit(':').next()).and_then(|l| l.parse().ok());
        let mut order: Vec<usize> = (0..j.keys.len()).collect();
        order.sort_by_key(|&x| j.first[x]);
        for x in order {
            if let Some(w) = want {
                if !j.keys[x].ends_with(&format!(":{}", w)) {
                    continue;
                }
            }
            out.line(&format!("### {}  ours {} | rustc {}  (samples {}%, count {})", j.show[x], j.ours[x].n, j.theirs[x].n, pct(j.samples[x], ts), count_str(j.count[x])));
            out.line("```");
            for k in 0..a.insns.len() {
                if a.lines.get(a.at[k] as usize).map_or("?", |l| l.key.as_str()) == j.keys[x] {
                    out.line(&format!("{:5x}  {}", a.insns[k].off, listing_row(a, k, true)));
                }
            }
            if let (Some(b), true) = (b, view == "listing") {
                out.line("  -- rustc");
                for k in 0..b.insns.len() {
                    if b.lines.get(b.at[k] as usize).map_or("?", |l| l.key.as_str()) == j.keys[x] {
                        out.line(&format!("{:5x}  {}", b.insns[k].off, listing_row(b, k, false)));
                    }
                }
            }
            out.line("```");
        }
        if out.truncated {
            out.always("(cut at the reply limit: add line=<n> or full=1)");
        }
    }
    // what is not shown, how it was measured, drill-down
    let mut tail = Vec::new();
    if others > 0 {
        tail.push(format!("{} other code bodies/instances of the query ({} samples): asm {} with @<slot>; versions {}", others, others_samples, q, q));
    }
    if unknown > 0 {
        tail.push(format!("{} instructions the decoder does not know (shown as .byte/.word)", unknown));
    }
    if !pcs.is_empty() && ts == 0 {
        tail.push(format!("no samples in this code in {:.1} s ({} samples elsewhere): is it running? (PGO counts still show)", took, pcs.len()));
    }
    for s in notes.iter().chain(snotes) {
        tail.push(s.clone());
    }
    tail.push(super::reliability::line(took > 0.0));
    for t in tail {
        out.always(&format!("note: {}", t));
    }
    let lines_hint = j.keys.iter().zip(&j.samples).max_by_key(|x| x.1).map(|x| x.0.rsplit(':').next().unwrap_or("").to_string()).unwrap_or_default();
    out.always(&format!("more: asm @{} view=listing line={}  asm @{} view=lines  versions @{}  count {}", slot, lines_hint, slot, slot, q));
}

// ------------------------------------------------------------------ asm top

/// `asm top [vs=rustc] [s=3] [n=15]`: the hottest JIT fns ranked by the time their excess
/// instructions cost: samples x (ours - rustc) / ours.
fn cmd_top(req: &Req, out: &mut Out) {
    let secs = req.get("s").and_then(|v| v.parse::<f64>().ok()).unwrap_or(3.0).clamp(0.2, 30.0);
    let hz = req.num("hz", 1000).clamp(10, 4000);
    let n = req.num("n", 15) as usize;
    let vs = req.get("vs").map_or(req.get("native").is_some(), |v| v == "rustc");
    let ev = match super::prof::Ev::parse(req.get("ev").unwrap_or("cpu")) {
        Ok(e) => e,
        Err(e) => return out.err(&e),
    };
    let (pcs, took, snotes, ev) = sample(secs, hz, ev, out);
    if out.cancelled() {
        return;
    }
    let up = crate::jit::current_unit();
    if up.is_null() {
        return out.err("no running unit");
    }
    let jit_pcs: Vec<(u64, u64)> = pcs.iter().map(|x| (x.0, x.2)).filter(|&(pc, _)| crate::jit::in_jit_code(pc)).collect();
    let total: u64 = pcs.iter().map(|x| x.2).sum();
    let r = crate::owner::call_within(crate::owner::Class::Job, 10_000, move || {
        let u = unsafe { &*up };
        let tab = u.code.read().unwrap_or_else(|e| e.into_inner());
        let mut per: HashMap<u32, (u64, u64, u32)> = HashMap::new();
        for (pc, w) in jit_pcs {
            if let Some((start, len, id)) = tab.entry_at(pc) {
                let e = per.entry(id).or_insert((0, start, len));
                e.0 += w;
                if start == u.fns[id as usize].code {
                    e.1 = start;
                    e.2 = len;
                }
            }
        }
        drop(tab);
        let mut v: Vec<(u32, u64, u64, u32, String, String)> = per.into_iter().map(|(id, (c, st, len))| {
            let k = super::codever::kind_at(u, st);
            (id, c, st, len, super::display_name(u, id, 0), format!("{} {}", k.tier_name(), k.origin_name()))
        }).collect();
        v.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(&b.0)));
        v.truncate(60);
        v
    });
    let Some(hot) = r else {
        return out.err(&format!("the owner did not answer in 10 s ({})", crate::owner::serving_note()));
    };
    let jit_total: u64 = hot.iter().map(|x| x.1).sum();
    let native = if vs { native_path(req).ok() } else { None };
    let mut rows: Vec<(f64, String)> = Vec::new();
    let mut missing = 0;
    for (id, c, st, len, name, tier) in hot.iter() {
        let code = unsafe { std::slice::from_raw_parts(*st as *const u8, *len as usize) };
        let ours = dis::decode(Arch::host(), code, *st).len();
        let theirs = native.as_deref().and_then(|p| with_native(p, |nb| rustc_side(nb, name, *len as usize).ok().map(|s| s.0.insns.len())).ok().flatten());
        if vs && theirs.is_none() {
            missing += 1;
        }
        let excess = theirs.map(|t| (ours as f64 - t as f64) / ours.max(1) as f64);
        let score = *c as f64 * excess.unwrap_or(0.0).max(0.0);
        rows.push((
            if vs { score } else { *c as f64 },
            format!(
                "| @{} | {} | {} | {} | {} | {} | {} |",
                id,
                short(&name.replace('|', "/"), 70),
                pct(*c, total),
                tier,
                ours,
                theirs.map_or("?".into(), |t| t.to_string()),
                excess.map_or("?".into(), |e| format!("{}", pct((score * 1000.0) as u64, total * 1000)).to_string() + if e < 0.0 { " (ours smaller)" } else { "" }),
            ),
        ));
    }
    rows.sort_by(|a, b| b.0.partial_cmp(&a.0).unwrap_or(std::cmp::Ordering::Equal));
    let top = rows.first().map(|r| r.1.split('|').nth(2).unwrap_or("").trim().to_string()).unwrap_or_default();
    if vs {
        let est: f64 = rows.iter().map(|r| r.0).sum::<f64>() * 100.0 / total.max(1) as f64;
        out.always(&format!("excess JIT instructions cost an estimated {:.1}% of all {} ({} in JIT code of {} in {:.1} s); worst: {}", est, ev_unit(ev), count_str(jit_total), count_str(total), took, if top.is_empty() { "-".into() } else { top }));
    } else {
        out.always(&format!("{} of {} {} ({}%) in JIT code in {:.1} s; hottest: {}", count_str(jit_total), count_str(total), ev_unit(ev), pct(jit_total, total), took, if top.is_empty() { "-".into() } else { top }));
    }
    out.line("");
    out.line(&format!("| slot | fn | {} % | tier | ours instr | rustc instr | excess cost % |", ev_unit(ev)));
    out.line("|---|---|---:|---|---:|---:|---:|");
    for (_, r) in rows.iter().take(n) {
        out.line(r);
    }
    if rows.len() > n {
        out.line(&format!("+{} smaller fns", rows.len() - n));
    }
    out.always("note: excess cost % = samples % x (ours - rustc) / ours: the share of all samples the fn's extra instructions take if each instruction costs the same; `asm @<slot> vs=rustc` shows where they are");
    if missing > 0 {
        out.always(&format!("note: {} fns have no rustc symbol of the same path (inlined by rustc, or Relax-only names): excess ?", missing));
    }
    if vs && native.is_none() {
        out.always(&format!("note: {}", native_path(req).err().unwrap_or_default()));
    }
    for s in &snotes {
        out.always(&format!("note: {}", s));
    }
    out.always(&format!("note: {}", super::reliability::line(true)));
    out.always("more: asm @<slot> vs=rustc  asm @<slot> view=listing  prof threads=main");
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn plain_names() {
        assert_eq!(plain_name("alloc::vec::Vec<u8>::push"), "alloc::vec::Vec::push");
        assert_eq!(plain_name("<alloc::vec::Vec<T> as core::ops::Drop>::drop"), "alloc::vec::Vec::drop");
        assert_eq!(plain_name("core::ptr::drop_in_place<alloc::string::String>"), "core::ptr::drop_in_place");
        assert_eq!(plain_name("foo::bar::h0123456789abcdef"), "foo::bar");
        assert_eq!(callee_key("<alloc::vec::Vec<T> as core::ops::Drop>::drop"), "Vec::drop");
    }

    #[test]
    fn path_keys() {
        assert_eq!(path_key("/rustc/abc123/library/core/src/slice/mod.rs"), "core/slice/mod.rs");
        assert_eq!(path_key("/Users/x/makepad/libs/relax/compiler/std/core/slice/mod.rs"), "core/slice/mod.rs");
        assert_eq!(path_key("/home/a/rc/x/src/widgets/src/view.rs"), "widgets/src/view.rs");
    }
}
