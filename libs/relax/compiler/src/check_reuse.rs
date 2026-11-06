//! `makepad check` reuses the verdict of every checked crate whose inputs did not change since a
//! check that passed: its diagnostics, as that check printed them, without checking the crate
//! again (as cargo check keeps an unchanged crate's metadata).
//!
//! A crate's key (`Reuse::open_in`) is what its check's output rests on: the Relax build and its
//! options, every `MAKEPAD_RUN_*` variable (the command line's lint flags among them), the checked
//! crates and the root, the crate as rustc is invoked on it (name, root, edition, cfg with the
//! features, binary or not, test harness, its dependencies by alias) and the text of every file of
//! it; and of each crate of its dependency closure, the interface (cache/items.rs: its items
//! outside the fn bodies that are holes; a file the load skipped by its text) when that crate is
//! checked too, its text when it is not (std, a registry crate), and the text of its whole
//! closure when it is a proc-macro crate (its code makes the expansions). The file hashes are the
//! front's (ParsedFile::source_hash: the graph certificate's memo on a warm start). So a body
//! edit in a dependency checks that dependency again, not every crate above it.
//!
//! What the key cannot name travels with the verdict and is checked before the verdict is used:
//! the macro inputs outside the source that the crate and its closure read (include_str!,
//! include!, env!: session sip.rs late inputs, which lazily parsed bodies read after the load),
//! and the text of every other crate a stored diagnostic points into.
//!
//! A verdict (`KIND_CRATE`) is the crate's diagnostics as the check rendered them, each with where
//! the sort places it (check_order.rs: its stage and its group, by path) and whether only a check
//! whose required analyses passed reports it (`LATE`) or only one whose well-formedness checks ran
//! (`WF`). Only a check with no error, and nothing accepted only in relaxed Rust, stores verdicts.
//! A check replays the hits' diagnostics among its own (the sort merges them, one of each text)
//! and runs the per-crate passes on the other crates only (check.rs); the cross-crate checks
//! (duplicate symbols, the allocator and lang items, the entry point, monomorphization) and the
//! check-wide gates still see every crate.
//!
//! When every crate hits and a passing check of the same keys stored its run record (`KIND_RUN`:
//! it printed no signature error, of any crate), the check prints the stored diagnostics right
//! after the load (run.rs), before declaration collection: nothing a check prints in between
//! rests on anything but the keys' inputs and those errors.
use crate::check_order::{Entry, GroupAt, Out, Phase, Stage};
use crate::program::{Program, NO_DEF};
use crate::sip::Sip128;
use std::collections::HashMap;
use std::path::{Path, PathBuf};

const VERSION: u32 = 1;
const KIND_CRATE: u32 = 1;
const KIND_RUN: u32 = 2;
/// a late lint: printed only when the required analyses passed (check_order.rs Stage::required)
pub(crate) const LATE: u8 = 1;
/// reported by the well-formedness checks, which run only when nothing failed before them
pub(crate) const WF: u8 = 2;

/// A stored diagnostic.
struct Stored { phase: Phase, step: u8, flags: u8, seq: u32, group: GroupAt, text: String }

/// A decoded verdict.
struct Verdict {
    /// (crate name, kind, name, content hash): the late inputs it rests on
    late: Vec<(String, u8, String, u128)>,
    /// (crate identity, its text): the other crates its diagnostics point into
    refs: Vec<(u128, u128)>,
    entries: Vec<Stored>,
}

/// One check's reuse: the checked crates' keys, the hits and their diagnostics.
pub(crate) struct Reuse {
    path: PathBuf,
    write: bool,
    checked: Vec<u32>,
    /// parallel to `checked`
    keys: Vec<u128>,
    hit: Vec<bool>,
    /// a hit's verdict as stored (a rewrite of the store keeps it)
    raw: Vec<Option<Vec<u8>>>,
    closures: Vec<Vec<u32>>,
    stored: Vec<Stored>,
    run_key: u128,
    run_hit: bool,
    /// by crate: identity, text
    idents: Vec<u128>,
    texts: Vec<u128>,
    store_entries: usize,
    /// run.rs: no signature error was printed (a run record may be stored)
    pub(crate) sig_clean: bool,
    pub(crate) t_keys: std::time::Duration,
    /// files the load skipped: of the checked crates, of the others
    pub(crate) skipped: (usize, usize),
}

/// What a check's crates' keys rest on beyond the crates: the Relax build and options, the
/// variables that steer the check.
fn env_key(prog: &Program) -> u128 {
    let mut h = Sip128::new();
    h.str("relax-check-env");
    h.u32(VERSION);
    h.u128(crate::codegen_id::id());
    h.u128(prog.session.options.fingerprint());
    let mut vars: Vec<(String, String)> = std::env::vars_os()
        .filter_map(|(k, v)| Some((k.into_string().ok()?, v.to_string_lossy().into_owned())))
        .filter(|(k, _)| k.starts_with("MAKEPAD_RUN_"))
        .collect();
    vars.sort();
    h.u32(vars.len() as u32);
    for (k, v) in vars { h.str(&k); h.str(&v); }
    h.finish128()
}

/// The crate's identity: as rustc is invoked on it.
fn ident(prog: &Program, c: u32) -> u128 {
    let ci = &prog.crates[c as usize];
    crate::crate_image::fingerprint_head(prog.syms.str(ci.name), ci.root_path(), ci.edition, ci.proc_macro, &ci.cfg.set).finish128()
}

/// The files the load skipped: (crate, path, content hash). They have no parse: their text is
/// their input (the selection read them already).
fn skipped_files(prog: &Program) -> Vec<(u32, String, u128)> {
    prog.skipped_files.iter().filter_map(|(m, (path, ..))| {
        let c = prog.mods.get(*m as usize)?.krate;
        // (an unreadable file: its absence is the input)
        Some((c, path.clone(), crate::vfs::read(path).map_or(0, |src| crate::crate_image::file_hash(path, &src))))
    }).collect()
}

/// Each crate's files: (path, content hash) by path, with the `skipped` ones; `iface`: the
/// interface hash instead for the loaded files of the crates it marks.
fn crate_files(prog: &Program, iface: &[bool], skipped: &[(u32, String, u128)]) -> Vec<Vec<(String, u128)>> {
    let n = prog.crates.len();
    let want: Vec<usize> = (0..prog.files.len())
        .filter(|f| !prog.front_macro_fragments.contains(f) && prog.file_crate.get(*f).is_some_and(|&c| iface.get(c as usize).copied().unwrap_or(false)))
        .collect();
    let ifaces = if want.is_empty() { Vec::new() } else { crate::cache::file_ifaces(prog, &want) };
    let mut files: Vec<Vec<(String, u128)>> = vec![Vec::new(); n];
    for f in 0..prog.files.len() {
        if prog.front_macro_fragments.contains(&f) { continue; }
        let (Some(&c), Some(path)) = (prog.file_crate.get(f), prog.file_paths.get(f)) else { continue };
        let Some(v) = files.get_mut(c as usize) else { continue };
        let h = match ifaces.get(f).copied().flatten() {
            Some(i) => i,
            None => prog.files[f].source_hash(path),
        };
        v.push((path.clone(), h));
    }
    for (c, path, h) in skipped {
        if let Some(v) = files.get_mut(*c as usize) { v.push((path.clone(), *h)); }
    }
    for v in &mut files { v.sort_unstable(); v.dedup(); }
    files
}

/// A crate's hash over `files` (crate_files), with its identity and its dependencies by alias.
fn crate_hash(prog: &Program, c: u32, what: &str, idents: &[u128], files: &[(String, u128)]) -> u128 {
    let ci = &prog.crates[c as usize];
    let mut h = Sip128::new();
    h.str(what);
    h.u128(idents[c as usize]);
    let mut deps: Vec<(&str, u128)> = ci.deps.iter().filter(|(_, d)| *d != c).map(|&(a, d)| (prog.syms.str(a), idents[d as usize])).collect();
    deps.sort_unstable();
    deps.dedup();
    h.u32(deps.len() as u32);
    for (a, d) in deps { h.str(a); h.u128(d); }
    h.u32(files.len() as u32);
    for (p, x) in files { h.str(p); h.u128(*x); }
    h.finish128()
}

/// The text of crate `c` and of every crate of its closure (a proc-macro crate's code).
fn deep_text(prog: &Program, c: u32, texts: &[u128]) -> u128 {
    let mut v: Vec<u128> = crate::check::dependency_closure(prog, c).iter().map(|&d| texts[d as usize]).collect();
    v.sort_unstable();
    let mut h = Sip128::new();
    h.str("deep-text");
    h.u128(texts[c as usize]);
    h.u32(v.len() as u32);
    for x in v { h.u128(x); }
    h.finish128()
}

/// The current value of a late input (as the front validates its images: cache.rs).
fn late_current(c: &str, kind: u8, name: &str, hash: u128) -> bool {
    let content = if kind == crate::sip::LATE_FILE { crate::vfs::read(name).ok() } else { crate::crates::crate_env_named(c, name).map(String::into_bytes) };
    crate::sip::late_hash(content.as_deref()) == hash
}

impl Reuse {
    /// The reuse of a one-shot check of `checked` rooted at `root`, in the cache's folder. None:
    /// the cache is off, or verifying (every crate is checked).
    pub(crate) fn open(prog: &Program, root: u32, checked: &[u32]) -> Option<Reuse> {
        let mode = crate::cache::mode_from_env(&prog.session.options)?;
        if mode == crate::cache::Mode::Verify { return None; }
        Some(Self::open_in(prog, root, checked, &crate::dirs::relax_dir().join("cache"), mode == crate::cache::Mode::On))
    }

    /// `open` with the store in `dir`; `write`: this check stores what it finds.
    pub(crate) fn open_in(prog: &Program, root: u32, checked: &[u32], dir: &Path, write: bool) -> Reuse {
        let t0 = std::time::Instant::now();
        let n = prog.crates.len();
        let mut checked = checked.to_vec();
        checked.sort_unstable();
        checked.dedup();
        let idents: Vec<u128> = (0..n as u32).map(|c| ident(prog, c)).collect();
        let mut is_checked = vec![false; n];
        for &c in &checked { is_checked[c as usize] = true; }
        let closures: Vec<Vec<u32>> = checked.iter().map(|&c| crate::check::dependency_closure(prog, c)).collect();
        // the checked crates some checked crate depends on: their interfaces
        let mut iface_of = vec![false; n];
        for d in closures.iter().flatten() {
            if is_checked[*d as usize] && !prog.crates[*d as usize].proc_macro { iface_of[*d as usize] = true; }
        }
        let skipped = skipped_files(prog);
        let text_files = crate_files(prog, &[], &skipped);
        let texts: Vec<u128> = (0..n as u32).map(|c| crate_hash(prog, c, "check-text", &idents, &text_files[c as usize])).collect();
        let iface_files = if iface_of.iter().any(|x| *x) { crate_files(prog, &iface_of, &skipped) } else { Vec::new() };
        let ifaces: Vec<u128> = (0..n as u32).map(|c| if iface_of[c as usize] { crate_hash(prog, c, "check-iface", &idents, &iface_files[c as usize]) } else { 0 }).collect();
        let mut deep: HashMap<u32, u128> = HashMap::new();
        let env = env_key(prog);
        let set = {
            let mut h = Sip128::new();
            h.str("relax-check-set");
            h.u128(idents[root as usize]);
            let mut v: Vec<u128> = checked.iter().map(|&c| idents[c as usize]).collect();
            v.sort_unstable();
            h.u32(v.len() as u32);
            for x in v { h.u128(x); }
            h.finish128()
        };
        let keys: Vec<u128> = checked.iter().zip(&closures).map(|(&c, closure)| {
            let ci = &prog.crates[c as usize];
            let mut h = Sip128::new();
            h.str("relax-check-crate");
            h.u128(env);
            h.u128(set);
            h.u128(texts[c as usize]);
            h.u8(ci.is_bin as u8);
            h.u8(ci.harness as u8);
            let mut v: Vec<u128> = closure.iter().map(|&d| {
                if prog.crates[d as usize].proc_macro { *deep.entry(d).or_insert_with(|| deep_text(prog, d, &texts)) }
                else if is_checked[d as usize] { ifaces[d as usize] }
                else { texts[d as usize] }
            }).collect();
            v.sort_unstable();
            h.u32(v.len() as u32);
            for x in v { h.u128(x); }
            h.finish128()
        }).collect();
        let run_key = {
            let mut h = Sip128::new();
            h.str("relax-check-run");
            h.u128(set);
            let mut v = keys.clone();
            v.sort_unstable();
            for x in v { h.u128(x); }
            h.finish128()
        };
        let path = dir.join(format!("check-{:016x}.rcs", set as u64));
        let mut r = Reuse {
            path, write, hit: vec![false; checked.len()], raw: vec![None; checked.len()], keys, checked, closures,
            stored: Vec::new(), run_key, run_hit: false, idents, texts, store_entries: 0, sig_clean: false, t_keys: Default::default(),
            skipped: (skipped.iter().filter(|s| is_checked[s.0 as usize]).count(), skipped.iter().filter(|s| !is_checked[s.0 as usize]).count()),
        };
        // MAKEPAD_RUN_CHECK_REUSE_TRACE: each crate's key parts (two checks' traces diff to what changed)
        if std::env::var_os("MAKEPAD_RUN_CHECK_REUSE_TRACE").is_some() {
            for c in 0..n {
                let j = r.checked.binary_search(&(c as u32)).ok();
                eprintln!("check-reuse-trace: {} checked={} text={:032x} iface={:032x} key={}", prog.syms.str(prog.crates[c].name), j.is_some(), r.texts[c], ifaces[c], j.map_or(String::new(), |j| format!("{:032x}", r.keys[j])));
                for (p, h) in text_files[c].iter().chain(iface_files.get(c).into_iter().flatten()) {
                    eprintln!("check-reuse-trace:   {} {:032x}", p, h);
                }
            }
            for s in &skipped { eprintln!("check-reuse-trace: skipped {} {}", prog.syms.str(prog.crates[s.0 as usize].name), s.1); }
            // (=<path part>[,<path part>..]: the interface text of the files whose path holds one)
            if let Some(parts) = std::env::var("MAKEPAD_RUN_CHECK_REUSE_TRACE").ok().filter(|v| v.len() > 1) {
                for (f, p) in prog.file_paths.iter().enumerate().filter(|(_, p)| parts.split(',').any(|q| !q.is_empty() && p.contains(q))) {
                    let pf = &prog.files[f];
                    let lazy = pf.ast.items.iter().filter(|it| matches!(&it.kind, crate::ast::ItemKind::Fn(sig, None, _) if pf.ast.fn_sig(*sig).lazy_body.is_some())).count();
                    eprintln!("check-reuse-trace: iface text of {} ({} items, {} lazy bodies, src {} of {}):\n{}", p, pf.ast.items.len(), lazy, pf.src_len, pf.src.len(), String::from_utf8_lossy(&crate::cache::file_iface_text(prog, f)));
                }
            }
        }
        if let Some(store) = crate::store::Store::open(&r.path) {
            r.store_entries = store.index.len();
            let by_ident: HashMap<u128, u32> = r.idents.iter().enumerate().map(|(c, &i)| (i, c as u32)).collect();
            let mut late_memo: HashMap<(String, u8, String, u128), bool> = HashMap::new();
            for j in 0..r.checked.len() {
                let Some((KIND_CRATE, p)) = store.get_checked(r.keys[j]) else { continue };
                let Some(v) = decode(p) else { continue };
                let late_ok = v.late.iter().all(|(c, k, name, h)| *late_memo.entry((c.clone(), *k, name.clone(), *h)).or_insert_with(|| late_current(c, *k, name, *h)));
                let refs_ok = v.refs.iter().all(|(i, t)| by_ident.get(i).is_some_and(|&c| r.texts[c as usize] == *t));
                if !late_ok || !refs_ok { continue; }
                r.hit[j] = true;
                r.raw[j] = Some(p.to_vec());
                r.stored.extend(v.entries);
            }
            r.run_hit = matches!(store.get_checked(r.run_key), Some((KIND_RUN, _)));
        }
        r.t_keys = t0.elapsed();
        r
    }

    /// Whether checked crate `c`'s verdict is reused.
    pub(crate) fn is_hit(&self, c: u32) -> bool {
        self.checked.binary_search(&c).is_ok_and(|j| self.hit[j])
    }

    pub(crate) fn hits(&self) -> usize { self.hit.iter().filter(|h| **h).count() }

    pub(crate) fn crates(&self) -> usize { self.checked.len() }

    /// Every crate hit and a passing check of the same keys stored its run record (run.rs: the
    /// check ends after the load).
    pub(crate) fn full(&self) -> bool { self.run_hit && self.hit.iter().all(|h| *h) }

    /// The hits' diagnostics: the late lints only when `late_ok`, the well-formedness checks'
    /// only when they ran (`wf_ran`), as the check that stored them would have reported them.
    pub(crate) fn replayed(&self, late_ok: bool, wf_ran: bool) -> Vec<Entry> {
        self.stored.iter().filter(|s| (late_ok || s.flags & LATE == 0) && (wf_ran || s.flags & WF == 0)).map(|s| Entry {
            stage: Stage::new(s.phase, s.step), seq: s.seq, out: Out::Warning(s.text.clone()), group_at: Some(s.group.clone()),
        }).collect()
    }

    /// A check whose every crate is unchanged (`full`): the stored diagnostics, printed as the
    /// check that stored them printed them, and the check's summary. Exit code 0 (the check that
    /// stored them passed).
    pub(crate) fn print_reused(&self, prog: &Program) -> i32 {
        let entries = crate::check_order::sort(prog, self.replayed(true, true));
        crate::check_order::print(&entries, true, true, crate::diag::enabled());
        eprintln!("makepad check: {} crates unchanged since a passing check: their verdicts reused", self.crates());
        eprintln!("makepad check: 0 body owners of the checked crates, 0 compiled in all, 0 errors");
        0
    }

    /// A passing check's diagnostics `entries` (its own: no replayed one; `flags` LATE / WF,
    /// parallel) stored as the verdicts of the crates that did not hit, and its run record
    /// when `sig_clean`. Nothing when a diagnostic belongs to no checked crate, or anything was
    /// accepted only in relaxed Rust (its report is the whole check's).
    pub(crate) fn record(&mut self, prog: &Program, entries: &[Entry], flags: &[u8]) {
        if !self.write { return; }
        let verbose = prog.session.options.verbose;
        if relax_types::borrowck::relaxed_pending() || crate::relaxed::pending() {
            if verbose { eprintln!("makepad check: verdicts not stored: sites accepted only in relaxed Rust"); }
            return;
        }
        let mut by_path: HashMap<&str, u32> = HashMap::new();
        for (f, p) in prog.file_paths.iter().enumerate() {
            if let Some(&c) = prog.file_crate.get(f) { by_path.entry(p.as_str()).or_insert(c); }
        }
        let mut per: Vec<Vec<usize>> = vec![Vec::new(); self.checked.len()];
        for (i, e) in entries.iter().enumerate() {
            let text = match &e.out { Out::Warning(s) => s.as_str(), _ => return };
            // whose check reported it: the definition it was reported in, else its place's crate
            let producer = if e.stage.group != NO_DEF && (e.stage.group.0 as usize) < prog.defs.len() { Some(prog.def(e.stage.group).krate) }
                else { crate::check_order::path_of(text).and_then(|p| by_path.get(p).copied()) };
            let Some(j) = producer.and_then(|k| self.checked.binary_search(&k).ok()) else {
                if verbose { eprintln!("makepad check: verdicts not stored: a diagnostic of no checked crate: {}", text.lines().next().unwrap_or("")); }
                return;
            };
            // (a hit's own diagnostics are in its stored verdict already)
            if !self.hit[j] { per[j].push(i); }
        }
        let stages: Vec<Stage> = entries.iter().map(|e| e.stage).collect();
        let groups = crate::check_order::groups_at(prog, &stages);
        let late = crate::sip::late_inputs();
        let mut new: Vec<crate::pack::NewEntry> = Vec::new();
        for j in 0..self.checked.len() {
            if self.hit[j] { continue; }
            let c = self.checked[j];
            // the late inputs of the crate and of its closure (by crate name, as the front notes them)
            let names: std::collections::HashSet<&str> = std::iter::once(c).chain(self.closures[j].iter().copied())
                .map(|k| prog.syms.str(prog.crates[k as usize].name)).collect();
            let mine: Vec<&(String, u8, String, u128)> = late.iter().filter(|(k, ..)| names.contains(k.as_str())).collect();
            // the other crates its diagnostics point into (their text: positions and the mod chains)
            let mut refs: Vec<(u128, u128)> = Vec::new();
            for &i in &per[j] {
                let Out::Warning(text) = &entries[i].out else { continue };
                let group = match &groups[i] { GroupAt::Path(p, ..) => Some(p.as_str()), _ => None };
                for p in crate::check_order::paths_named(text).into_iter().chain(group) {
                    if let Some(&k) = by_path.get(p) {
                        if k != c { refs.push((self.idents[k as usize], self.texts[k as usize])); }
                    }
                }
            }
            refs.sort_unstable();
            refs.dedup();
            let mut w = W(Vec::new());
            w.u32(VERSION);
            w.u32(mine.len() as u32);
            for (k, kind, name, h) in mine { w.str(k); w.0.push(*kind); w.str(name); w.u128(*h); }
            w.u32(refs.len() as u32);
            for (i, t) in &refs { w.u128(*i); w.u128(*t); }
            w.u32(per[j].len() as u32);
            for &i in &per[j] {
                let e = &entries[i];
                let Out::Warning(text) = &e.out else { continue };
                w.0.push(e.stage.phase.code());
                w.0.push(e.stage.step);
                w.0.push(flags[i]);
                w.u32(e.seq);
                match &groups[i] {
                    GroupAt::Zero => w.0.push(0),
                    GroupAt::At => w.0.push(1),
                    GroupAt::Path(p, l, col) => { w.0.push(2); w.str(p); w.u32(*l); w.u32(*col); }
                }
                w.str(text);
            }
            new.push(crate::pack::NewEntry { key: self.keys[j], kind: KIND_CRATE, payload: w.0 });
        }
        if self.sig_clean {
            new.push(crate::pack::NewEntry { key: self.run_key, kind: KIND_RUN, payload: VERSION.to_le_bytes().to_vec() });
        }
        if new.is_empty() { return; }
        // a store that holds many checks' worth of verdicts starts again from this check's
        let drop_all = self.store_entries > 8 * self.checked.len() + 64;
        if drop_all {
            for j in 0..self.checked.len() {
                if let Some(p) = self.raw[j].take() { new.push(crate::pack::NewEntry { key: self.keys[j], kind: KIND_CRATE, payload: p }); }
            }
        }
        let dir = self.path.parent().unwrap_or(Path::new("."));
        let r = dir.parent().map_or(Ok(()), crate::pack::ensure_private_dir).and_then(|_| crate::pack::ensure_private_dir(dir))
            .and_then(|_| crate::store::append(&self.path, new, drop_all).map_err(|e| e.to_string()));
        if verbose { eprintln!("makepad check: verdicts stored ({:?})", r.err()); }
    }
}

struct W(Vec<u8>);
impl W {
    fn u32(&mut self, x: u32) { self.0.extend_from_slice(&x.to_le_bytes()); }
    fn u128(&mut self, x: u128) { self.0.extend_from_slice(&x.to_le_bytes()); }
    fn str(&mut self, s: &str) { self.u32(s.len() as u32); self.0.extend_from_slice(s.as_bytes()); }
}

struct R<'a>(&'a [u8]);
impl<'a> R<'a> {
    fn take(&mut self, n: usize) -> Option<&'a [u8]> {
        if self.0.len() < n { return None; }
        let (a, b) = self.0.split_at(n);
        self.0 = b;
        Some(a)
    }
    fn u8(&mut self) -> Option<u8> { Some(self.take(1)?[0]) }
    fn u32(&mut self) -> Option<u32> { Some(u32::from_le_bytes(self.take(4)?.try_into().ok()?)) }
    fn u128(&mut self) -> Option<u128> { Some(u128::from_le_bytes(self.take(16)?.try_into().ok()?)) }
    fn str(&mut self) -> Option<String> { let n = self.u32()? as usize; String::from_utf8(self.take(n)?.to_vec()).ok() }
}

fn decode(p: &[u8]) -> Option<Verdict> {
    let mut r = R(p);
    if r.u32()? != VERSION { return None; }
    let mut late = Vec::new();
    for _ in 0..r.u32()? { late.push((r.str()?, r.u8()?, r.str()?, r.u128()?)); }
    let mut refs = Vec::new();
    for _ in 0..r.u32()? { refs.push((r.u128()?, r.u128()?)); }
    let mut entries = Vec::new();
    for _ in 0..r.u32()? {
        let phase = Phase::of_code(r.u8()?)?;
        let (step, flags, seq) = (r.u8()?, r.u8()?, r.u32()?);
        let group = match r.u8()? {
            0 => GroupAt::Zero,
            1 => GroupAt::At,
            2 => GroupAt::Path(r.str()?, r.u32()?, r.u32()?),
            _ => return None,
        };
        entries.push(Stored { phase, step, flags, seq, group, text: r.str()? });
    }
    r.0.is_empty().then_some(Verdict { late, refs, entries })
}
