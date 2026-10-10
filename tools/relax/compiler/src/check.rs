//! `relax check`: compile without running (rustc `check-pass` / `build-pass`). Every function
//! of the package's workspace crates (every loaded crate whose sources are in the workspace,
//! std excepted) is type- and borrow-checked (generic ones polymorphically, as rustc checks
//! generic bodies once), every non-generic one is compiled to machine code by the run's own
//! per-function compile (`jit::compile_slot`), and so is every instance, closure and glue those
//! reach (rustc's monomorphization collector for `build-pass`), on `RELAX_JOBS` threads. Every
//! failure prints as one line (`file:line:col: error|internal: ..`); `internal` marks a Relax
//! bug (a compiler panic, an error without a user-facing code, or an error inside std or a
//! dependency rustc builds). The exit code is 0 when there are none. `--root-only` and the watch
//! session's deep check (`collect_deep`) cover the root crate (and what it reaches) only.

macro_rules! eprintln {
    ($($arg:tt)*) => { if !crate::diag::enabled() { std::eprintln!($($arg)*); } };
}

use relax_types::solve::SelectionResult;
use crate::jit::{self, FnKey, Unit};
use crate::program::DefKind;

/// Errors of earlier phases (`file:line:col: ..` lines) that belong to the root crate's files.
pub fn own_errors(prog: &crate::program::Program, root: u32, errs: &[String], phase: &'static str) -> Vec<String> {
    let mut paths: Vec<&str> = Vec::new();
    for (i, p) in prog.file_paths.iter().enumerate() {
        if prog.file_crate.get(i).copied() == Some(root) {
            paths.push(p.as_str());
        }
    }
    errs.iter().filter(|e| paths.iter().any(|p| e.starts_with(p))).map(|e| {
        if crate::diag::enabled() { crate::diag::record(e.clone(),crate::diag::from_legacy(e,phase)) }
        else { e.clone() }
    }).collect()
}

/// The crates a one-shot `relax check` covers: the root and every loaded crate whose root file
/// is in the workspace, except std (RELAX_STD may live inside it) and proc-macro crates (their
/// code runs in the macro host, never in the program).
pub fn workspace_crates(prog: &crate::program::Program, root: u32) -> Vec<u32> {
    fn canon(p: &str) -> String {
        std::fs::canonicalize(p).map(|c| c.display().to_string()).unwrap_or_else(|_| p.to_string())
    }
    let ws = format!("{}/", canon(&crate::run::workspace_dir()).trim_end_matches('/'));
    let std_dir = format!("{}/", canon(&crate::std_dir()).trim_end_matches('/'));
    let mut out = Vec::new();
    for (k, c) in prog.crates.iter().enumerate() {
        let path = canon(c.root_path());
        let inside = path.starts_with(&ws) && !path.starts_with(&std_dir);
        if k as u32 == root || (inside && !c.proc_macro && !matches!(prog.syms.str(c.name), "core" | "alloc" | "std" | "proc_macro")) {
            out.push(k as u32);
        }
    }
    out
}

pub fn check_crate(u: &mut Unit, root: u32, errors: Vec<String>, root_only: bool) -> i32 {
    let crates = if root_only { vec![root] } else { workspace_crates(&u.prog, root) };
    check_crate_impl(u, root, &crates, errors, true).0
}

/// The deep check's diagnostics without printing a second stream into a watch response.
pub fn collect_deep(u: &mut Unit, root: u32) -> Vec<crate::diag::Diagnostic> {
    check_crate_impl(u, root, &[root], Vec::new(), false).1
}

fn check_crate_impl(u: &mut Unit, root: u32, crates: &[u32], mut errors: Vec<String>, emit: bool) -> (i32, Vec<crate::diag::Diagnostic>) {
    let t_check = std::time::Instant::now();
    // a constant that cannot be evaluated is one reported failure, not the end of the check
    jit::COMPILE_ERRORS_FATAL.store(false, std::sync::atomic::Ordering::Relaxed);
    crate::layout::set_root_crate(root);
    for &k in crates {
        errors.extend(u.tcx.check_signature_errors(&u.prog, k));
    }
    let mut own = vec![false; u.prog.crates.len()];
    for &k in crates {
        own[k as usize] = true;
    }
    let options = &u.prog.session.clone().options;
    crate::borrowck::lazy::disable_gandalf();
    if options.borrowck_all != crate::options::BorrowckAll::Default {
        // constants the signatures wait for (`[u8; size_of::<T>()]`) are evaluated first, as
        // the run does before it compiles a caller: their items are re-collected with the values
        while u.resolve_const_requests() {}
        let up: *mut Unit = u;
        // SAFETY: as the instance loop below: the unit outlives the call, and constant
        // evaluation (which re-collects waiting items) runs between body checks, never inside one
        let mut resolve = || unsafe { (&mut *up).resolve_const_requests() };
        let n = unsafe { crate::borrowck::check_all(&(*up).prog, &(*up).tcx, options.borrowck_all == crate::options::BorrowckAll::Std, &mut resolve) };
        return (if n == 0 { 0 } else { 1 }, Vec::new());
    }
    let console = crate::gandalf_out::Console::start(emit && crate::diag::enabled(), !emit);
    let mut borrow_diagnostics = Vec::new();
    let up: *mut Unit = u;
    let mut fns = Vec::new();
    for owner in crate::borrowck::body::owners(&u.prog) {
        let d = u.prog.def(owner.owner);
        if !own[d.krate as usize] { continue; }
        let in_trait = u.prog.def(d.parent).kind == DefKind::Trait;
        let generic = u.tcx.fn_sig(&u.prog, owner.owner).map_or(true, |s| s.n_generics > 0);
        // a fn whose where-clauses on concrete types cannot hold (`where &'a mut (): Clone`) is
        // type-checked but never compiled (rustc: impossible predicates are not codegened)
        let impossible = u.tcx.fn_ty_bounds(&u.prog, owner.owner).map_or(false, |bs| {
            bs.iter().any(|(st, td, ta)| u.tcx.tys.is_concrete(*st) && ta.iter().all(|x| u.tcx.tys.is_concrete(*x)) && matches!(u.tcx.select_trait(&crate::tcx::EvalCx::new(&u.prog, crate::tcx::TypingEnv::fully_monomorphized(), &crate::tcx::EvalState::new()), *td, *st, ta), SelectionResult::NoSolution))
        });
        fns.push((owner, generic || in_trait || impossible));
    }
    let n_own = fns.len();
    let mut checked = 0usize;
    // the non-generic fns whose bodies type-check: compiled below, in parallel
    let mut seeds = Vec::new();
    for (owner, generic) in fns {
        let d = owner.owner;
        if owner.kind != crate::borrowck::body::BodyKind::Function {
            let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                let args = owner.identity_args(&u.prog, &u.tcx);
                // as for fn bodies: consts whose values the owner's types wait for (array lengths
                // of foreign consts, `[u8; len(..)]`) are evaluated, then the owner is checked again
                u.resolve_const_requests();
                let mut body = crate::typeck::check_fn(&crate::tcx::EvalCx::new(&u.prog, crate::tcx::TypingEnv::fully_monomorphized(), &crate::tcx::EvalState::new()), &u.prog, &u.tcx, d, &args);
                for _ in 0..4 {
                    if (body.errors.is_empty() && !u.tcx.has_blocked_consts()) || !u.resolve_const_requests() {
                        break;
                    }
                    body = crate::typeck::check_fn(&crate::tcx::EvalCx::new(&u.prog, crate::tcx::TypingEnv::fully_monomorphized(), &crate::tcx::EvalState::new()), &u.prog, &u.tcx, d, &args);
                }
                if !body.errors.is_empty() { return body.errors; }
                if !crate::borrowck::enabled(options) { return Vec::new(); }
                let v = crate::borrowck::check_body(&crate::tcx::EvalCx::new(&u.prog, crate::tcx::TypingEnv::fully_monomorphized(), &crate::tcx::EvalState::new()), &u.prog, &u.tcx, &body);
                crate::borrowck::note_verdict(&v);
                if std::env::var_os("RELAX_BORROWCK_UNCHECKED").is_some() {
                    for x in &v.unchecked { eprintln!("relax-check: borrowck unchecked: {}", x); }
                }
                borrow_diagnostics.extend(crate::borrowck::lazy::report_checked(&u.prog, 0, u.tcx.collect_epoch.load(std::sync::atomic::Ordering::SeqCst), d, &args, v.errors, crate::borrowck::event::Origin::Check).iter().map(|e| e.error.to_diagnostic()));
                Vec::<String>::new()
            }));
            match r {
                Ok(e) => errors.extend(e),
                Err(_) => errors.push(format!("internal compiler error while checking {}", u.prog.def_path(d))),
            }
            continue;
        }
        // generic bodies are checked through their instances (Relax type-checks per instance;
        // a polymorphic check lacks bound-driven lookups); the borrow checker tries the
        // polymorphic body (rustc borrow-checks generic bodies once) when it type-checks
        if generic {
            if crate::borrowck::enabled(options) {
                let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| unsafe {
                    let uu = &mut *up;
                    let args = match crate::borrowck::identity_args(&uu.tcx, &uu.prog, d) {
                        Some(a) => a,
                        None => return Vec::new(),
                    };
                    let body = crate::typeck::check_fn(&crate::tcx::EvalCx::new(&uu.prog, crate::tcx::TypingEnv::fully_monomorphized(), &crate::tcx::EvalState::new()), &uu.prog, &uu.tcx, d, &args);
                    if !body.errors.is_empty() {
                        return Vec::new();
                    }
                    let v = crate::borrowck::check_body(&crate::tcx::EvalCx::new(&uu.prog, crate::tcx::TypingEnv::fully_monomorphized(), &crate::tcx::EvalState::new()), &uu.prog, &uu.tcx, &body);
                    crate::borrowck::note_verdict(&v);
                    borrow_diagnostics.extend(crate::borrowck::lazy::report_checked(&uu.prog, 0, uu.tcx.collect_epoch.load(std::sync::atomic::Ordering::SeqCst), d, &args, v.errors, crate::borrowck::event::Origin::Check).iter().map(|e| e.error.to_diagnostic()));
                    Vec::<String>::new()
                }));
                match r {
                    Ok(e) => errors.extend(e),
                    // the polymorphic body's check panicked: a Relax bug, reported (never dropped)
                    Err(_) => {
                        let def = u.prog.def(d);
                        let pos = u.prog.files[def.file as usize].ast.item(def.item).lo;
                        errors.push(u.prog.record_error(def.file, pos, "borrowck", format!("internal compiler error while borrow-checking {} -- Relax bug, report it{}", u.prog.def_path(d), jit::take_ice_location())));
                    }
                }
            }
            continue;
        }
        let name = u.prog.def_path(d);
        jit::compile_watch(Some((&format!("check typeck {}", name), 0)));
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| unsafe {
            // as a build does: consts that lengths wait for are evaluated (CTFE by running them)
            // and the body is checked again once they are
            (&mut *up).resolve_const_requests();
            let mut errs = { let uu = &mut *up; crate::typeck::check_fn(&crate::tcx::EvalCx::new(&uu.prog, crate::tcx::TypingEnv::fully_monomorphized(), &crate::tcx::EvalState::new()), &uu.prog, &mut uu.tcx, d, &[]).errors };
            for _ in 0..4 {
                if errs.is_empty() || !(&mut *up).resolve_const_requests() {
                    break;
                }
                errs = { let uu = &mut *up; crate::typeck::check_fn(&crate::tcx::EvalCx::new(&uu.prog, crate::tcx::TypingEnv::fully_monomorphized(), &crate::tcx::EvalState::new()), &uu.prog, &mut uu.tcx, d, &[]).errors };
            }
            // the borrow checker on the checked body (plans/relax-borrowck.md)
            if errs.is_empty() && crate::borrowck::enabled(options) {
                let uu = &mut *up;
                let body = crate::typeck::check_fn(&crate::tcx::EvalCx::new(&uu.prog, crate::tcx::TypingEnv::fully_monomorphized(), &crate::tcx::EvalState::new()), &uu.prog, &uu.tcx, d, &[]);
                if body.errors.is_empty() {
                    let v = crate::borrowck::check_body(&crate::tcx::EvalCx::new(&uu.prog, crate::tcx::TypingEnv::fully_monomorphized(), &crate::tcx::EvalState::new()), &uu.prog, &uu.tcx, &body);
                    crate::borrowck::note_verdict(&v);
                    borrow_diagnostics.extend(crate::borrowck::lazy::report_checked(&uu.prog, 0, uu.tcx.collect_epoch.load(std::sync::atomic::Ordering::SeqCst), d, &[], v.errors, crate::borrowck::event::Origin::Check).iter().map(|e| e.error.to_diagnostic()));
                    if std::env::var_os("RELAX_BORROWCK_UNCHECKED").is_some() {
                        for x in v.unchecked {
                            eprintln!("relax-check: borrowck unchecked: {}", x);
                        }
                    }
                }
            }
            errs
        }));
        match r {
            Ok(errs) => {
                if errs.is_empty() {
                    seeds.push(d);
                }
                errors.extend(errs)
            }
            Err(_) => {
                let def = u.prog.def(d);
                let pos = u.prog.files[def.file as usize].ast.item(def.item).lo;
                errors.push(u.prog.record_error(def.file,pos,"typeck",format!("internal compiler error while type-checking {} -- Relax bug, report it",name)));
            },
        }
        checked += 1;
        // the type/borrow check of a whole workspace frees as much as it allocates: return the
        // allocator's free pages as it goes (Stage held 4.6 GB of them at the end of this loop)
        if checked % 20_000 == 0 {
            crate::memstat::trim();
        }
    }
    let t_front = t_check.elapsed();
    // the type/borrow check's freed memory goes back before the compile starts (Stage: 4.6 GB
    // of malloc free pages held after it)
    unsafe {
        let _job = jit::compile_job();
        jit::lock_unit();
        let mut d = jit::settle_drop(up);
        jit::unlock_unit();
        d.release_rir();
    }
    crate::memstat::trim();
    if crate::memstat::enabled() {
        crate::memstat::print("check: type/borrow checked", &crate::memreport::unit_sizes(unsafe { &*up }));
    }
    for e in errors.iter_mut() {
        if is_internal(unsafe { &*up }, &own, e) && !e.contains(": internal:") && !e.starts_with("internal: ") {
            *e = label_internal(e);
        }
    }
    // every seed, and every instance, closure and glue slot the compiled code reaches (generic
    // callees, drop glue, vtable methods, std), compiled to machine code by the run's per-fn
    // compile until no new slots appear
    let failures = unsafe { compile_all(up, &seeds) };
    let n_failed = failures.len();
    // what the builds reported besides their own failures: constants that could not be
    // evaluated (CTFE panics), recorded instead of ending the check
    for e in unsafe { (&(*up).errors).iter().filter(|e| !e.starts_with("compile error in ")).cloned().collect::<Vec<_>>() } {
        errors.push(if is_internal(unsafe { &*up }, &own, &e) { label_internal(&e) } else { e });
    }
    for (id, e) in failures {
        let name = unsafe { (&(*up).fns)[id as usize].name.clone() };
        report(up, id, &name, &e, "compile", &own, &mut errors);
    }
    // RELAX_BORROWCK_INSTANCES=1: every reached instance is borrow-checked too (the background
    // checker's view: concrete type arguments, all crates)
    if crate::borrowck::enabled(options) && options.borrowck_instances {
        for id in 0..unsafe { (&(*up).fns).len() } {
            let key = unsafe { (&(*up).fns)[id].key.clone() };
            let FnKey::Inst(d, args) = key else { continue };
            let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| unsafe {
                let uu = &mut *up;
                let body = crate::typeck::check_fn(&crate::tcx::EvalCx::new(&uu.prog, crate::tcx::TypingEnv::fully_monomorphized(), &crate::tcx::EvalState::new()), &uu.prog, &uu.tcx, d, &args);
                if !body.errors.is_empty() {
                    return;
                }
                let v = crate::borrowck::check_body(&crate::tcx::EvalCx::new(&uu.prog, crate::tcx::TypingEnv::fully_monomorphized(), &crate::tcx::EvalState::new()), &uu.prog, &uu.tcx, &body);
                crate::borrowck::note_verdict(&v);
                borrow_diagnostics.extend(crate::borrowck::lazy::report_checked(&uu.prog, 0, uu.tcx.collect_epoch.load(std::sync::atomic::Ordering::SeqCst), d, &args, v.errors, crate::borrowck::event::Origin::Check).iter().map(|e| e.error.to_diagnostic()));
            }));
            let _ = r;
        }
    }
    let t_compile = t_check.elapsed() - t_front;
    if crate::memstat::enabled() {
        crate::memstat::print("check", &crate::memreport::unit_sizes(unsafe { &*up }));
    }
    eprintln!("relax-check: {} crates checked, {} fns compiled from {} seeds, {} failed builds; type/borrow check {:.1} s, compile {:.1} s", crates.len(), unsafe { (&(*up).fns).len() }, seeds.len(), n_failed, t_front.as_secs_f64(), t_compile.as_secs_f64());
    errors.sort();
    errors.dedup();
    for e in errors.iter().filter(|_| emit) {
        if crate::diag::enabled() {
            crate::diag::emit(&crate::diag::from_legacy(e, "typeck"));
        } else { println!("{}", e); }
    }
    crate::borrowck::finish_check(unsafe { &(*up).prog });
    let borrow_count = console.finish();
    eprintln!("relax-check: {} body owners of the checked crates, {} compiled in all, {} errors", n_own, unsafe { (*up).stats.compiled }, errors.len() + borrow_count);
    {
        let st = unsafe { &(*up).stats };
        eprintln!(
            "relax-check: cpu typeck {} ms, lower {} ms, opt {} ms, codegen {} ms; {} RIR insts, {} KB code",
            st.typeck_ns / 1_000_000,
            st.lower_ns / 1_000_000,
            st.opt_ns / 1_000_000,
            st.codegen_ns / 1_000_000,
            st.rir_insts,
            st.code_bytes / 1024
        );
        eprintln!("relax-check: constant initializers: {} evaluated to data, {} compiled and run; evaluation cpu {:.1} ms", st.ctfe_data, st.ctfe_code, st.ctfe_ns as f64 / 1e6);
    }
    {
        let n = crate::jit::NESTED_AT_YIELD.load(std::sync::atomic::Ordering::Relaxed);
        if n != 0 {
            eprintln!("relax-check: UNBALANCED unit lock in O3 jobs: {} nested at a yield, {} left held", n & 0xffff_ffff, n >> 32);
        }
    }
    unsafe { crate::jit::backend_bench(up) };
    if std::env::var("RELAX_PASS_TIMES").is_ok() || std::env::var("RELAX_OPT_HIST").is_ok() {
        let mut passes = String::new();
        for i in 0..crate::opt::PASS_NAMES.len() {
            passes.push_str(&format!("{} {:.0}  ", crate::opt::PASS_NAMES[i], crate::opt::PASS_NS[i].load(std::sync::atomic::Ordering::Relaxed) as f64 / 1e6));
        }
        eprintln!("relax-check: passes (cpu ms): {}", passes);
        eprintln!("relax-check: opt ms by size (<16,<64,<256,<1k,<4k,more) {:?} fns {:?}", crate::opt::HIST[..6].iter().map(|x| x.load(std::sync::atomic::Ordering::Relaxed) / 1_000_000).collect::<Vec<_>>(), crate::opt::HIST[6..].iter().map(|x| x.load(std::sync::atomic::Ordering::Relaxed)).collect::<Vec<_>>());
    }
    let _ = checked;
    crate::relaxed::finish_check();
    let mut diagnostics: Vec<_> = errors.iter().map(|e| crate::diag::from_legacy(e, "typeck")).collect();
    diagnostics.extend(borrow_diagnostics);
    (i32::from(!errors.is_empty() || borrow_count != 0), diagnostics)
}

/// Compiles every seed fn, then every slot the compiled code creates (callees, closures, glue,
/// vtable methods), each through the run's own per-fn compile (`jit::compile_slot`: front end
/// under the unit lock, optimisation and code generation off it), on RELAX_JOBS threads until
/// no slot is left. Returns every failed build: (slot, error).
unsafe fn compile_all(up: *mut Unit, seeds: &[crate::program::DefId]) -> Vec<(u32, String)> {
    use std::sync::atomic::{AtomicUsize, Ordering};
    *jit::CHECK_FAILURES.lock().unwrap_or_else(|p| p.into_inner()) = Some(Vec::new());
    // as a run: the front end under the unit lock, optimisation and code generation off it
    // (and the run's speculative callee builds)
    jit::enable_pipelining(&(*up).prog.session.clone().options);
    // (slots made before the seeds -- the root's main, constants' readers -- are compiled too)
    jit::lock_unit();
    for &d in seeds {
        (&mut *up).fn_id(FnKey::Inst(d, Vec::new()));
    }
    jit::unlock_unit();
    // every in-flight build holds its front end's and back end's state: at most 8 by default
    let jobs = std::env::var("RELAX_JOBS").ok().and_then(|v| v.parse::<usize>().ok()).filter(|n| *n > 0)
        .unwrap_or_else(|| std::thread::available_parallelism().map_or(4, |n| n.get()).min(8));
    // the run's reclamation (jit::settle_drop: RIR, checked bodies, templates of compiled
    // slots) once the process grew SETTLE_GROWTH since the last one (looked at every 2,000
    // compiled slots), so a whole-program check keeps the working set of a run, not every body
    // it ever built (Stage went past 18 GB without it). Dropped RIR is rebuilt for inlining:
    // settling every 20,000 slots made Scope's compile 4x slower.
    const SETTLE_GROWTH: u64 = 3 << 30;
    let compiled = AtomicUsize::new(0);
    let settled_at = AtomicUsize::new(0);
    let settled_rss = std::sync::atomic::AtomicU64::new(crate::memstat::process_rss().0 as u64);
    let next = AtomicUsize::new(0);
    let active = AtomicUsize::new(0);
    let panics: std::sync::Mutex<Vec<(u32, String)>> = std::sync::Mutex::new(Vec::new());
    let upn = up as usize;
    std::thread::scope(|sc| {
        for w in 0..jobs {
            let (next, active, panics, compiled, settled_at, settled_rss) = (&next, &active, &panics, &compiled, &settled_at, &settled_rss);
            std::thread::Builder::new().name(format!("relax-check-{}", w)).stack_size(256 << 20).spawn_scoped(sc, move || {
                let up = upn as *mut Unit;
                loop {
                    // the next slot not compiled yet; done when none is left and no worker is
                    // compiling (a compile in flight may still make new slots)
                    active.fetch_add(1, Ordering::SeqCst);
                    let pick = {
                        let _job = jit::compile_job();
                        jit::lock_unit();
                        let n = (&(*up).fns).len();
                        let mut pick = None;
                        loop {
                            let i = next.load(Ordering::SeqCst);
                            if i >= n { break; }
                            if next.compare_exchange(i, i + 1, Ordering::SeqCst, Ordering::SeqCst).is_ok() {
                                let f = &(&(*up).fns)[i];
                                if !f.compiled {
                                    pick = Some(i as u32);
                                    break;
                                }
                            }
                        }
                        jit::unlock_unit();
                        pick
                    };
                    let Some(id) = pick else {
                        active.fetch_sub(1, Ordering::SeqCst);
                        if active.load(Ordering::SeqCst) == 0 && next.load(Ordering::SeqCst) >= { jit::lock_unit(); let n = (&(*up).fns).len(); jit::unlock_unit(); n } {
                            break;
                        }
                        std::thread::sleep(std::time::Duration::from_millis(2));
                        continue;
                    };
                    let depth = jit::lock_depth();
                    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| jit::compile_slot(up, id)));
                    if let Err(p) = r {
                        jit::unlock_to(depth);
                        let msg = p.downcast_ref::<&str>().map(|s| s.to_string()).or_else(|| p.downcast_ref::<String>().cloned()).unwrap_or_else(|| "panic".into());
                        panics.lock().unwrap().push((id, format!("internal compiler error: {}{}", msg, jit::take_ice_location())));
                    }
                    active.fetch_sub(1, Ordering::SeqCst);
                    let n = compiled.fetch_add(1, Ordering::Relaxed) + 1;
                    let at = settled_at.load(Ordering::Relaxed);
                    if n >= at + 2_000 && settled_at.compare_exchange(at, n, Ordering::AcqRel, Ordering::Relaxed).is_ok()
                        && crate::memstat::process_rss().0 as u64 > settled_rss.load(Ordering::Relaxed) + SETTLE_GROWTH {
                        let _job = jit::compile_job();
                        jit::lock_unit();
                        let mut d = jit::settle_drop(up);
                        jit::unlock_unit();
                        d.release_rir();
                        crate::memstat::trim();
                        settled_rss.store(crate::memstat::process_rss().0 as u64, Ordering::Relaxed);
                    }
                }
            }).expect("check worker");
        }
    });
    let mut out = jit::CHECK_FAILURES.lock().unwrap_or_else(|p| p.into_inner()).take().unwrap_or_default();
    out.extend(panics.into_inner().unwrap());
    out
}

/// Is a failure a Relax bug rather than an error rustc would report? A compiler panic, an
/// internal error, an error without an error code, or one located outside the checked crates
/// (std or a dependency: rustc builds those).
fn is_internal(u: &Unit, own: &[bool], e: &str) -> bool {
    let first = e.lines().next().unwrap_or("");
    if first.contains("internal compiler error") || first.contains("internal:") || first.contains("Relax bug") {
        return true;
    }
    // `path:line:col: E0123: ..`
    let mut it = first.splitn(4, ':');
    let (Some(path), Some(l), Some(c), Some(rest)) = (it.next(), it.next(), it.next(), it.next()) else { return true };
    if l.trim().parse::<u32>().is_err() || c.trim().parse::<u32>().is_err() {
        return true;
    }
    let rest = rest.trim_start();
    let coded = rest.len() > 5 && rest.starts_with('E') && rest[1..5].bytes().all(|b| b.is_ascii_digit());
    if !coded {
        return true;
    }
    match u.prog.file_paths.iter().position(|p| p == path) {
        Some(i) => !u.prog.file_crate.get(i).is_some_and(|k| own.get(*k as usize).copied().unwrap_or(false)),
        None => true,
    }
}

/// `path:line:col: internal: msg` for a Relax bug (the error keeps its own text otherwise).
fn label_internal(e: &str) -> String {
    let mut it = e.splitn(4, ':');
    if let (Some(p), Some(l), Some(c), Some(rest)) = (it.next(), it.next(), it.next(), it.next()) {
        if l.trim().parse::<u32>().is_ok() && c.trim().parse::<u32>().is_ok() {
            return format!("{}:{}:{}: internal:{}", p, l, c, rest);
        }
    }
    format!("internal: {}", e)
}

/// One failed build as an error line: its location (the error's own, else the fn's), the
/// message's first line, the instance it failed for, and `internal` for a Relax bug.
fn report(up: *mut Unit, id: u32, name: &str, e: &str, phase: &'static str, own: &[bool], errors: &mut Vec<String>) {
    let u = unsafe { &*up };
    let mut first = e.lines().next().unwrap_or("").to_string();
    // an error without a location takes its fn's
    let located = {
        let mut it = first.splitn(4, ':');
        matches!((it.next(), it.next(), it.next()), (Some(_), Some(l), Some(c)) if l.trim().parse::<u32>().is_ok() && c.trim().parse::<u32>().is_ok())
    };
    if !located {
        if let Some((file, pos)) = function_origin(u, id) {
            let path = &u.prog.file_paths[file as usize];
            let (l, c) = crate::lexer::line_col(&u.prog.files[file as usize].src, pos);
            first = format!("{}:{}:{}: {}", path, l, c, first);
        }
    }
    let internal = is_internal(u, own, &first);
    // the type check of the fn reported it already (a non-generic body checked before compiling)
    let shown = if internal { label_internal(&first) } else { first.clone() };
    if errors.iter().any(|x| *x == shown) {
        return;
    }
    let mut n = name.to_string();
    if let crate::jit::FnKey::Inst(_, args) = &u.fns[id as usize].key {
        if !args.is_empty() && !n.contains('<') {
            let a: Vec<String> = args.iter().map(|t| crate::typeck::ty_to_string(false, &u.prog, &u.tcx, *t)).collect();
            n = format!("{}<{}>", n, a.join(", "));
        }
    }
    let line = format!("{} [in {}]", shown, n);
    if crate::diag::enabled() {
        let mut d = crate::diag::recorded(e).or_else(|| crate::diag::recorded(&first)).unwrap_or_else(|| crate::diag::from_legacy(&first, phase));
        d.notes.push(format!("in {}", n));
        if internal { d.notes.push("internal: a Relax bug, not an error in the program".to_string()); }
        crate::diag::record(line.clone(), d);
    }
    errors.push(line);
}

fn function_origin(u: &Unit, mut id: u32) -> Option<(u32,u32)> {
    for _ in 0..64 {
        match &u.fns[id as usize].key {
            FnKey::Inst(d,_) => { let d = u.prog.def(*d); return Some((d.file,u.prog.files[d.file as usize].ast.item(d.item).lo)); }
            FnKey::Closure(f,e,_) => return Some((*f,u.prog.files[*f as usize].ast.expr(crate::ast::ExprId(*e)).lo)),
            FnKey::Sandbox(parent) => id = *parent,
            FnKey::Glue(_,t) => {
                if let crate::types::TyKind::Adt(d,_, _) = u.tcx.tys.kind(*t) {
                    let d = u.prog.def(*d); return Some((d.file,u.prog.files[d.file as usize].ast.item(d.item).lo));
                }
                return None;
            }
        }
    }
    None
}
