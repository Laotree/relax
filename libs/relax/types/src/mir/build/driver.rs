//! The MIR-building harness behind `MAKEPAD_RUN_MIR_BUILD_ALL=1 makepad check <pkg>`: build the MIR of every body
//! owner (fns, consts, statics, anonymous consts, closures and async blocks), run `mir::validate` on each result
//! and print a per-reason histogram of the bodies that could not be built or do not validate.
//!
//! `MAKEPAD_RUN_MIR_BUILD_ALL=std` includes the standard library crates, `MAKEPAD_RUN_MIR_BUILD_ONLY=<substr>`
//! restricts the owners to those whose path contains the substring, and `MAKEPAD_RUN_MIR_BUILD_DUMP=<substr>`
//! prints the pretty MIR (`mir::pretty`) of each built body whose path contains the substring.
use super::{build_mir, BuildCx, BuildRoot, UnsupportedReason};
use crate::ast::{ExprId, ExprKind};
use crate::borrowck::body::{self, BodyKind, CheckedBody};
use crate::program::Program;
use crate::tcx::{EvalCx, EvalState, RecursionLimit, Tcx, TypingEnv, TypingMode};
use crate::typeck;
use std::collections::BTreeMap;

/// The closure-like children of a typeck root: closures and async blocks whose expression facts this root owns.
pub fn closure_children(prog: &Program, tcx: &Tcx, body: &typeck::Body) -> Vec<CheckedBody> {
    let ast = &prog.files[body.file as usize].ast;
    let mut out = Vec::new();
    for i in 0..body.expr_ty.len() {
        if body.expr_ty[i] == tcx.tys.error {
            continue;
        }
        let e = ExprId(if i < body.expr_n1 as usize { body.expr_lo + i as u32 } else { body.expr_lo2 + i as u32 - body.expr_n1 });
        match ast.expr(e).kind {
            ExprKind::Closure(_) => out.push(CheckedBody { owner: body.def, kind: BodyKind::Closure(e) }),
            // Async blocks and an async closure's coroutine are bodies of their own.
            ExprKind::Async(..) => out.push(CheckedBody { owner: body.def, kind: BodyKind::Closure(e) }),
            _ => {}
        }
    }
    out
}

fn line_of(prog: &Program, file: u32, pos: u32) -> usize {
    let src = prog.src(file).src;
    1 + src[..(pos as usize).min(src.len())].iter().filter(|&&c| c == b'\n').count()
}

#[derive(Default)]
struct Histogram {
    counts: BTreeMap<String, usize>,
    example: BTreeMap<String, String>,
}
impl Histogram {
    fn note(&mut self, reason: String, at: String) {
        *self.counts.entry(reason.clone()).or_insert(0) += 1;
        self.example.entry(reason).or_insert(at);
    }
}

fn reason_key(reason: &UnsupportedReason) -> String {
    match reason {
        UnsupportedReason::NotYetBuilt(what) => format!("not yet built: {what}"),
        UnsupportedReason::Internal(what) => format!("internal: {what}"),
        UnsupportedReason::UnresolvedFact(what) => format!("unresolved fact: {what}"),
        other => format!("{other:?}"),
    }
}

/// Build and validate every body. Returns the number of bodies that panicked or did not validate (the gate);
/// unbuilt bodies are counted per reason and are not failures.
pub fn build_all(prog: &Program, tcx: &Tcx, with_std: bool) -> usize {
    let only = std::env::var("MAKEPAD_RUN_MIR_BUILD_ONLY").ok();
    let dump: Vec<String> = std::env::var("MAKEPAD_RUN_MIR_BUILD_DUMP").map(|s| s.split(',').map(str::to_string).collect()).unwrap_or_default();
    let std_crates: Vec<u32> = ["core", "alloc", "std"].iter().filter_map(|n| prog.crates.iter().position(|c| prog.syms.str(c.name) == *n).map(|i| i as u32)).collect();
    let (mut owners, mut typeck_fail, mut built, mut validate_fail, mut panics) = (0usize, 0usize, 0usize, 0usize, 0usize);
    let mut unbuilt = Histogram::default();
    let mut invalid = Histogram::default();
    let mut panicked = Histogram::default();
    let mut by_kind: BTreeMap<&'static str, (usize, usize)> = BTreeMap::new();
    let t0 = crate::clock::cpu_ns();
    for owner in body::owners(prog) {
        let d = prog.def(owner.owner);
        if !with_std && std_crates.contains(&d.krate) {
            continue;
        }
        let path = prog.def_path(owner.owner);
        if let Some(o) = &only {
            if !path.contains(o.as_str()) {
                continue;
            }
        }
        owners += 1;
        let typeck_body = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| tcx.typeck(prog, owner.owner)));
        let typeck_body = match typeck_body {
            Ok(b) if b.errors.is_empty() => b,
            _ => {
                typeck_fail += 1;
                continue;
            }
        };
        let env = TypingEnv {
            limit: RecursionLimit::for_item(prog, typeck_body.def),
            param_env: typeck_body.param_env.unwrap_or_default(),
            mode: TypingMode::borrowck(tcx, prog, typeck_body.def),
        };
        let state = EvalState::new();
        let eval = EvalCx::new(prog, tcx, env, &state);
        let root = match BuildRoot::new(BuildCx { prog, tcx, env, eval: &eval }, &typeck_body) {
            Ok(root) => root,
            Err(why) => {
                unbuilt.note(format!("no region scope tree: {why}"), path);
                continue;
            }
        };
        let mut bodies = vec![owner];
        bodies.extend(body::const_children(prog, tcx, &typeck_body));
        bodies.extend(closure_children(prog, tcx, &typeck_body));
        for b in bodies {
            let kind = super::owner_kind_name(b.kind);
            let slot = by_kind.entry(kind).or_insert((0, 0));
            slot.0 += 1;
            let mut loc = String::new();
            let at = if let BodyKind::Closure(e) = b.kind {
                let lo = prog.files[typeck_body.file as usize].ast.expr(e).lo;
                loc = format!(" ({}:{})", prog.file_paths[typeck_body.file as usize], line_of(prog, typeck_body.file, lo));
                format!("{path}::{{closure#{}}}", e.0)
            } else {
                path.clone()
            };
            match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| build_mir(&root, b))) {
                Ok(Ok(mir)) => {
                    built += 1;
                    slot.1 += 1;
                    if dump.iter().any(|s| at.contains(s.as_str())) {
                        println!("{}", crate::mir::pretty::print_body(prog, tcx, &at, &mir));
                    }
                    let errors = crate::mir::validate::validate(&mir, tcx);
                    if let Some(first) = errors.first() {
                        validate_fail += 1;
                        invalid.note(format!("{} (bb{:?} stmt{:?})", first.message, first.bb.map(|b| b.0), first.statement_index), format!("{at}{loc}"));
                    }
                }
                Ok(Err(err)) => {
                    let line = line_of(prog, err.span.file, err.span.lo);
                    unbuilt.note(reason_key(&err.reason), format!("{at}{loc} @ {}:{line}", prog.file_paths[err.span.file as usize]))
                }
                Err(p) => {
                    if crate::preempt::is_cancelled(&*p) {
                        std::panic::resume_unwind(p);
                    }
                    panics += 1;
                    let msg = p.downcast_ref::<String>().cloned().or_else(|| p.downcast_ref::<&str>().map(|s| s.to_string())).unwrap_or_else(|| "panic".into());
                    let (key, detail) = match msg.split_once(": ") { Some((k, v)) => (k.to_string(), format!(" [{v}]")), None => (msg.clone(), String::new()) };
                    panicked.note(key, format!("{at}{loc}{detail}"));
                }
            }
        }
    }
    eprintln!(
        "makepad-run mir-build: {owners} owners ({typeck_fail} failed typeck), {built} bodies built, {validate_fail} failed validation, {panics} panicked, {} not built; cpu {:.1} ms",
        unbuilt.counts.values().sum::<usize>(),
        (crate::clock::cpu_ns() - t0) as f64 / 1e6
    );
    for (kind, (all, ok)) in &by_kind {
        eprintln!("makepad-run mir-build: {kind:>12}: {ok}/{all} built");
    }
    for (title, h) in [("not built", &unbuilt), ("INVALID", &invalid), ("PANIC", &panicked)] {
        let mut rows: Vec<_> = h.counts.iter().collect();
        rows.sort_by(|a, b| b.1.cmp(a.1));
        for (reason, n) in rows {
            eprintln!("makepad-run mir-build: {title} {n:>6}  {reason}   e.g. {}", h.example.get(reason).map_or("", |s| s.as_str()));
        }
    }
    validate_fail + panics
}
