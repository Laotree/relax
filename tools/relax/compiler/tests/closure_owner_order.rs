//! Run with RELAX_STD=$PWD/std RELAX_CACHE=off cargo test --release --offline --test closure_owner_order.
//! The fixture also runs with `relax test tests/closure_owner/main.rs`.
use relax_compiler::{program::{DefId, Program}, tcx::{EvalCx, EvalState, Tcx, TypingEnv}, typeck, types::TyKind};

fn named(prog: &Program, name: &str) -> DefId {
    (0..prog.defs.len()).map(|i| DefId(i as u32)).find(|&d| prog.name(d) == name).unwrap()
}

#[test]
fn consumer_before_capture_owner() {
    let session = std::sync::Arc::new(relax_compiler::Session::default());
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/closure_owner/main.rs");
    let (prog, _, _) = relax_compiler::load_with_std(&session, path, "closure_owner", true).unwrap();
    let mut tcx = Tcx::new();
    tcx.collect(&prog);
    tcx.impl_projection_ready = true;
    assert!(tcx.errors.is_empty(), "{:?}", tcx.errors);
    let state = EvalState::new();
    let cx = EvalCx::new(&prog, TypingEnv::fully_monomorphized(), &state);
    use relax_compiler::upvar::ClosureKind::{Fn, FnMut, FnOnce};
    for (name, wrapper, kind) in [("foreign_file", "wrap", Fn), ("same_file", "wrap", Fn), ("mutable", "wrap_mut", FnMut), ("consuming", "wrap_once", FnOnce)] {
        // Obtain the closure's type as it would arrive from another checked/cached
        // body, then discard published capture results to force consumer-first order.
        let owner = typeck::check_fn(&cx, &prog, &tcx, named(&prog, name), &[]);
        assert!(owner.errors.is_empty(), "{:?}", owner.errors);
        let closure = owner.ty(relax_compiler::ast::ExprId(owner.closures[0]));
        assert!(matches!(tcx.tys.kind(closure), TyKind::Closure(..)));
        tcx.closure_capture_types.clear();
        let consumer = typeck::check_fn(&cx, &prog, &tcx, named(&prog, wrapper), &[closure]);
        assert!(consumer.errors.is_empty(), "{name}: {:?}", consumer.errors);
        assert_eq!(consumer.min_captures.len(), 1);
        assert_eq!(consumer.min_captures.values().next().unwrap().kind, kind);
    }
}
