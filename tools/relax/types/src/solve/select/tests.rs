use crate::solve::SelectionResult;
use super::*;
use crate::program::Program;
use crate::tcx::{EvalState, ParamEnv, TypingEnv};
use crate::solve::infer::Inference;
use crate::solve::relate::TypeRelation;

fn program(source: &[u8]) -> (Program, Tcx) {
    let dir = std::env::temp_dir().join(format!("relax-selection-{}-{}", std::process::id(), std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos()));
    std::fs::create_dir(&dir).unwrap();
    let path = dir.join("lib.rs");
    std::fs::write(&path, source).unwrap();
    let mut prog = Program::new(&std::sync::Arc::new(crate::Session::default()));
    prog.load_crate("typing", path.to_str().unwrap(), 2021, crate::cfg::CfgSet::host(&prog.session, &[]), Vec::new()).unwrap();
    let mut tcx = Tcx::new();
    tcx.collect(&prog);
    tcx.impl_projection_ready = true;
    std::fs::remove_file(&path).unwrap();
    std::fs::remove_dir(&dir).unwrap();
    assert!(tcx.errors.is_empty(), "{:?}", tcx.errors);
    (prog, tcx)
}

fn named(prog: &Program, name: &str) -> DefId {
    for (i, _) in prog.defs.iter().enumerate() {
        let d = DefId(i as u32);
        if prog.name(d) == name { return d; }
    }
    panic!("missing {name}")
}


fn pred(def: DefId, ty: TyId, args: &[TyId]) -> TraitPredicate {
    let mut all = vec![ty]; all.extend_from_slice(args);
    TraitPredicate { trait_ref: TraitRef { def, args: all }, polarity: PredicatePolarity::Positive }
}
fn adt(tcx: &Tcx, prog: &Program, name: &str, args: Vec<TyId>) -> TyId {
    tcx.tys.intern(TyKind::Adt(named(prog, name), args, RegionArgsId::EMPTY))
}

#[test]
fn fn_header_candidates_stay_distinct() {
    let (prog, tcx) = program(br#"#![no_std]
        trait Marker {}
        impl Marker for fn() {}
        impl Marker for unsafe fn() {}
        impl Marker for extern "C" fn() {}
        impl Marker for unsafe extern "C" fn(u32) {}
        impl Marker for unsafe extern "C" fn(u32, ...) {}
        fn inputs(a: fn(), b: unsafe fn(), c: extern "C" fn(),
            d: unsafe extern "C" fn(u32), e: unsafe extern "C" fn(u32, ...)) {}
    "#);
    let state = EvalState::new();
    let cx = EvalCx::new(&prog, TypingEnv::fully_monomorphized(), &state);
    let mut infcx = Inference::new(&tcx.tys);
    let inputs = &tcx.fn_item_sig(&prog, named(&prog, "inputs")).unwrap().params;
    let mut sources = Vec::new();
    for &ty in inputs {
        let SelectionResult::Ok(s) = select(&tcx, &cx, &mut infcx, pred(named(&prog, "Marker"), ty, &[])) else { panic!("no unique header candidate") };
        assert!(!sources.contains(&s.source));
        sources.push(s.source);
    }
    assert_eq!(sources.len(), 5);
}

#[test]
fn fn_header_trait_argument_is_related() {
    let (prog, tcx) = program(br#"#![no_std]
        trait Marker<T> {}
        impl Marker<fn()> for bool {}
        impl Marker<unsafe fn()> for bool {}
        fn inputs(a: fn(), b: unsafe fn()) {}
    "#);
    let state = EvalState::new();
    let cx = EvalCx::new(&prog, TypingEnv::fully_monomorphized(), &state);
    let mut infcx = Inference::new(&tcx.tys);
    let inputs = &tcx.fn_item_sig(&prog, named(&prog, "inputs")).unwrap().params;
    let SelectionResult::Ok(a) = select(&tcx, &cx, &mut infcx, pred(named(&prog, "Marker"), tcx.tys.bool_, &[inputs[0]])) else { panic!() };
    let SelectionResult::Ok(b) = select(&tcx, &cx, &mut infcx, pred(named(&prog, "Marker"), tcx.tys.bool_, &[inputs[1]])) else { panic!() };
    assert_ne!(a.source, b.source);
}

#[test]
fn two_impls_are_ambiguous() {
    let (prog, tcx) = program(b"#![no_std] trait Tr {} impl Tr for bool {} impl Tr for bool {}");
    let state = EvalState::new();
    let cx = EvalCx::new(&prog, TypingEnv::fully_monomorphized(), &state);
    let mut infcx = Inference::new(&tcx.tys);
    assert!(matches!(select(&tcx, &cx, &mut infcx, pred(named(&prog, "Tr"), tcx.tys.bool_, &[])), SelectionResult::Ambiguous(MaybeCause::Ambiguity)));
}

#[test]
fn inference_self_stalls_without_binding() {
    let (prog, tcx) = program(b"#![no_std] trait Tr {} impl Tr for bool {}");
    let state = EvalState::new();
    let cx = EvalCx::new(&prog, TypingEnv::fully_monomorphized(), &state);
    let mut infcx = Inference::new(&tcx.tys);
    let ty = infcx.fresh_ty(TyVariableKind::General);
    assert!(matches!(select(&tcx, &cx, &mut infcx, pred(named(&prog, "Tr"), ty, &[])), SelectionResult::Ambiguous(_)));
    assert_eq!(infcx.resolve_ty(ty), ty);
}

#[test]
fn param_environment_precedes_blanket_impl() {
    let (prog, tcx) = program(b"#![no_std] trait Tr {} impl<T> Tr for T {}");
    let tr = named(&prog, "Tr");
    let ty = tcx.tys.intern(TyKind::Param(0));
    let mut env = ParamEnv::default(); env.preds.push((ty, tr, Vec::new()));
    let state = EvalState::new();
    let cx = EvalCx::new(&prog, TypingEnv { param_env: tcx.intern_param_env(env), ..TypingEnv::fully_monomorphized() }, &state);
    let mut infcx = Inference::new(&tcx.tys);
    let SelectionResult::Ok(s) = select(&tcx, &cx, &mut infcx, pred(tr, ty, &[])) else { panic!() };
    assert_eq!(s.source, CandidateSource::ParamEnv(0));
}

#[test]
fn nested_failure_is_returned_then_evaluated() {
    let (prog, tcx) = program(b"#![no_std] trait Tr {} trait Bound {} struct W<T>(T); impl<T: Bound> Tr for W<T> {}");
    let ty = adt(&tcx, &prog, "W", vec![tcx.tys.bool_]);
    let tr = named(&prog, "Tr");
    let state = EvalState::new();
    let cx = EvalCx::new(&prog, TypingEnv::fully_monomorphized(), &state);
    let mut infcx = Inference::new(&tcx.tys);
    let SelectionResult::Ok(s) = select(&tcx, &cx, &mut infcx, pred(tr, ty, &[])) else { panic!() };
    assert!(!s.nested.is_empty());
    assert_eq!(evaluate(&tcx, &cx, &mut infcx, trait_goal(&cx, tr, ty, &[])), Err(NoSolution));
}

#[test]
fn composite_where_clause_is_not_lost() {
    let (prog, tcx) = program(b"#![no_std] trait Tr {} trait Bound {} struct W<T>(T); struct Q<T>(T); impl<T> Tr for W<T> where Q<T>: Bound {}");
    let ty = adt(&tcx, &prog, "W", vec![tcx.tys.bool_]);
    let state = EvalState::new();
    let cx = EvalCx::new(&prog, TypingEnv::fully_monomorphized(), &state);
    let mut infcx = Inference::new(&tcx.tys);
    assert_eq!(evaluate(&tcx, &cx, &mut infcx, trait_goal(&cx, named(&prog, "Tr"), ty, &[])), Err(NoSolution));
}

#[test]
fn nested_failure_winnows_overlapping_headers() {
    let (prog, tcx) = program(b"#![no_std] trait Tr {} trait Bound {} struct W<T>(T); impl<T: Bound> Tr for W<T> {} impl Tr for W<bool> {}");
    let ty = adt(&tcx, &prog, "W", vec![tcx.tys.bool_]);
    let state = EvalState::new();
    let cx = EvalCx::new(&prog, TypingEnv::fully_monomorphized(), &state);
    let mut infcx = Inference::new(&tcx.tys);
    let SelectionResult::Ok(s) = select(&tcx, &cx, &mut infcx, pred(named(&prog, "Tr"), ty, &[])) else { panic!() };
    assert!(s.args.is_empty());
}

#[test]
fn auto_trait_cycle_is_coinductive() {
    let (prog, tcx) = program(b"#![no_std] auto trait Auto {} struct Node { next: *const Node }");
    let ty = adt(&tcx, &prog, "Node", Vec::new());
    let state = EvalState::new();
    let cx = EvalCx::new(&prog, TypingEnv::fully_monomorphized(), &state);
    let mut infcx = Inference::new(&tcx.tys);
    assert_eq!(evaluate(&tcx, &cx, &mut infcx, trait_goal(&cx, named(&prog, "Auto"), ty, &[])), Ok(Certainty::Yes));
}

#[test]
fn closure_auto_traits_wait_for_minimum_capture_types() {
    let (prog, tcx) = program(b"#![no_std] auto trait Auto {} struct NotAuto; impl !Auto for NotAuto {}");
    let state = EvalState::new();
    let cx = EvalCx::new(&prog, TypingEnv::fully_monomorphized(), &state);
    let mut infcx = Inference::new(&tcx.tys);
    let sig = tcx.tys.intern(TyKind::FnPtr(vec![], tcx.tys.unit, crate::types::FnHeader::RUST, 0));
    let root = adt(&tcx, &prog, "NotAuto", vec![]);
    let ty = tcx.tys.intern(TyKind::Closure(0, 0, sig, root, tcx.tys.unit));
    let goal = trait_goal(&cx, named(&prog, "Auto"), ty, &[]);
    assert!(matches!(select(&tcx, &cx, &mut infcx, pred(named(&prog, "Auto"), ty, &[])), SelectionResult::Ambiguous(_)));
    assert_eq!(evaluate(&tcx, &cx, &mut infcx, goal.clone()), Ok(Certainty::Maybe(MaybeCause::Ambiguity)));
    let key = (0, 0, tcx.tys.unit, tcx.collect_epoch.load(std::sync::atomic::Ordering::Relaxed));
    let upvar = infcx.fresh_ty(TyVariableKind::General);
    tcx.closure_capture_types.insert(key, crate::upvar::ClosureCaptureTypes {
        kind: crate::upvar::ClosureKind::Fn, is_copy: false,
        upvars: tcx.tys.intern(TyKind::Tuple(vec![upvar])),
    });
    assert_eq!(evaluate(&tcx, &cx, &mut infcx, goal.clone()), Ok(Certainty::Maybe(MaybeCause::Ambiguity)));
    assert!(infcx.relate(upvar, tcx.tys.bool_));
    assert_eq!(evaluate(&tcx, &cx, &mut infcx, goal.clone()), Ok(Certainty::Yes));
    tcx.closure_capture_types.insert(key, crate::upvar::ClosureCaptureTypes {
        kind: crate::upvar::ClosureKind::Fn, is_copy: false,
        upvars: tcx.tys.intern(TyKind::Tuple(vec![root])),
    });
    assert_eq!(evaluate(&tcx, &cx, &mut infcx, goal.clone()), Err(NoSolution));
}

#[test]
fn coroutine_auto_traits_use_published_upvars_until_arch_scope() {
    let (prog, tcx) = program(b"#![no_std] auto trait Auto {} struct NotAuto; impl !Auto for NotAuto {}");
    let state = EvalState::new();
    let cx = EvalCx::new(&prog, TypingEnv::fully_monomorphized(), &state);
    let mut infcx = Inference::new(&tcx.tys);
    let sig = tcx.tys.intern(TyKind::FnPtr(vec![], tcx.tys.unit, crate::types::FnHeader::RUST, 0));
    let ty = tcx.tys.intern(TyKind::Closure(0, 0, sig, tcx.tys.unit, tcx.tys.unit));
    tcx.coroutines.insert((0, 0), ());
    let goal = trait_goal(&cx, named(&prog, "Auto"), ty, &[]);
    let key = (0, 0, tcx.tys.unit, tcx.collect_epoch.load(std::sync::atomic::Ordering::Relaxed));
    assert_eq!(evaluate(&tcx, &cx, &mut infcx, goal.clone()), Ok(Certainty::Maybe(MaybeCause::Ambiguity)));
    tcx.closure_capture_types.insert(key, crate::upvar::ClosureCaptureTypes {
        kind: crate::upvar::ClosureKind::FnOnce, is_copy: false, upvars: tcx.tys.unit,
    });
    assert_eq!(evaluate(&tcx, &cx, &mut infcx, goal.clone()), Ok(Certainty::Yes));
    tcx.closure_capture_types.insert(key, crate::upvar::ClosureCaptureTypes {
        kind: crate::upvar::ClosureKind::FnOnce, is_copy: false,
        upvars: tcx.tys.intern(TyKind::Tuple(vec![adt(&tcx, &prog, "NotAuto", vec![])])),
    });
    assert_eq!(evaluate(&tcx, &cx, &mut infcx, goal), Err(NoSolution));
}

#[test]
fn ordinary_trait_cycle_has_no_solution() {
    let (prog, tcx) = program(b"#![no_std] trait Tr {} impl<T: Tr> Tr for T {}");
    let state = EvalState::new();
    let cx = EvalCx::new(&prog, TypingEnv::fully_monomorphized(), &state);
    let mut infcx = Inference::new(&tcx.tys);
    assert_eq!(evaluate(&tcx, &cx, &mut infcx, trait_goal(&cx, named(&prog, "Tr"), tcx.tys.bool_, &[])), Err(NoSolution));
}

#[test]
fn overflow_is_ambiguity() {
    let (prog, tcx) = program(b"#![no_std] trait Tr {} struct W<T>(T); impl<T> Tr for T where W<T>: Tr {}");
    let state = EvalState::new();
    let cx = EvalCx::new(&prog, TypingEnv::fully_monomorphized(), &state);
    let mut infcx = Inference::new(&tcx.tys);
    let mut ecx = Evaluation::new(&tcx, &cx, &mut infcx);
    let mut graph = SearchGraph::new(SearchGraphConfig { recursion_limit: 4, ..SearchGraphConfig::default() });
    assert_eq!(ecx.evaluate(&mut graph, trait_goal(&cx, named(&prog, "Tr"), tcx.tys.bool_, &[])), Ok(Certainty::overflow(true)));
}

#[test]
fn selection_normalizes_chained_associated_values() {
    let (prog, tcx) = program(b"#![no_std] trait A { type Item; } struct Inner; struct Outer; impl A for Inner { type Item = bool; } impl A for Outer { type Item = <Inner as A>::Item; } trait Tr {} impl Tr for bool {}");
    let state = EvalState::new();
    let cx = EvalCx::new(&prog, TypingEnv::fully_monomorphized(), &state);
    let mut infcx = Inference::new(&tcx.tys);
    let projection = tcx.tys.intern(TyKind::Assoc(named(&prog, "Item"), vec![adt(&tcx, &prog, "Outer", vec![])], RegionArgsId::EMPTY));
    assert_eq!(evaluate(&tcx, &cx, &mut infcx, trait_goal(&cx, named(&prog, "Tr"), projection, &[])), Ok(Certainty::Yes));
}

#[test]
fn chained_projection_cycle_overflows_as_ambiguity() {
    let (prog, tcx) = program(b"#![no_std] trait A { type Item; } struct Left; struct Right; impl A for Left { type Item = <Right as A>::Item; } impl A for Right { type Item = <Left as A>::Item; } trait Tr {} impl Tr for bool {}");
    let state = EvalState::new();
    let cx = EvalCx::new(&prog, TypingEnv::fully_monomorphized(), &state);
    let mut infcx = Inference::new(&tcx.tys);
    let projection = tcx.tys.intern(TyKind::Assoc(named(&prog, "Item"), vec![adt(&tcx, &prog, "Left", vec![])], RegionArgsId::EMPTY));
    assert_eq!(evaluate(&tcx, &cx, &mut infcx, trait_goal(&cx, named(&prog, "Tr"), projection, &[])), Ok(Certainty::overflow(true)));
}

#[test]
fn ambiguous_probes_rollback_bindings_and_equations() {
    let (prog, tcx) = program(b"#![no_std] trait Tr<T> {} impl Tr<bool> for u32 {} impl Tr<char> for u32 {}");
    let state = EvalState::new();
    let cx = EvalCx::new(&prog, TypingEnv::fully_monomorphized(), &state);
    let mut infcx = Inference::new(&tcx.tys);
    let arg = infcx.fresh_ty(TyVariableKind::General);
    let mark = infcx.snapshot();
    assert!(matches!(select(&tcx, &cx, &mut infcx, pred(named(&prog, "Tr"), tcx.tys.prim(crate::program::Prim::U32), &[arg])), SelectionResult::Ambiguous(_)));
    assert_eq!(infcx.resolve_ty(arg), arg);
    assert!(infcx.take_relations_since(mark).is_empty());
    let p = tcx.tys.intern(TyKind::Assoc(named(&prog, "Tr"), vec![tcx.tys.bool_], RegionArgsId::EMPTY));
    assert!(infcx.relate(arg, p));
    infcx.rollback(mark);
    assert!(infcx.take_relations_since(mark).is_empty());
}

#[test]
fn definitive_answers_do_not_cross_environments() {
    let (prog, tcx) = program(b"#![no_std] trait Tr {}");
    let tr = named(&prog, "Tr");
    let state = EvalState::new();
    let empty = EvalCx::new(&prog, TypingEnv::fully_monomorphized(), &state);
    let mut env = ParamEnv::default(); env.preds.push((tcx.tys.bool_, tr, Vec::new()));
    let bounded = EvalCx::new(&prog, TypingEnv { param_env: tcx.intern_param_env(env), ..TypingEnv::fully_monomorphized() }, &state);
    let mut infcx = Inference::new(&tcx.tys);
    assert_eq!(evaluate(&tcx, &empty, &mut infcx, trait_goal(&empty, tr, tcx.tys.bool_, &[])), Err(NoSolution));
    assert_eq!(evaluate(&tcx, &bounded, &mut infcx, trait_goal(&bounded, tr, tcx.tys.bool_, &[])), Ok(Certainty::Yes));
}

#[test]
fn global_where_clause_does_not_hide_an_impl() {
    let (prog, tcx) = program(b"#![no_std] trait Tr {} impl Tr for bool {}");
    let tr = named(&prog, "Tr");
    let mut env = ParamEnv::default(); env.preds.push((tcx.tys.bool_, tr, Vec::new()));
    let state = EvalState::new();
    let cx = EvalCx::new(&prog, TypingEnv { param_env: tcx.intern_param_env(env), ..TypingEnv::fully_monomorphized() }, &state);
    let mut infcx = Inference::new(&tcx.tys);
    let SelectionResult::Ok(s) = select(&tcx, &cx, &mut infcx, pred(tr, tcx.tys.bool_, &[])) else { panic!() };
    assert!(matches!(s.source, CandidateSource::Impl(_)));
}

#[test]
fn alias_and_object_bounds_relate_trait_arguments() {
    let (prog, tcx) = program(b"#![no_std] trait Tr<T> {} trait Has { type Out: Tr<bool>; } fn input(a: &dyn Tr<bool>) {}");
    let tr = named(&prog, "Tr");
    let p = tcx.tys.intern(TyKind::Param(0));
    let projection = tcx.tys.intern(TyKind::Assoc(named(&prog, "Out"), vec![p], RegionArgsId::EMPTY));
    let input = tcx.fn_item_sig(&prog, named(&prog, "input")).unwrap().params[0];
    let TyKind::Ref(_, object, _) = tcx.tys.kind(input) else { panic!() };
    let state = EvalState::new();
    let cx = EvalCx::new(&prog, TypingEnv::fully_monomorphized(), &state);
    let mut infcx = Inference::new(&tcx.tys);
    for ty in [projection, *object] {
        assert!(matches!(select(&tcx, &cx, &mut infcx, pred(tr, ty, &[tcx.tys.bool_])), SelectionResult::Ok(_)));
        assert!(matches!(select(&tcx, &cx, &mut infcx, pred(tr, ty, &[tcx.tys.char_])), SelectionResult::NoSolution));
    }
}

#[test]
fn inference_dependent_ambiguity_is_retried() {
    let (prog, tcx) = program(b"#![no_std] trait Tr {} trait Bound {} impl Bound for bool {} struct W<T>(T); impl<T: Bound> Tr for W<T> {}");
    let state = EvalState::new();
    let cx = EvalCx::new(&prog, TypingEnv::fully_monomorphized(), &state);
    let mut infcx = Inference::new(&tcx.tys);
    let v = infcx.fresh_ty(TyVariableKind::General);
    let ty = adt(&tcx, &prog, "W", vec![v]);
    let mut ecx = Evaluation::new(&tcx, &cx, &mut infcx);
    let mut graph = SearchGraph::new(SearchGraphConfig::default());
    let goal = trait_goal(&cx, named(&prog, "Tr"), ty, &[]);
    assert_eq!(ecx.evaluate(&mut graph, goal.clone()), Ok(Certainty::Maybe(MaybeCause::Ambiguity)));
    assert!(ecx.infcx.relate(v, tcx.tys.bool_));
    assert_eq!(ecx.evaluate(&mut graph, goal), Ok(Certainty::Yes));
}

#[test]
fn projection_binding_retries_an_earlier_nested_trait() {
    let (prog, tcx) = program(b"#![no_std] trait Tr {} trait Bound {} trait Has { type Out; } impl Bound for bool {} impl Has for char { type Out = bool; } struct W<I>(I); impl<T: Bound, I: Has<Out = T>> Tr for W<I> {}");
    let state = EvalState::new();
    let cx = EvalCx::new(&prog, TypingEnv::fully_monomorphized(), &state);
    let mut infcx = Inference::new(&tcx.tys);
    let ty = adt(&tcx, &prog, "W", vec![tcx.tys.char_]);
    let SelectionResult::Ok(s) = select_fulfilled(&tcx, &cx, &mut infcx, pred(named(&prog, "Tr"), ty, &[])) else { panic!("nested goals did not converge") };
    assert_eq!(s.args, vec![tcx.tys.bool_, tcx.tys.char_]);
}

#[test]
fn rustc_oracle_destructor_with_callable_predicate() {
    struct OnDrop<F: FnMut()>(F);
    impl<F: FnMut()> Drop for OnDrop<F> {
        fn drop(&mut self) { (self.0)(); }
    }
    let count = std::cell::Cell::new(0);
    { let _guard = OnDrop(|| count.set(count.get() + 1)); }
    assert_eq!(count.get(), 1);
}

#[test]
fn nested_unresolved_goal_keeps_ambiguity_cause() {
    let (prog, tcx) = program(b"#![no_std] trait Tr {} trait Bound {} trait Inner {} struct W<T>(T); impl<T: Bound> Inner for W<T> {} impl<T> Tr for W<T> where W<T>: Inner {}");
    let state = EvalState::new();
    let cx = EvalCx::new(&prog, TypingEnv::fully_monomorphized(), &state);
    let mut infcx = Inference::new(&tcx.tys);
    let v = infcx.fresh_ty(TyVariableKind::General);
    let ty = adt(&tcx, &prog, "W", vec![v]);
    assert_eq!(evaluate(&tcx, &cx, &mut infcx, trait_goal(&cx, named(&prog, "Tr"), ty, &[])), Ok(Certainty::Maybe(MaybeCause::Ambiguity)));
}

#[test]
fn callable_nested_bound_dispatch_probe() {
    let (prog, tcx) = program(br#"#![no_std]
        #[lang = "fn_mut"] trait FnMut<Args> {}
        trait Tr {}
        struct W<F: FnMut()>(F);
        impl<F: FnMut()> Tr for W<F> {}
        fn input(f: fn()) {}
    "#);
    let state = EvalState::new();
    let cx = EvalCx::new(&prog, TypingEnv::fully_monomorphized(), &state);
    let mut infcx = Inference::new(&tcx.tys);
    let f = tcx.fn_item_sig(&prog, named(&prog, "input")).unwrap().params[0];
    let ty = adt(&tcx, &prog, "W", vec![f]);
    let tr = named(&prog, "Tr");
    assert!(matches!(tcx.select_trait(&cx, tr, ty, &[]), SelectionResult::Ok(_)), "fulfilled query");
    let selected = select_fulfilled(&tcx, &cx, &mut infcx, pred(tr, ty, &[]));
    assert!(matches!(selected, SelectionResult::Ok(_)), "valid callable bound: {selected:?}");
}

#[test]
fn callable_output_equality_precedes_sized_obligation() {
    let (prog, tcx) = program(br#"#![no_std]
        #[lang = "sized"] trait Sized {}
        #[lang = "fn_once"] trait FnOnce<Args> { #[lang = "fn_once_output"] type Output; }
    "#);
    let state = EvalState::new();
    let cx = EvalCx::new(&prog, TypingEnv::fully_monomorphized(), &state);
    let mut infcx = Inference::new(&tcx.tys);
    let ret = infcx.fresh_ty(TyVariableKind::General);
    let f = tcx.tys.intern(TyKind::FnPtr(vec![], ret, crate::types::FnHeader::RUST, 0));
    let projection = tcx.tys.intern(TyKind::Assoc(named(&prog, "Output"), vec![f, tcx.tys.unit], RegionArgsId::EMPTY));
    let goal = Goal { param_env: ParamEnvId(cx.typing_env.param_env.index()), predicate: Predicate::AliasRelate(Term::Ty(projection), Term::Ty(tcx.tys.i32_), AliasRelationDirection::Equate) };
    assert_eq!(evaluate(&tcx, &cx, &mut infcx, goal), Ok(Certainty::Yes));
    assert_eq!(infcx.resolve_deep(ret), tcx.tys.i32_);
}

#[test]
fn unknown_closure_kind_stalls_shared_but_admits_once() {
    let (prog, tcx) = program(br#"#![no_std]
        #[lang = "fn"] trait Fn<Args> {}
        #[lang = "fn_once"] trait FnOnce<Args> {}
    "#);
    let state = EvalState::new();
    let cx = EvalCx::new(&prog, TypingEnv::fully_monomorphized(), &state);
    let sig = tcx.tys.intern(TyKind::FnPtr(vec![], tcx.tys.unit, crate::types::FnHeader::RUST, 0));
    let ty = tcx.tys.intern(TyKind::Closure(0, 0, sig, tcx.tys.unit, tcx.tys.unit));
    assert!(matches!(tcx.select_trait(&cx, named(&prog, "Fn"), ty, &[tcx.tys.unit]), SelectionResult::Ambiguous(_)));
    assert!(matches!(tcx.select_trait(&cx, named(&prog, "FnOnce"), ty, &[tcx.tys.unit]), SelectionResult::Ok(_)));
    tcx.closure_capture_types.insert((0, 0, tcx.tys.unit, tcx.collect_epoch.load(std::sync::atomic::Ordering::Relaxed)), crate::upvar::ClosureCaptureTypes { kind: crate::upvar::ClosureKind::Fn, is_copy: true, upvars: tcx.tys.unit });
    assert!(matches!(tcx.select_trait(&cx, named(&prog, "Fn"), ty, &[tcx.tys.unit]), SelectionResult::Ok(_)));
}

#[test]
fn numeric_variable_assembles_numeric_impls() {
    let (prog, tcx) = program(b"#![no_std] trait One {} impl One for u32 {} trait Many {} impl Many for u32 {} impl Many for i32 {}");
    let state = EvalState::new();
    let cx = EvalCx::new(&prog, TypingEnv::fully_monomorphized(), &state);
    let mut infcx = Inference::new(&tcx.tys);
    let v = infcx.fresh_ty(TyVariableKind::Int);
    assert!(matches!(select(&tcx, &cx, &mut infcx, pred(named(&prog, "Many"), v, &[])), SelectionResult::Ambiguous(_)));
    assert_eq!(infcx.resolve_deep(v), v);
    assert!(matches!(select(&tcx, &cx, &mut infcx, pred(named(&prog, "One"), v, &[])), SelectionResult::Ok(_)));
    assert_eq!(infcx.resolve_deep(v), tcx.tys.prim(crate::program::Prim::U32));
}

#[test]
fn dyn_auto_traits_distinguish_impl_headers() {
    let (prog, tcx) = program(b"#![no_std] trait Principal {} auto trait Auto {} trait Tr {} impl Tr for dyn Principal {} impl Tr for dyn Principal + Auto {} fn a(_: &dyn Principal) {} fn b(_: &(dyn Principal + Auto)) {}");
    let state = EvalState::new();
    let cx = EvalCx::new(&prog, TypingEnv::fully_monomorphized(), &state);
    let mut selected = Vec::new();
    for name in ["a", "b"] {
        let TyKind::Ref(_, ty, _) = tcx.tys.kind(tcx.fn_item_sig(&prog, named(&prog, name)).unwrap().params[0]) else { panic!("ref") };
        let SelectionResult::Ok(result) = tcx.select_trait(&cx, named(&prog, "Tr"), *ty, &[]) else { panic!("unique object impl") };
        selected.push(result.source);
    }
    assert_ne!(selected[0], selected[1]);
}

#[test]
fn numeric_auto_goal_retries_after_fallback() {
    let (prog, tcx) = program(b"#![no_std] auto trait Auto {}");
    let state = EvalState::new();
    let cx = EvalCx::new(&prog, TypingEnv::fully_monomorphized(), &state);
    let mut infcx = Inference::new(&tcx.tys);
    let ty = infcx.fresh_ty(TyVariableKind::Float);
    let predicate = pred(named(&prog, "Auto"), ty, &[]);
    assert!(matches!(select(&tcx, &cx, &mut infcx, predicate.clone()), SelectionResult::Ambiguous(_)));
    assert!(infcx.relate(ty, tcx.tys.f64_));
    assert!(matches!(select_fulfilled(&tcx, &cx, &mut infcx, predicate), SelectionResult::Ok(_)));
}

#[test]
fn method_lookup_preserves_ambiguous_and_missing_goals() {
    let (prog, tcx) = program(b"#![no_std] trait Tr { fn call(&self); } impl Tr for bool {} impl Tr for bool {}");
    let state = EvalState::new();
    let cx = EvalCx::new(&prog, TypingEnv::fully_monomorphized(), &state);
    let method = named(&prog, "call");
    assert!(matches!(tcx.resolve_trait_method(&cx, &prog, method, &[tcx.tys.bool_]), crate::tcx::MethodResolution::Ambiguous(_, _)));
    assert!(matches!(tcx.resolve_trait_method(&cx, &prog, method, &[tcx.tys.char_]), crate::tcx::MethodResolution::NoSolution(_)));
}

#[test]
fn callable_builtin_checks_full_function_header() {
    use crate::types::{Abi, FnHeader, Safety};
    let (prog, tcx) = program(br#"#![no_std]
        #[lang = "fn_once"] trait FnOnce<Args> {}
        fn ordinary() {}
        unsafe fn unsafe_function() {}
        extern "C" fn c_function() {}
        #[target_feature(enable = "sse2")] fn featured() {}
    "#);
    let state = EvalState::new();
    let cx = EvalCx::new(&prog, TypingEnv::fully_monomorphized(), &state);
    let once = named(&prog, "FnOnce");
    for abi in [Abi::Rust, Abi::C, Abi::CUnwind, Abi::RustCall] {
        for safety in [Safety::Safe, Safety::Unsafe] {
            for c_variadic in [false, true] {
                let header = FnHeader { abi, safety, c_variadic };
                let ty = tcx.tys.intern(TyKind::FnPtr(vec![], tcx.tys.unit, header, 0));
                let selected = tcx.select_trait(&cx, once, ty, &[tcx.tys.unit]);
                assert_eq!(matches!(selected, SelectionResult::Ok(_)), abi == Abi::Rust && safety == Safety::Safe && !c_variadic);
            }
        }
    }
    for name in ["ordinary", "unsafe_function", "c_function", "featured"] {
        let ty = tcx.tys.intern(TyKind::FnDef(named(&prog, name), Vec::new(), RegionArgsId::EMPTY));
        assert_eq!(matches!(tcx.select_trait(&cx, once, ty, &[tcx.tys.unit]), SelectionResult::Ok(_)), name == "ordinary");
    }
}

#[test]
fn async_callable_requires_future_and_projects_its_output() {
    let (prog, tcx) = program(br#"#![no_std]
        #[lang = "future_trait"] trait Future { #[lang = "future_output"] type Output; }
        #[lang = "async_fn_once"] trait AsyncFnOnce<Args> {
            #[lang = "async_fn_once_output"] type Output;
            #[lang = "call_once_future"] type CallOnceFuture;
        }
        struct Fut;
        impl Future for Fut { type Output = u32; }
    "#);
    let state = EvalState::new();
    let cx = EvalCx::new(&prog, TypingEnv::fully_monomorphized(), &state);
    let once = named(&prog, "AsyncFnOnce");
    let fut = adt(&tcx, &prog, "Fut", vec![]);
    let good = tcx.tys.intern(TyKind::FnPtr(vec![], fut, crate::types::FnHeader::RUST, 0));
    let bad = tcx.tys.intern(TyKind::FnPtr(vec![], tcx.tys.u32_, crate::types::FnHeader::RUST, 0));
    assert!(matches!(tcx.select_trait(&cx, once, good, &[tcx.tys.unit]), SelectionResult::Ok(_)));
    assert!(matches!(tcx.select_trait(&cx, once, bad, &[tcx.tys.unit]), SelectionResult::NoSolution));
    let output = tcx.lang_items.get(LangItem::AsyncFnOnceOutput).unwrap();
    let projection = tcx.tys.intern(TyKind::Assoc(output, vec![good, tcx.tys.unit], RegionArgsId::EMPTY));
    let mut infcx = Inference::new(&tcx.tys);
    assert_eq!(normalize_projection(&tcx, &cx, &mut infcx, projection), Ok((tcx.tys.u32_, Certainty::Yes)));
}

#[test]
fn opaque_auto_trait_waits_for_publication_without_typeck_reentry() {
    let (prog, tcx) = program(b"#![no_std] auto trait Auto {} trait Bound {} fn hidden() -> impl Bound { 1u32 }");
    let def = named(&prog, "hidden");
    let ty = tcx.fn_item_sig(&prog, def).unwrap().ret;
    let state = EvalState::new();
    let cx = EvalCx::new(&prog, TypingEnv::fully_monomorphized(), &state);
    let mut infcx = Inference::new(&tcx.tys);
    let goal = trait_goal(&cx, named(&prog, "Auto"), ty, &[]);
    assert_eq!(evaluate(&tcx, &cx, &mut infcx, goal.clone()), Ok(Certainty::Maybe(MaybeCause::Ambiguity)));
    assert!(tcx.opaque_hidden.get(&ty).is_none());
    assert_eq!(*state.opaque_requests.borrow(), vec![ty]);
    tcx.opaque_hidden.insert(ty, tcx.tys.u32_);
    assert_eq!(evaluate(&tcx, &cx, &mut infcx, goal), Ok(Certainty::Yes));
}

#[test]
fn opaque_auto_trait_leaks_negative_hidden_type() {
    let (prog, tcx) = program(b"#![no_std] auto trait Auto {} struct Bad; impl !Auto for Bad {} trait Bound {} fn hidden() -> impl Bound { Bad }");
    let ty = tcx.fn_item_sig(&prog, named(&prog, "hidden")).unwrap().ret;
    tcx.opaque_hidden.insert(ty, adt(&tcx, &prog, "Bad", vec![]));
    let state = EvalState::new();
    let cx = EvalCx::new(&prog, TypingEnv::fully_monomorphized(), &state);
    let mut infcx = Inference::new(&tcx.tys);
    assert_eq!(evaluate(&tcx, &cx, &mut infcx, trait_goal(&cx, named(&prog, "Auto"), ty, &[])), Err(NoSolution));
}

#[test]
fn opaque_auto_bound_needs_no_hidden_type_query() {
    let (prog, tcx) = program(b"#![no_std] auto trait Auto {} fn hidden() -> impl Auto { 1u32 }");
    let ty = tcx.fn_item_sig(&prog, named(&prog, "hidden")).unwrap().ret;
    let state = EvalState::new();
    let cx = EvalCx::new(&prog, TypingEnv::fully_monomorphized(), &state);
    let mut infcx = Inference::new(&tcx.tys);
    assert_eq!(evaluate(&tcx, &cx, &mut infcx, trait_goal(&cx, named(&prog, "Auto"), ty, &[])), Ok(Certainty::Yes));
    assert!(state.opaque_requests.borrow().is_empty());
}

#[test]
fn projection_overflow_budget_survives_nested_evaluations() {
    let (prog, tcx) = program(b"#![no_std] trait Project { type Out; } impl Project for u32 { type Out = u32; }");
    let state = EvalState::new();
    let cx = EvalCx::new(&prog, TypingEnv::fully_monomorphized(), &state);
    let projection = tcx.tys.intern(TyKind::Assoc(named(&prog, "Out"), vec![tcx.tys.u32_], RegionArgsId::EMPTY));
    let mut infcx = Inference::new(&tcx.tys);
    let mut parents = Vec::new();
    for _ in 0..127 { parents.push(crate::tcx::Depth::enter_solver(&state).unwrap()); }
    assert!(matches!(normalize_projection(&tcx, &cx, &mut infcx, projection),
        Ok((_, Certainty::Maybe(MaybeCause::Overflow { .. })))));
    assert_eq!(state.solver_depth.get(), 127);
    drop(parents);
    assert_eq!(normalize_projection(&tcx, &cx, &mut infcx, projection), Ok((tcx.tys.u32_, Certainty::Yes)));
    assert_eq!(state.solver_depth.get(), 0);
}

#[test]
fn callable_output_predicate_is_inherited_from_impl() {
    let (prog, tcx) = program(br#"#![no_std]
        #[lang = "fn_once"] trait FnOnce<Args> { #[lang = "fn_once_output"] type Output; }
        #[lang = "fn_mut"] trait FnMut<Args>: FnOnce<Args> {}
        #[lang = "fn"] trait Fn<Args>: FnMut<Args> {}
        struct Option<T>(T);
        trait Selector { fn select(self); }
        impl<F, G> Selector for F where F: Fn(&mut u32) -> Option<G> {
            fn select(self) {}
        }
    "#);
    let mut method = None;
    for (i, def) in prog.defs.iter().enumerate() {
        if prog.name(DefId(i as u32)) == "select" && prog.def(def.parent).kind == DefKind::Impl { method = Some(DefId(i as u32)); }
    }
    let signatures = tcx.callable_signatures(&prog, method.unwrap());
    assert_eq!(signatures.len(), 1);
    let TyKind::FnPtr(_, output, _, _) = tcx.tys.kind(signatures[0].signature) else { panic!("callable signature") };
    assert_eq!(*output, adt(&tcx, &prog, "Option", vec![tcx.tys.intern(TyKind::Param(1))]));
}
