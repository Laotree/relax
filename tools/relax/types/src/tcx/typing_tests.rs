use crate::solve::SelectionResult;
use super::*;

#[test]
fn inference_diagnostics_do_not_mask_body_error() {
    let (prog, tcx) = program(br#"#![no_std]
        #[lang = "fn_once"] trait FnOnce<Args> {
            #[lang = "fn_once_output"] type Output;
        }
        struct Choice<T>(T);
        impl<T> Choice<T> {
            fn accepts<F: FnOnce(T) -> bool>(self, _f: F) -> bool { true }
        }
        trait Property {}
        impl Property for u8 {}
        fn consume<T: Property>(_: fn() -> T) {}
        fn broken() {
            let _ = Choice(1u8).accepts(|value| value == 1);
            consume(missing);
        }
        fn unknown<T: Property>() {}
        fn ambiguous() { unknown(); }
    "#);
    let state = EvalState::new();
    let cx = EvalCx::new(&prog, TypingEnv::fully_monomorphized(), &state);
    let body = crate::typeck::check_fn(&cx, &prog, &tcx, named(&prog, "broken"), &[]);
    assert!(body.errors.iter().any(|e| e.contains("cannot find value `missing`")), "{:?}", body.errors);
    assert!(!body.errors.iter().any(|e| e.contains("cannot infer the generic arguments")), "{:?}", body.errors);
    assert!(!body.errors.iter().any(|e| e.contains("ambiguous obligation")), "{:?}", body.errors);
    let body = crate::typeck::check_fn(&cx, &prog, &tcx, named(&prog, "ambiguous"), &[]);
    assert!(body.errors.iter().any(|e| e.contains("cannot infer the generic arguments")), "{:?}", body.errors);
}

fn program(source: &[u8]) -> (Program, Tcx) {
    let dir = std::env::temp_dir().join(format!("relax-typing-env-{}-{}", std::process::id(), std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos()));
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

#[test]
fn projection_fields_do_not_cross_environments() {
    let (prog, tcx) = program(b"#![no_std]\ntrait Tr { type A; } struct S<T: Tr> { value: T::A }");
    let assoc = named(&prog, "A");
    let param = tcx.tys.intern(TyKind::Param(0));
    let projection = tcx.tys.intern(TyKind::Assoc(assoc, vec![param], crate::types::RegionArgsId::EMPTY));
    let mut a = ParamEnv::default();
    a.eqs.push((projection, tcx.tys.bool_));
    let mut b = ParamEnv::default();
    b.eqs.push((projection, tcx.tys.char_));
    let a_state = crate::tcx::EvalState::new();
    let a = EvalCx::new(&prog, TypingEnv { param_env: tcx.intern_param_env(a), mode: TypingMode::Analysis { defining_opaques: Default::default() } }, &a_state);
    let b_state = crate::tcx::EvalState::new();
    let b = EvalCx::new(&prog, TypingEnv { param_env: tcx.intern_param_env(b), mode: TypingMode::Borrowck }, &b_state);
    for _ in 0..2 {
        assert_eq!(tcx.field_ty(&prog, a.typing_env, named(&prog, "S"), 0, 0, &[param]), tcx.tys.bool_);
        assert_eq!(tcx.field_ty(&prog, b.typing_env, named(&prog, "S"), 0, 0, &[param]), tcx.tys.char_);
    }
    // Concrete projections are memoized too; a predicate environment remains an input.
    let concrete = tcx.tys.intern(TyKind::Assoc(assoc, vec![tcx.tys.bool_], crate::types::RegionArgsId::EMPTY));
    let mut aenv = ParamEnv::default();
    aenv.eqs.push((concrete, tcx.tys.bool_));
    let mut benv = ParamEnv::default();
    benv.eqs.push((concrete, tcx.tys.char_));
    let a_state = crate::tcx::EvalState::new();
    let a = EvalCx::new(&prog, TypingEnv { param_env: tcx.intern_param_env(aenv), mode: TypingMode::PostAnalysis }, &a_state);
    let b_state = crate::tcx::EvalState::new();
    let b = EvalCx::new(&prog, TypingEnv { param_env: tcx.intern_param_env(benv), mode: TypingMode::PostAnalysis }, &b_state);
    for _ in 0..2 {
        assert_eq!(tcx.normalize(&a, &prog, concrete), tcx.tys.bool_);
        assert_eq!(tcx.normalize(&b, &prog, concrete), tcx.tys.char_);
    }
}

#[test]
fn selection_cycles_leave_other_roots_usable() {
    let (prog, tcx) = program(b"#![no_std]\ntrait Tr {} trait Good {} struct S; impl<T: Tr> Tr for T {} impl Good for S {}");
    let tr = named(&prog, "Tr");
    let good = named(&prog, "Good");
    let s = tcx.tys.intern(TyKind::Adt(named(&prog, "S"), Vec::new(), crate::types::RegionArgsId::EMPTY));
    let a_state = crate::tcx::EvalState::new();
    let a = EvalCx::new(&prog, TypingEnv::fully_monomorphized(), &a_state);
    let b_state = crate::tcx::EvalState::new();
    let b = EvalCx::new(&prog, TypingEnv { param_env: Default::default(), mode: TypingMode::Analysis { defining_opaques: Default::default() } }, &b_state);
    assert!(matches!(tcx.select_trait(&a, tr, tcx.tys.bool_, &[]), SelectionResult::NoSolution));
    assert!(matches!(tcx.select_trait(&b, good, s, &[]), SelectionResult::Ok(_)));
    assert!(matches!(tcx.select_trait(&b, tr, tcx.tys.bool_, &[]), SelectionResult::NoSolution));
    assert!(matches!(tcx.select_trait(&a, good, s, &[]), SelectionResult::Ok(_)));
}

#[test]
fn nested_const_frames_restore_self_args_and_bindings() {
    let (prog, tcx) = program(br#"#![no_std]
        trait Val { const N: usize; }
        struct Three;
        struct Twice<T>(T);
        impl Val for Three { const N: usize = 3; }
        impl<T: Val> Val for Twice<T> { const N: usize = T::N * 2; }
        const fn add(a: usize, b: usize) -> usize { a + b }
        const A: usize = <Twice<Three> as Val>::N;
        const B: usize = <Twice<Twice<Three>> as Val>::N;
        const C: usize = add(add(1, 2), add(3, 4));
    "#);
    let cx_state = crate::tcx::EvalState::new();
    let cx = EvalCx::new(&prog, TypingEnv::fully_monomorphized(), &cx_state);
    for (name, expected) in [("A", 6), ("B", 12), ("C", 10), ("A", 6)] {
        assert_eq!(crate::consteval::eval_const_def(&cx, &prog, &tcx, named(&prog, name), 0), Some(expected));
    }
}

#[test]
fn empty_analysis_and_nested_body_inputs_are_explicit() {
    let (prog, tcx) = program(b"#![no_std]\ntrait Tr<A> {} impl Tr<u8> for bool {} fn inner() -> u8 { 1 }");
    let tr = named(&prog, "Tr");
    let param = tcx.tys.intern(TyKind::Param(0));
    let mono_state = crate::tcx::EvalState::new();
    let mono = EvalCx::new(&prog, TypingEnv::fully_monomorphized(), &mono_state);
    let analysis_state = crate::tcx::EvalState::new();
    let analysis = EvalCx::new(&prog, TypingEnv { param_env: Default::default(), mode: TypingMode::Analysis { defining_opaques: Default::default() } }, &analysis_state);
    assert!(matches!(tcx.select_trait(&mono, tr, tcx.tys.bool_, &[param]), SelectionResult::NoSolution));
    assert!(matches!(tcx.select_trait(&analysis, tr, tcx.tys.bool_, &[param]), SelectionResult::NoSolution));
    analysis.lit_vars.borrow_mut().push(2);
    let body = crate::typeck::check_fn(&analysis, &prog, &tcx, named(&prog, "inner"), &[]);
    assert!(body.errors.is_empty(), "{:?}", body.errors);
    assert_eq!(*analysis.lit_vars.borrow(), vec![2]);
    assert!(matches!(tcx.select_trait(&analysis, tr, tcx.tys.bool_, &[param]), SelectionResult::NoSolution));
}

#[test]
fn environments_are_interned_across_threads_and_growth() {
    let tcx = Tcx::new();
    assert_eq!(tcx.intern_param_env(ParamEnv::default()), ParamEnvId::EMPTY);
    assert_eq!(TypingEnv::fully_monomorphized().param_env, ParamEnvId::EMPTY);
    let mut env = ParamEnv::default();
    env.preds.push((tcx.tys.bool_, DefId(1), vec![tcx.tys.u8_]));
    env.eqs.push((tcx.tys.bool_, tcx.tys.char_));
    env.eqs.push((tcx.tys.u8_, tcx.tys.u32_));
    let id = tcx.intern_param_env(env.clone());
    let retained = tcx.param_env(id).unwrap();
    std::thread::scope(|scope| {
        for _ in 0..8 {
            let tcx = &tcx;
            let env = &env;
            scope.spawn(move || {
                for i in 0..1024 {
                    let mut other = env.clone();
                    other.preds[0].1 = DefId(i + 2);
                    let other_id = tcx.intern_param_env(other.clone());
                    assert_eq!(tcx.param_env(other_id), Some(&other));
                    assert_eq!(tcx.intern_param_env(other), other_id);
                    assert_eq!(tcx.intern_param_env(env.clone()), id);
                }
            });
        }
    });
    assert!(std::ptr::eq(retained, tcx.param_env(id).unwrap()));
    assert_eq!(retained, &env);
    let mut other = env.clone();
    other.eqs[0].1 = tcx.tys.u8_;
    assert_ne!(tcx.intern_param_env(other), id);
    let mut other = env.clone();
    other.eqs[1].1 = tcx.tys.u8_;
    assert_ne!(tcx.intern_param_env(other), id);
    let owners = tcx.intern_defining_opaques(vec![DefId(1), DefId(2)]);
    assert_eq!(tcx.intern_defining_opaques(vec![DefId(1), DefId(2)]), owners);
    assert_ne!(tcx.intern_defining_opaques(vec![DefId(1)]), owners);
    assert_eq!(tcx.defining_opaques(owners), &[DefId(1), DefId(2)]);
    assert!(tcx.defining_opaques(Default::default()).is_empty());
}

#[test]
fn copying_typing_env_and_borrowing_nested_state_preserves_keys() {
    let prog = Program::new(&std::sync::Arc::new(crate::Session::default()));
    let tcx = Tcx::new();
    let state = EvalState::new();
    let env = TypingEnv { param_env: ParamEnvId::EMPTY, mode: TypingMode::Analysis { defining_opaques: tcx.intern_defining_opaques(vec![DefId(1)]) } };
    let copied = env;
    let mut memo = crate::fxhash::HashMap::default();
    memo.insert(env, true);
    assert_eq!(memo.get(&copied), Some(&true));
    assert_eq!(std::mem::size_of::<TypingEnv>(), 12);
    let cx = EvalCx::new(&prog, copied, &state);
    cx.lit_vars.borrow_mut().push(1);
    let nested = cx.body();
    assert!(std::ptr::eq(cx.state, nested.state));
    nested.state.const_asked.set(7);
    assert_eq!(cx.state.const_asked.get(), 7);
    assert!(nested.lit_vars.borrow().is_empty());
    assert_eq!(*cx.lit_vars.borrow(), vec![1]);
}
