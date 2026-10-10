use super::*;
use crate::solve::canonical::GenericArg;
use crate::solve::canonical::*;
use crate::solve::canonicalizer::*;
use crate::solve::goal::*;
use crate::types::{
    BoundTy, BoundTyKind, BoundVar, PlaceholderType, RegionArgsId, RegionId, RegionKind,
};

// Diagnostic for the merged selection/callable migration. A callable predicate
// must retain its binder and its relation must not certify a placeholder leak.
// rustc_trait_selection/src/traits/select/{mod.rs:545,confirmation.rs:602}.
#[test]
#[ignore = "region track: tinfer-b leak check"]
fn arch_t2b1_callable_general_pointer_is_not_static_pointer() {
    let prog = Program::new(&std::sync::Arc::new(crate::Session::default()));
    let tcx = Tcx::new();
    let state = crate::tcx::EvalState::new();
    let mut fcx = context(&prog, &tcx, &state);
    let bound = tcx.tys.intern_region(RegionKind::ReBound(0, BoundVar(0)));
    let static_ = tcx.tys.intern_region(RegionKind::ReStatic);
    let a = tcx.tys.intern(TyKind::Ref(false, tcx.tys.u32_, bound));
    let b = tcx.tys.intern(TyKind::Ref(false, tcx.tys.u32_, static_));
    let general = tcx.tys.intern(TyKind::FnPtr(vec![a], tcx.tys.unit, crate::types::FnHeader::RUST, 1));
    let specific = tcx.tys.intern(TyKind::FnPtr(vec![b], tcx.tys.unit, crate::types::FnHeader::RUST, 0));
    assert_ne!(general, specific);
    assert!(!fcx.unify(general, specific), "region-insensitive equality certifies unequal callable signatures");
}

#[test]
#[ignore = "region track: tinfer-b leak check"]
fn arch_t2b1_callable_placeholder_relation_is_not_proof() {
    let prog = Program::new(&std::sync::Arc::new(crate::Session::default()));
    let tcx = Tcx::new();
    let state = crate::tcx::EvalState::new();
    let mut fcx = context(&prog, &tcx, &state);
    let universe = fcx.create_next_universe();
    let placeholder = tcx.tys.intern_region(RegionKind::RePlaceholder { universe, var: BoundVar(0) });
    let static_ = tcx.tys.intern_region(RegionKind::ReStatic);
    let a = tcx.tys.intern(TyKind::Ref(false, tcx.tys.u32_, placeholder));
    let b = tcx.tys.intern(TyKind::Ref(false, tcx.tys.u32_, static_));
    let a = tcx.tys.intern(TyKind::Tuple(vec![a]));
    let b = tcx.tys.intern(TyKind::Tuple(vec![b]));
    let mark = fcx.snapshot();
    let accepted = fcx.unify(a, b);
    let recorded_effects = fcx.snapshot() != mark;
    fcx.rollback(mark);
    assert!(!accepted || recorded_effects,
        "Fn Args relation returns success without recording the placeholder = static constraint");
}

#[test]
fn arch_t2b1_callable_same_binder_control() {
    let prog = Program::new(&std::sync::Arc::new(crate::Session::default()));
    let tcx = Tcx::new();
    let state = crate::tcx::EvalState::new();
    let mut fcx = context(&prog, &tcx, &state);
    let bound = tcx.tys.intern_region(RegionKind::ReBound(0, BoundVar(0)));
    let a = tcx.tys.intern(TyKind::Ref(false, tcx.tys.u32_, bound));
    let general = tcx.tys.intern(TyKind::FnPtr(vec![a], tcx.tys.unit, crate::types::FnHeader::RUST, 1));
    assert!(fcx.unify(general, general));
}

#[test]
fn arch_t2b1_callable_rustc_oracle() {
    let root = std::env::temp_dir().join(format!("arch-t2b1-callable-oracle-{}", std::process::id()));
    std::fs::create_dir(&root).unwrap();
    let source = root.join("probe.rs");
    let metadata = root.join("probe.rmeta");
    for (input, accepted) in [("for<'a> fn(&'a u32)", true), ("fn(&'static u32)", false)] {
        let text = format!("fn require<F: for<'a> Fn(&'a u32)>(_: F) {{}}\npub fn probe(f: {input}) {{ require(f); }}\n");
        std::fs::write(&source, text).unwrap();
        let result = std::process::Command::new("rustc")
            .args(["--edition=2021", "--crate-type=lib", "--emit=metadata"])
            .arg(&source).arg("-o").arg(&metadata).output().unwrap();
        let stderr = String::from_utf8_lossy(&result.stderr);
        assert_eq!(result.status.success(), accepted, "{input}: {stderr}");
        if !accepted { assert!(stderr.contains("not general enough"), "{stderr}"); }
    }
    std::fs::remove_file(source).unwrap();
    if metadata.exists() { std::fs::remove_file(metadata).unwrap(); }
    std::fs::remove_dir(root).unwrap();
}

fn context<'a>(prog: &'a Program, tcx: &'a Tcx, state: &'a crate::tcx::EvalState) -> Fcx<'a> {
    Fcx {
        cx: crate::tcx::EvalCx::new(prog, crate::tcx::TypingEnv::fully_monomorphized(), state),
        prog,
        tcx,
        file: 0,
        module: 0,
        env: GenEnv::default(),
        inst_args: Vec::new(),
        b: Body::empty(NO_DEF, Vec::new(), 0, tcx.tys.unit),
        scopes: Vec::new(),
        local_hyg: Vec::new(),
        vars: Vec::new(),
        var_universes: Vec::new(),
        universe: UniverseIndex::ROOT,
        region_universes: HashMap::default(),
        region_vars: Default::default(),
        loops: Vec::new(),
        in_loop_condition: false,
        diverges: false,
        ret_stack: Vec::new(),
        closure_depth: Vec::new(),
        async_depth: 0,
        await_count: 0,
        cur_binop: 0,
        keep_literal_vars: true,
        diverging: Vec::new(),
        deferred_dyn: Vec::new(),
        deferred_casts: Vec::new(),
        bind_mode: 0,
        pat_path_pre: None,
        pending_goals: Vec::new(),
        pending_captures: Vec::new(),
        expected_closure_kinds: HashMap::default(),
        fn_expectations: Vec::new(),
        pending_tries: Vec::new(),
        extra_arg: None,
        last_lo: 0,
        bound_traits: None,
        known_targs: None,
        opaque_vars: Vec::new(),
        deferred_repeats: Vec::new(),
        forced_autoref: None,
        undo: Vec::new(),
        projection_relations: Vec::new(),
        method_expected: None,
        revealing: false,
    }
}

fn goal(envs: &mut ParamEnvInterner, ty: TyId) -> Goal {
    Goal {
        param_env: envs.intern(Vec::new()),
        predicate: Predicate::Clause(Clause::WellFormed(Term::Ty(ty))),
    }
}

fn vid(tcx: &Tcx, t: TyId) -> u32 {
    let TyKind::Infer(v) = tcx.tys.kind(t) else {
        panic!("expected inference variable")
    };
    *v
}

fn bound(tcx: &Tcx, depth: u32, var: u32) -> TyId {
    tcx.tys.intern(TyKind::Bound(
        depth,
        BoundTy {
            var: BoundVar(var),
            kind: BoundTyKind::Anon,
        },
    ))
}

#[test]
fn repeated_nested_variables_round_trip_and_resolve() {
    let prog = Program::new(&std::sync::Arc::new(crate::Session::default()));
    let tcx = Tcx::new();
    let state = crate::tcx::EvalState::new();
    let mut source = context(&prog, &tcx, &state);
    let a = source.fresh(0);
    let b = source.fresh(0);
    assert!(source.bind(vid(&tcx, b), a));
    let nested = tcx
        .tys
        .intern(TyKind::Tuple(vec![a, tcx.tys.intern(TyKind::Slice(b)), a]));
    let mut envs = ParamEnvInterner::new();
    let input = goal(&mut envs, nested);
    let (canonical, originals) = canonicalize_goal(
        &mut source,
        &tcx.tys,
        &mut envs,
        &input,
        CanonicalizeMode::Input,
    );
    assert_eq!(canonical.variables.len(), 1);
    assert_eq!(originals.values, vec![GenericArg::Ty(a)]);
    let restored = substitute_goal(&tcx.tys, &mut envs, &canonical.value, &originals);
    let resolved = tcx
        .tys
        .intern(TyKind::Tuple(vec![a, tcx.tys.intern(TyKind::Slice(a)), a]));
    assert_eq!(restored, goal(&mut envs, resolved));
    let target_state = crate::tcx::EvalState::new();
    let mut target = context(&prog, &tcx, &target_state);
    target.fresh(0);
    let (instantiated, values) =
        instantiate_canonical(&mut target, &tcx.tys, &mut envs, &canonical).unwrap();
    let GenericArg::Ty(fresh) = values.values[0] else {
        panic!()
    };
    assert_ne!(fresh, a);
    assert!(target.bind(vid(&tcx, fresh), tcx.tys.bool_));
    let (answer, _) = canonicalize_goal(
        &mut target,
        &tcx.tys,
        &mut envs,
        &instantiated,
        CanonicalizeMode::Response {
            max_input_universe: UniverseIndex::ROOT,
        },
    );
    assert!(answer.variables.is_empty());
    let expected = tcx.tys.intern(TyKind::Tuple(vec![
        tcx.tys.bool_,
        tcx.tys.intern(TyKind::Slice(tcx.tys.bool_)),
        tcx.tys.bool_,
    ]));
    assert_eq!(answer.value, goal(&mut envs, expected));
}

#[test]
fn params_placeholders_and_numeric_classes_are_distinct() {
    let prog = Program::new(&std::sync::Arc::new(crate::Session::default()));
    let tcx = Tcx::new();
    let state = crate::tcx::EvalState::new();
    let mut source = context(&prog, &tcx, &state);
    let u = source.create_next_universe();
    let general = source.fresh_in_universe(0, u);
    let int = source.fresh(1);
    let float = source.fresh(2);
    let param = tcx.tys.intern(TyKind::Param(3));
    let placeholder = tcx.tys.intern(TyKind::Placeholder(PlaceholderType {
        universe: u,
        bound: BoundVar(8),
    }));
    let ty = tcx.tys.intern(TyKind::Tuple(vec![
        general,
        int,
        float,
        param,
        placeholder,
        param,
    ]));
    let mut envs = ParamEnvInterner::new();
    let input = goal(&mut envs, ty);
    let (canonical, originals) = canonicalize_goal(
        &mut source,
        &tcx.tys,
        &mut envs,
        &input,
        CanonicalizeMode::Input,
    );
    assert_eq!(canonical.variables.len(), 5);
    assert_eq!(canonical.max_universe, UniverseIndex::ROOT);
    for (i, kind) in [
        TyVariableKind::General,
        TyVariableKind::Int,
        TyVariableKind::Float,
    ]
    .iter()
    .enumerate()
    {
        assert_eq!(
            canonical.variables[i],
            CanonicalVarKind::Ty {
                universe: UniverseIndex::ROOT,
                kind: *kind,
                sub_root: BoundVar(i as u32)
            }
        );
    }
    assert_eq!(
        canonical.variables[3],
        CanonicalVarKind::PlaceholderTy(Placeholder {
            universe: UniverseIndex::ROOT,
            var: BoundVar(3)
        })
    );
    assert_eq!(
        canonical.variables[4],
        CanonicalVarKind::PlaceholderTy(Placeholder {
            universe: UniverseIndex::ROOT,
            var: BoundVar(4)
        })
    );
    assert_eq!(
        substitute_goal(&tcx.tys, &mut envs, &canonical.value, &originals),
        input
    );
    let target_state = crate::tcx::EvalState::new();
    let mut target = context(&prog, &tcx, &target_state);
    let current = target.create_next_universe();
    let (_, values) = instantiate_canonical(&mut target, &tcx.tys, &mut envs, &canonical).unwrap();
    for (i, class) in [
        TyVariableKind::General,
        TyVariableKind::Int,
        TyVariableKind::Float,
    ]
    .iter()
    .enumerate()
    {
        let GenericArg::Ty(t) = values.values[i] else {
            panic!()
        };
        let info = target.ty_variable(vid(&tcx, t));
        assert_eq!(info.kind, *class);
        assert_eq!(
            info.universe,
            if i == 0 { current } else { UniverseIndex::ROOT }
        );
    }
}

#[test]
fn environment_is_folded_first_and_preserves_static_only_there() {
    let prog = Program::new(&std::sync::Arc::new(crate::Session::default()));
    let tcx = Tcx::new();
    let state = crate::tcx::EvalState::new();
    let mut fcx = context(&prog, &tcx, &state);
    let t = fcx.fresh(0);
    let r = fcx.fresh_region();
    let static_r = tcx.tys.intern_region(RegionKind::ReStatic);
    let reference = tcx.tys.intern(TyKind::Ref(false, t, static_r));
    let mut envs = ParamEnvInterner::new();
    let input = Goal {
        param_env: envs.intern(vec![Clause::TypeOutlives(reference, r)]),
        predicate: Predicate::Clause(Clause::TypeOutlives(reference, r)),
    };
    let (canonical, originals) = canonicalize_goal(
        &mut fcx,
        &tcx.tys,
        &mut envs,
        &input,
        CanonicalizeMode::Input,
    );
    assert_eq!(
        originals.values,
        vec![
            GenericArg::Ty(t),
            GenericArg::Region(r),
            GenericArg::Region(static_r)
        ]
    );
    assert!(matches!(
        canonical.variables[1],
        CanonicalVarKind::PlaceholderRegion(_)
    ));
    let env_ref = tcx
        .tys
        .intern(TyKind::Ref(false, bound(&tcx, 0, 0), static_r));
    let bound_r = tcx.tys.intern_region(RegionKind::ReBound(0, BoundVar(1)));
    assert_eq!(
        envs.get(canonical.value.param_env),
        &[Clause::TypeOutlives(env_ref, bound_r)]
    );
    let pred_ref = tcx.tys.intern(TyKind::Ref(
        false,
        bound(&tcx, 0, 0),
        tcx.tys.intern_region(RegionKind::ReBound(0, BoundVar(2))),
    ));
    assert_eq!(
        canonical.value.predicate,
        Predicate::Clause(Clause::TypeOutlives(pred_ref, bound_r))
    );
    assert_eq!(
        substitute_goal(&tcx.tys, &mut envs, &canonical.value, &originals),
        input
    );
}

#[test]
fn nested_binders_preserve_bound_variables_and_shift_canonical_ones() {
    let prog = Program::new(&std::sync::Arc::new(crate::Session::default()));
    let tcx = Tcx::new();
    let state = crate::tcx::EvalState::new();
    let mut fcx = context(&prog, &tcx, &state);
    let t = fcx.fresh(0);
    let free = fcx.fresh_region();
    let local = tcx.tys.intern_region(RegionKind::ReBound(0, BoundVar(0)));
    let outer = tcx.tys.intern_region(RegionKind::ReBound(1, BoundVar(0)));
    let inner = tcx.tys.intern(TyKind::FnPtr(
        vec![
            tcx.tys.intern(TyKind::Ref(false, t, local)),
            tcx.tys.intern(TyKind::Ref(false, t, outer)),
            tcx.tys.intern(TyKind::Ref(false, t, free)),
            bound(&tcx, 0, 4),
        ],
        t,
        FnHeader::RUST,
        1,
    ));
    let ty = tcx.tys.intern(TyKind::Tuple(vec![
        t,
        tcx.tys.intern(TyKind::FnPtr(vec![inner], t, FnHeader::RUST, 1)),
    ]));
    let mut envs = ParamEnvInterner::new();
    let input = goal(&mut envs, ty);
    let (canonical, originals) = canonicalize_goal(
        &mut fcx,
        &tcx.tys,
        &mut envs,
        &input,
        CanonicalizeMode::Input,
    );
    assert_eq!(canonical.variables.len(), 2);
    assert_eq!(
        substitute_goal(&tcx.tys, &mut envs, &canonical.value, &originals),
        input
    );
    let target_state = crate::tcx::EvalState::new();
    let mut target = context(&prog, &tcx, &target_state);
    let (instantiated, _) =
        instantiate_canonical(&mut target, &tcx.tys, &mut envs, &canonical).unwrap();
    let (again, _) = canonicalize_goal(
        &mut target,
        &tcx.tys,
        &mut envs,
        &instantiated,
        CanonicalizeMode::Input,
    );
    assert_eq!(canonical, again);
}

#[test]
fn response_universes_are_relative_and_freshly_instantiated() {
    let prog = Program::new(&std::sync::Arc::new(crate::Session::default()));
    let tcx = Tcx::new();
    let state = crate::tcx::EvalState::new();
    let mut fcx = context(&prog, &tcx, &state);
    let input_u = fcx.create_next_universe();
    let input_ty = fcx.fresh_in_universe(0, input_u);
    let new_u = fcx.create_next_universe();
    let output_ty = fcx.fresh_in_universe(0, new_u);
    let region = fcx.instantiate_var(CanonicalVarKind::Region(new_u));
    let p = Placeholder {
        universe: new_u,
        var: BoundVar(9),
    };
    let pt = fcx.instantiate_var(CanonicalVarKind::PlaceholderTy(p));
    let pr = fcx.instantiate_var(CanonicalVarKind::PlaceholderRegion(p));
    let pc = fcx.instantiate_var(CanonicalVarKind::PlaceholderConst(p));
    let values = CanonicalVarValues {
        values: vec![
            GenericArg::Ty(input_ty),
            GenericArg::Ty(output_ty),
            region,
            pt,
            pr,
            pc,
        ],
    };
    let canonical = canonicalize_response_values(&mut fcx, &tcx.tys, &values, input_u);
    assert_eq!(canonical.max_universe, UniverseIndex(1));
    assert_eq!(canonical.variables[0].universe(), UniverseIndex::ROOT);
    for kind in &canonical.variables[1..] {
        assert_eq!(kind.universe(), UniverseIndex(1));
    }
    assert_eq!(
        canonical.variables[4],
        CanonicalVarKind::PlaceholderRegion(Placeholder {
            universe: UniverseIndex(1),
            var: BoundVar(9)
        })
    );
    let target_state = crate::tcx::EvalState::new();
    let mut target = context(&prog, &tcx, &target_state);
    let target_input = target.create_next_universe();
    let (instantiated, _) =
        instantiate_canonical_values(&mut target, &tcx.tys, &canonical).unwrap();
    assert_eq!(target.universe(), UniverseIndex(2));
    let again = canonicalize_response_values(&mut target, &tcx.tys, &instantiated, target_input);
    assert_eq!(canonical, again);
}

#[test]
fn binding_minimizes_root_universe_and_rollback_restores_it() {
    let prog = Program::new(&std::sync::Arc::new(crate::Session::default()));
    let tcx = Tcx::new();
    let state = crate::tcx::EvalState::new();
    let mut fcx = context(&prog, &tcx, &state);
    let low = fcx.fresh(0);
    let u = fcx.create_next_universe();
    let high = fcx.fresh_in_universe(0, u);
    let mark = fcx.snapshot();
    assert!(fcx.bind(vid(&tcx, low), high));
    assert_eq!(
        fcx.ty_variable(vid(&tcx, high)).universe,
        UniverseIndex::ROOT
    );
    assert_eq!(fcx.ty_variable(vid(&tcx, low)).root, vid(&tcx, high));
    fcx.rollback(mark);
    assert_eq!(fcx.ty_variable(vid(&tcx, high)).universe, u);
    assert_eq!(fcx.ty_variable(vid(&tcx, low)).root, vid(&tcx, low));
    let int = fcx.fresh(1);
    let mark = fcx.snapshot();
    assert!(fcx.bind(vid(&tcx, int), high));
    assert_eq!(fcx.ty_variable(vid(&tcx, high)).kind, TyVariableKind::Int);
    assert_eq!(
        fcx.ty_variable(vid(&tcx, high)).universe,
        UniverseIndex::ROOT
    );
    fcx.rollback(mark);
    assert_eq!(fcx.ty_variable(vid(&tcx, high)).universe, u);
    assert_eq!(
        fcx.ty_variable(vid(&tcx, high)).kind,
        TyVariableKind::General
    );
    assert_eq!(fcx.universe(), u);
}

#[test]
fn nontrivial_sub_roots_are_rejected_before_allocation() {
    let prog = Program::new(&std::sync::Arc::new(crate::Session::default()));
    let tcx = Tcx::new();
    let state = crate::tcx::EvalState::new();
    let mut fcx = context(&prog, &tcx, &state);
    let kind = CanonicalVarKind::Ty {
        universe: UniverseIndex(1),
        kind: TyVariableKind::General,
        sub_root: BoundVar(0),
    };
    let canonical = Canonical {
        value: CanonicalVarValues::default(),
        max_universe: UniverseIndex(1),
        variables: vec![kind, kind],
    };
    assert_eq!(
        instantiate_canonical_values(&mut fcx, &tcx.tys, &canonical),
        Err(InstantiateError::NontrivialSubRoot)
    );
    assert_eq!(fcx.universe(), UniverseIndex::ROOT);
    assert!(fcx.vars.is_empty());
}

fn declarations() -> (Program, Tcx) {
    declarations_source(b"#![no_std]\nstruct S<T, const N: usize>(T); trait Tr<T, const N: usize> { type A; } fn f<T, const N: usize>() {}")
}

fn declarations_source(source: &[u8]) -> (Program, Tcx) {
    let dir = std::env::temp_dir().join(format!(
        "relax-canonical-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ));
    std::fs::create_dir(&dir).unwrap();
    let path = dir.join("lib.rs");
    std::fs::write(&path, source).unwrap();
    let mut prog = Program::new(&std::sync::Arc::new(crate::Session::default()));
    prog.load_crate(
        "canonical",
        path.to_str().unwrap(),
        2021,
        crate::cfg::CfgSet::host(&prog.session, &[]),
        Vec::new(),
    )
    .unwrap();
    let mut tcx = Tcx::new();
    tcx.collect(&prog);
    std::fs::remove_file(&path).unwrap();
    std::fs::remove_dir(&dir).unwrap();
    assert!(tcx.errors.is_empty(), "{:?}", tcx.errors);
    (prog, tcx)
}

fn named(prog: &Program, name: &str) -> DefId {
    for (i, _) in prog.defs.iter().enumerate() {
        let d = DefId(i as u32);
        if prog.name(d) == name {
            return d;
        }
    }
    panic!("missing declaration {name}")
}

#[test]
fn const_positions_cover_arrays_generic_args_traits_and_dyn_binders() {
    let (prog, tcx) = declarations();
    let state = crate::tcx::EvalState::new();
    let mut fcx = context(&prog, &tcx, &state);
    let t = fcx.fresh(0);
    let n = fcx.fresh(0);
    let param = tcx.tys.intern(TyKind::Param(4));
    let s = named(&prog, "S");
    let tr = named(&prog, "Tr");
    let assoc = named(&prog, "A");
    let f = named(&prog, "f");
    assert!(fcx.is_const_arg(s, 1));
    assert!(fcx.is_const_arg(tr, 2));
    assert!(fcx.is_const_arg(assoc, 2));
    assert!(fcx.is_const_arg(f, 1));
    let args = RegionArgsId::EMPTY;
    let array = tcx.tys.mk_array(t, n);
    let adt = tcx.tys.intern(TyKind::Adt(s, vec![t, n], args));
    let assoc_ty = tcx.tys.intern(TyKind::Assoc(assoc, vec![t, t, n], args));
    let fn_ty = tcx.tys.intern(TyKind::FnDef(f, vec![t, param], args));
    let obj = tcx.tys.intern(TyKind::Dyn(
        tr,
        crate::types::DynList::from(vec![t, n]),
        crate::types::DynList::from(vec![(assoc, t, 0)]),
        args,
        RegionId::ERASED,
        0,
     Default::default()));
    let ty = tcx
        .tys
        .intern(TyKind::Tuple(vec![array, adt, assoc_ty, fn_ty, obj]));
    let mut envs = ParamEnvInterner::new();
    let input = Goal {
        param_env: envs.intern(vec![Clause::Trait(TraitPredicate {
            trait_ref: TraitRef {
                def: tr,
                args: vec![t, t, n],
            },
            polarity: PredicatePolarity::Positive,
        })]),
        predicate: Predicate::Clause(Clause::WellFormed(Term::Ty(ty))),
    };
    let (canonical, originals) = canonicalize_goal(
        &mut fcx,
        &tcx.tys,
        &mut envs,
        &input,
        CanonicalizeMode::Input,
    );
    assert_eq!(
        originals.values,
        vec![
            GenericArg::Ty(t),
            GenericArg::Const(n),
            GenericArg::Const(param),
            GenericArg::Region(RegionId::ERASED)
        ]
    );
    assert_eq!(
        canonical.variables[1],
        CanonicalVarKind::Const(UniverseIndex::ROOT)
    );
    assert_eq!(
        canonical.variables[2],
        CanonicalVarKind::PlaceholderConst(Placeholder {
            universe: UniverseIndex::ROOT,
            var: BoundVar(2)
        })
    );
    assert_eq!(
        substitute_goal(&tcx.tys, &mut envs, &canonical.value, &originals),
        input
    );
    let target_state = crate::tcx::EvalState::new();
    let mut target = context(&prog, &tcx, &target_state);
    let (instantiated, values) =
        instantiate_canonical(&mut target, &tcx.tys, &mut envs, &canonical).unwrap();
    let GenericArg::Const(fresh_n) = values.values[1] else {
        panic!()
    };
    assert!(target.bind(vid(&tcx, fresh_n), tcx.tys.intern(TyKind::ConstVal(7))));
    let (answer, _) = canonicalize_goal(
        &mut target,
        &tcx.tys,
        &mut envs,
        &instantiated,
        CanonicalizeMode::Response {
            max_input_universe: UniverseIndex::ROOT,
        },
    );
    assert_eq!(answer.variables.len(), 3);
    let Predicate::Clause(Clause::WellFormed(Term::Ty(ty))) = answer.value.predicate else {
        panic!()
    };
    let TyKind::Tuple(fields) = tcx.tys.kind(ty) else {
        panic!()
    };
    assert!(matches!(tcx.tys.kind(fields[0]), TyKind::Array(_, 7)));
}

#[test]
fn const_and_type_identity_tags_and_literal_lengths_survive() {
    let prog = Program::new(&std::sync::Arc::new(crate::Session::default()));
    let tcx = Tcx::new();
    let state = crate::tcx::EvalState::new();
    let mut fcx = context(&prog, &tcx, &state);
    let param = tcx.tys.intern(TyKind::Param(0));
    let ty = tcx.tys.mk_array(param, param);
    let literal = tcx.tys.intern(TyKind::Array(tcx.tys.unit, u64::MAX));
    let ty = tcx.tys.intern(TyKind::Tuple(vec![ty, literal]));
    let mut envs = ParamEnvInterner::new();
    let input = goal(&mut envs, ty);
    let (canonical, originals) = canonicalize_goal(
        &mut fcx,
        &tcx.tys,
        &mut envs,
        &input,
        CanonicalizeMode::Input,
    );
    assert_eq!(
        originals.values,
        vec![GenericArg::Ty(param), GenericArg::Const(param)]
    );
    assert!(matches!(
        canonical.variables[0],
        CanonicalVarKind::PlaceholderTy(_)
    ));
    assert!(matches!(
        canonical.variables[1],
        CanonicalVarKind::PlaceholderConst(_)
    ));
    assert_eq!(
        substitute_goal(&tcx.tys, &mut envs, &canonical.value, &originals),
        input
    );
}

#[test]
fn free_region_kinds_round_trip_and_response_rigid_regions_remain() {
    use crate::types::{LateParamKind, RegionScope};
    let prog = Program::new(&std::sync::Arc::new(crate::Session::default()));
    let tcx = Tcx::new();
    let state = crate::tcx::EvalState::new();
    let mut fcx = context(&prog, &tcx, &state);
    let u = fcx.create_next_universe();
    let mut references = Vec::new();
    let kinds = [
        RegionKind::ReEarlyParam(0),
        RegionKind::ReLateParam(RegionScope::Item(DefId(0)), LateParamKind::Anon(0)),
        RegionKind::RePlaceholder {
            universe: u,
            var: BoundVar(1),
        },
        RegionKind::ReErased,
        RegionKind::ReError,
        RegionKind::ReStatic,
    ];
    for kind in kinds {
        references.push(tcx.tys.intern(TyKind::Ref(
            false,
            tcx.tys.bool_,
            tcx.tys.intern_region(kind),
        )));
    }
    let ty = tcx.tys.intern(TyKind::Tuple(references));
    let mut envs = ParamEnvInterner::new();
    let input = goal(&mut envs, ty);
    let (canonical, originals) = canonicalize_goal(
        &mut fcx,
        &tcx.tys,
        &mut envs,
        &input,
        CanonicalizeMode::Input,
    );
    assert_eq!(canonical.variables.len(), kinds.len());
    for kind in &canonical.variables {
        assert!(matches!(kind, CanonicalVarKind::PlaceholderRegion(_)));
    }
    assert_eq!(
        substitute_goal(&tcx.tys, &mut envs, &canonical.value, &originals),
        input
    );
    let values = CanonicalVarValues {
        values: vec![
            GenericArg::Region(RegionId::ERASED),
            GenericArg::Region(tcx.tys.intern_region(RegionKind::ReStatic)),
            GenericArg::Region(tcx.tys.intern_region(RegionKind::ReError)),
        ],
    };
    let response = canonicalize_response_values(&mut fcx, &tcx.tys, &values, u);
    assert!(response.variables.is_empty());
    assert_eq!(response.value, values);
}

#[test]
fn pending_selection_goals_rollback_with_probe() {
    let prog = Program::new(&std::sync::Arc::new(crate::Session::default()));
    let tcx = Tcx::new();
    let state = crate::tcx::EvalState::new();
    let mut fcx = context(&prog, &tcx, &state);
    let goal = Goal { param_env: crate::solve::goal::ParamEnvId(0), predicate: Predicate::Ambiguous };
    let mark = fcx.snapshot();
    fcx.register_goal(goal.clone(), 17);
    assert_eq!(fcx.pending_goals.len(), 1);
    assert_eq!(fcx.pending_goals[0].goal, goal);
    assert_eq!(fcx.pending_goals[0].lo, 17);
    fcx.rollback(mark);
    assert!(fcx.pending_goals.is_empty());
}

#[test]
fn solver_relations_transfer_once_and_preserve_probe_rollback() {
    let prog = Program::new(&std::sync::Arc::new(crate::Session::default()));
    let tcx = Tcx::new();
    let state = crate::tcx::EvalState::new();
    let mut fcx = context(&prog, &tcx, &state);
    let outer = InferDelegate::snapshot(&fcx);
    fcx.defer_proj_eq(tcx.tys.bool_, tcx.tys.u32_);
    let inner = InferDelegate::snapshot(&fcx);
    let var = fcx.fresh(0);
    assert!(fcx.unify(var, tcx.tys.bool_));
    fcx.defer_proj_eq(var, tcx.tys.u32_);
    let goal = Goal { param_env: crate::solve::goal::ParamEnvId(0), predicate: Predicate::Ambiguous };
    fcx.push_pending_goal(goal, 17, Certainty::Maybe(MaybeCause::Ambiguity));
    assert_eq!(fcx.take_relations_since(inner), vec![(var, tcx.tys.u32_)]);
    assert!(fcx.take_relations_since(inner).is_empty());
    assert_eq!(fcx.projection_relations.len(), 1);
    InferDelegate::rollback(&mut fcx, inner);
    assert_eq!(fcx.shallow_vars(var), var);
    assert!(fcx.pending_goals.is_empty());
    assert_eq!(fcx.projection_relations.len(), 1);
    InferDelegate::rollback(&mut fcx, outer);
    assert!(fcx.projection_relations.is_empty());
}

#[test]
fn pending_selection_waits_for_inputs_and_closure_publication() {
    let (prog, tcx) = declarations_source(br#"#![no_std]
        #[lang = "fn_mut"] trait FnMut<A> {}
        trait Tr {}
        struct W<T>(T);
        impl<T: FnMut<()>> Tr for W<T> {}
        impl Tr for bool {}
    "#);
    let state = crate::tcx::EvalState::new();
    let mut fcx = context(&prog, &tcx, &state);
    let tr = named(&prog, "Tr");
    let var = fcx.fresh(0);
    let goal = crate::solve::select::trait_goal(&fcx.cx, tr, var, &[]);
    fcx.register_goal(goal.clone(), 17);
    fcx.register_goal(goal, 19);
    assert_eq!(fcx.pending_goals.len(), 1);
    assert!(fcx.unify(var, tcx.tys.bool_));
    fcx.retry_goals(false);
    assert!(fcx.pending_goals.is_empty());

    let sig = tcx.tys.intern(TyKind::FnPtr(vec![], tcx.tys.unit, crate::types::FnHeader::RUST, 0));
    let closure = tcx.tys.intern(TyKind::Closure(0, 0, sig, tcx.tys.unit, tcx.tys.unit));
    let wrapped = tcx.tys.intern(TyKind::Adt(named(&prog, "W"), vec![closure], RegionArgsId::EMPTY));
    let goal = crate::solve::select::trait_goal(&fcx.cx, tr, wrapped, &[]);
    fcx.register_goal(goal, 23);
    assert_eq!(fcx.pending_goals.len(), 1);
    let allocated = fcx.vars.len();
    for _ in 0..8 { fcx.retry_goals(false); }
    assert_eq!(fcx.vars.len(), allocated, "unchanged nested impl must not be reinstantiated");
    assert_eq!(fcx.pending_goals.len(), 1, "concrete ambiguity must remain pending");
    tcx.closure_capture_types.insert((0, 0, tcx.tys.unit, tcx.collect_epoch.load(std::sync::atomic::Ordering::Relaxed)), crate::upvar::ClosureCaptureTypes { kind: crate::upvar::ClosureKind::Fn, is_copy: true, upvars: tcx.tys.unit });
    tcx.trait_input_revision.fetch_add(1, std::sync::atomic::Ordering::Release);
    fcx.retry_goals(false);
    assert!(fcx.pending_goals.is_empty());
    assert!(fcx.b.errors.is_empty());
}

#[test]
fn pending_opaque_requests_check_definitions_after_selection() {
    let (prog, tcx) = declarations_source(b"#![no_std] auto trait Auto {} trait Bound {} impl Bound for u32 {} fn hidden() -> impl Bound { 1u32 }");
    let state = crate::tcx::EvalState::new();
    let mut fcx = context(&prog, &tcx, &state);
    let ty = tcx.fn_item_sig(&prog, named(&prog, "hidden")).unwrap().ret;
    let goal = crate::solve::select::trait_goal(&fcx.cx, named(&prog, "Auto"), ty, &[]);
    fcx.register_goal(goal, 0);
    assert_eq!(fcx.pending_goals.len(), 1);
    assert!(tcx.opaque_hidden.get(&ty).is_none());
    fcx.retry_goals(true);
    assert_eq!(tcx.opaque_hidden.get(&ty), Some(tcx.tys.u32_));
    assert!(fcx.pending_goals.is_empty());
    assert!(fcx.b.errors.is_empty(), "{:?}", fcx.b.errors);
    assert!(state.typeck_inprog.borrow().is_empty());
}

#[test]
fn pending_opaque_active_definition_stalls_until_publication() {
    let (prog, tcx) = declarations_source(b"#![no_std] auto trait Auto {} trait Bound {} impl Bound for u32 {} fn hidden() -> impl Bound { 1u32 }");
    let state = crate::tcx::EvalState::new();
    let mut fcx = context(&prog, &tcx, &state);
    let def = named(&prog, "hidden");
    let ty = tcx.fn_item_sig(&prog, def).unwrap().ret;
    state.typeck_inprog.borrow_mut().push(def);
    let goal = crate::solve::select::trait_goal(&fcx.cx, named(&prog, "Auto"), ty, &[]);
    fcx.register_goal(goal, 0);
    let revision = tcx.trait_input_revision.load(std::sync::atomic::Ordering::Acquire);
    for _ in 0..8 { fcx.retry_goals(false); }
    assert!(tcx.opaque_hidden.get(&ty).is_none());
    assert_eq!(fcx.pending_goals.len(), 1);
    assert_eq!(tcx.trait_input_revision.load(std::sync::atomic::Ordering::Acquire), revision);
    let body = check_fn_uncached(&fcx.cx, &prog, &tcx, def, &[]);
    assert!(body.errors.is_empty(), "{:?}", body.errors);
    state.typeck_inprog.borrow_mut().pop();
    fcx.retry_goals(true);
    assert!(fcx.pending_goals.is_empty());
    assert!(fcx.b.errors.is_empty(), "{:?}", fcx.b.errors);
}

#[test]
fn final_fulfillment_reports_overflow_at_obligation_site() {
    let (prog, tcx) = declarations_source(b"#![no_std] fn f() {}");
    let state = crate::tcx::EvalState::new();
    let mut fcx = context(&prog, &tcx, &state);
    let goal = Goal { param_env: crate::solve::goal::ParamEnvId(0), predicate: Predicate::Ambiguous };
    let revision = tcx.trait_input_revision.load(std::sync::atomic::Ordering::Acquire);
    fcx.push_pending(PendingGoal { goal: goal.clone(), lo: 0, certainty: Certainty::overflow(true), stalled: Some((goal, revision)) });
    fcx.retry_goals(true);
    assert_eq!(fcx.b.errors.len(), 1);
    assert!(fcx.b.errors[0].contains("E0275: overflow evaluating the requirement"), "{:?}", fcx.b.errors);
}
