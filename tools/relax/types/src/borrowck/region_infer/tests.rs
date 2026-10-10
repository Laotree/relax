use super::*;
use crate::borrowck::constraints::*;
use crate::borrowck::handle_placeholders::*;
use crate::borrowck::type_check::free_region_relations::UniversalRegionRelations;
use crate::borrowck::universal_regions::{UniversalRegions, RegionClassification as Class};
use crate::types::{BoundVar, RegionKind, Types, TyKind};
use values::LivenessValues;

fn definition(origin: NllRegionVariableOrigin, universe: u32) -> RegionDefinition {
    RegionDefinition { origin, universe: UniverseIndex(universe), external_name: None }
}
fn constraint(sup: usize, sub: usize, category: ConstraintCategory) -> OutlivesConstraint {
    OutlivesConstraint { sup, sub, category, location: None, span: crate::mir::Span { file: 0, lo: sup as u32, hi: sub as u32 }, from_closure: false }
}
fn constraints(edges: &[(usize, usize)]) -> OutlivesConstraintSet {
    let mut set = OutlivesConstraintSet::default();
    for &(a,b) in edges { set.push(constraint(a,b,ConstraintCategory::Assignment)); }
    set
}
fn solve(definitions: Vec<RegionDefinition>, edges: OutlivesConstraintSet, universals: &[(usize,Class)], known: &[(usize,usize)], live: LivenessValues, points: usize) -> RegionInferenceContext {
    let relations = UniversalRegionRelations::create(UniversalRegions::new(0,None,universals.to_vec()), definitions.len(),known);
    let lowered = compute_sccs_applying_placeholder_outlives_constraints(definitions,edges,0);
    RegionInferenceContext::solve(&crate::tcx::Tcx::new(),&crate::program::Program::new(&std::sync::Arc::new(crate::Session::default())),lowered,relations,live,points,&[],false)
}
#[test]
fn annotated_sccs_and_values_match_reachability() {
    // Cross-check different cyclic graphs against an independent closure oracle.
    let n = 12;
    for seed in 0..32 {
        let mut bits = seed + 1u64;
        let mut edges = vec![];
        let mut reach = vec![vec![false;n];n];
        for a in 0..n { for b in 0..n {
            bits = bits.wrapping_mul(6364136223846793005).wrapping_add(1);
            if a == 0 || bits >> 61 == 0 { edges.push((a,b)); reach[a][b] = true; }
        } reach[a][a] = true; }
        for k in 0..n { for a in 0..n { for b in 0..n { reach[a][b] |= reach[a][k] && reach[k][b]; } } }
        let mut defs = vec![definition(NllRegionVariableOrigin::Existential,0);n];
        defs[0].origin = NllRegionVariableOrigin::FreeRegion;
        let mut live = LivenessValues::new(n,n);
        for r in 0..n { live.add_point(r,r); }
        let cx = solve(defs,constraints(&edges),&[(0,Class::Global)],&[],live,n);
        for a in 0..n { for b in 0..n {
            assert_eq!(cx.region_contains_point(a,b),reach[a][b],"seed {seed}, {a}:{b}");
            assert_eq!(cx.constraint_sccs.scc(a)==cx.constraint_sccs.scc(b),reach[a][b] && reach[b][a]);
        } }
    }
}
#[test]
fn placeholder_leak_is_rewritten_and_blame_uses_original_path() {
    let tys = Types::new();
    let p = tys.intern_region(RegionKind::RePlaceholder { universe: UniverseIndex(1), var: BoundVar(0) });
    let defs = vec![definition(NllRegionVariableOrigin::FreeRegion,0), definition(NllRegionVariableOrigin::Existential,0),definition(NllRegionVariableOrigin::Placeholder(p),1)];
    let lowered = compute_sccs_applying_placeholder_outlives_constraints(defs,constraints(&[(1,2)]),0);
    assert_eq!(lowered.constraint_sccs.scc(1),lowered.constraint_sccs.scc(0));
    assert!(lowered.outlives_constraints.outlives.iter().any(|c| c.sup == 1 && c.sub == 0 && c.category == ConstraintCategory::OutlivesUnnameablePlaceholder(2)));
    let defs = vec![definition(NllRegionVariableOrigin::FreeRegion,0), definition(NllRegionVariableOrigin::Placeholder(p),1)];
    let cx = solve(defs,constraints(&[(1,0)]),&[(0,Class::Global)],&[],LivenessValues::new(2,0),0);
    assert!(cx.errors.iter().any(|e| matches!(e, RegionErrorKind::PlaceholderOutlivesIllegalRegion { longer_fr:1,.. })));
}
#[test]
fn nameable_placeholder_is_not_a_free_region_or_a_point() {
    let tys = Types::new();
    let p = tys.intern_region(RegionKind::RePlaceholder { universe: UniverseIndex(1),var: BoundVar(0) });
    let defs = vec![definition(NllRegionVariableOrigin::FreeRegion,0),definition(NllRegionVariableOrigin::Existential,1),definition(NllRegionVariableOrigin::Placeholder(p),1)];
    let cx = solve(defs,constraints(&[(1,2)]),&[(0,Class::Global)],&[],LivenessValues::new(3,1),1);
    assert_ne!(cx.constraint_sccs.scc(0),cx.constraint_sccs.scc(1));
    assert_eq!(cx.universal_regions_outlived_by(1).count(),0);
    assert!(!cx.region_contains_point(1,0));
    assert!(cx.errors.is_empty());
}
#[test]
fn blame_follows_one_shortest_path_not_a_return_on_another_branch() {
    let defs = vec![definition(NllRegionVariableOrigin::FreeRegion,0);4];
    let mut edges = constraints(&[(1,2),(1,3)]);
    edges.push(constraint(3,2,ConstraintCategory::Return(ReturnConstraint::Normal)));
    let cx = solve(defs,edges,&[(0,Class::Global),(1,Class::Local),(2,Class::Local),(3,Class::Local)],&[],LivenessValues::new(4,0),0);
    let blame = cx.best_blame_constraint(&crate::tcx::Tcx::new(),1,2).unwrap();
    assert_eq!((blame.sup,blame.sub),(1,2));
}
#[test]
fn non_local_bounds_keep_incomparable_parents() {
    let u = UniversalRegions::new(0,Some(4), vec![(0,Class::Global),(1,Class::External),(2,Class::External),(3,Class::Local),(4,Class::Local)]);
    let relations = UniversalRegionRelations::create(u,5,&[(1,3),(2,3)]);
    let mut upper = relations.non_local_upper_bounds(3); upper.sort();
    assert_eq!(upper,vec![1,2]);
    assert!(relations.non_local_lower_bounds(3).is_empty());
}
#[test]
fn opaque_member_uses_unique_smallest_choice() {
    let tcx = crate::tcx::Tcx::new();
    let tys = &tcx.tys;
    let a = tys.intern_region(RegionKind::ReEarlyParam(0));
    let mut defs = vec![definition(NllRegionVariableOrigin::FreeRegion,0);3];
    defs[0].external_name = Some(tys.intern_region(RegionKind::ReStatic)); defs[1].external_name = Some(a);
    defs[2].origin = NllRegionVariableOrigin::Existential;
    let relations = UniversalRegionRelations::create(UniversalRegions::new(0,None,vec![(0,Class::Global),(1,Class::Local)]),3,&[]);
    let r = tys.intern_region(RegionKind::ReVar(2));
    let ty = tys.intern(crate::types::TyKind::Ref(false,tys.intern(crate::types::TyKind::Bool),r));
    let d = crate::program::DefId(0);
    let uses = vec![opaque_types::DefiningUse { def_id:d,hidden_type:ty,arg_regions:vec![0,1] }];
    let (hidden,errors) = opaque_types::compute_definition_site_hidden_types(&tcx,&crate::program::Program::new(&std::sync::Arc::new(crate::Session::default())),defs,&relations,constraints(&[(1,2)]),&uses);
    assert!(errors.is_empty());
    assert!(matches!(tys.kind(hidden[0].1),crate::types::TyKind::Ref(_,_,region) if *region == a));
}

#[test]
fn erased_signature_occurrences_get_distinct_query_placeholders() {
    let tcx = crate::tcx::Tcx::new();
    let b = tcx.tys.intern(crate::types::TyKind::Bool);
    let erased = tcx.tys.intern(crate::types::TyKind::Ref(false,b,RegionId::ERASED));
    let bound = tcx.tys.intern_region(RegionKind::ReBound(0,BoundVar(0)));
    let nested = tcx.tys.intern(crate::types::TyKind::FnPtr(vec![tcx.tys.intern(crate::types::TyKind::Ref(false,b,bound))],erased,crate::types::FnHeader::RUST,1));
    let query = crate::borrowck::implied_bounds::replace_erased_regions_with_placeholders(&tcx,&[erased,erased,nested]);
    assert_ne!(query[0],query[1]);
    let regions = crate::borrowck::implied_bounds::implied_bounds_query_var_values(&tcx,&query,|r| matches!(tcx.tys.region_kind(r),RegionKind::RePlaceholder { .. }));
    assert_eq!(regions.len(),3);
    assert!(regions.iter().enumerate().all(|(i,&r)| matches!(tcx.tys.region_kind(r),RegionKind::RePlaceholder { universe:UniverseIndex::ROOT,var } if var.0 == i as u32)));
    let crate::types::TyKind::FnPtr(ps,_,_,_) = tcx.tys.kind(query[2]) else { panic!() };
    assert!(matches!(tcx.tys.kind(ps[0]),crate::types::TyKind::Ref(_,_,r) if *r == bound));
}

#[test]
fn conditional_type_tests_match_binders_and_scc_representatives() {
    let tcx = crate::tcx::Tcx::new();
    let tys = &tcx.tys;
    let b = tys.intern(TyKind::Bool);
    let region = |v| tys.intern_region(RegionKind::ReVar(v));
    let bound = tys.intern_region(RegionKind::ReBound(0,BoundVar(0)));
    let pattern = tys.intern(TyKind::Ref(false,b,bound));
    let subject = tys.intern(TyKind::Ref(false,b,region(2)));
    let span = Span::default();
    let tests = vec![
        TypeTest { generic_kind:subject,lower_bound:1,span,verify_bound:VerifyBound::IfEq { ty:pattern,bound } },
        TypeTest { generic_kind:subject,lower_bound:1,span,verify_bound:VerifyBound::IfEq { ty:tys.intern(TyKind::Ref(false,b,region(1))),bound:region(2) } },
        TypeTest { generic_kind:tys.intern(TyKind::Tuple(vec![subject,tys.intern(TyKind::Ref(false,b,region(0)))])),lower_bound:1,span,
            verify_bound:VerifyBound::IfEq { ty:tys.intern(TyKind::Tuple(vec![pattern,pattern])),bound } },
    ];
    let defs = vec![definition(NllRegionVariableOrigin::FreeRegion,0);3];
    let relations = UniversalRegionRelations::create(UniversalRegions::new(0,None,vec![(0,Class::Global),(1,Class::Local),(2,Class::Local)]),3,&[(1,2),(2,1)]);
    let lowered = compute_sccs_applying_placeholder_outlives_constraints(defs,constraints(&[(1,2),(2,1)]),0);
    let cx = RegionInferenceContext::solve(&tcx,&crate::program::Program::new(&std::sync::Arc::new(crate::Session::default())),lowered,relations,LivenessValues::new(3,0),0,&tests,false);
    assert!(matches!(cx.errors.as_slice(),[RegionErrorKind::TypeTest { test:2 }]));
}

#[test]
fn closure_type_tests_promote_external_subjects_and_requirements() {
    let tcx = crate::tcx::Tcx::new();
    let p = tcx.tys.intern_region(RegionKind::RePlaceholder { universe:UniverseIndex(1),var:BoundVar(0) });
    let subject = tcx.tys.intern(TyKind::Param(0));
    let defs = vec![definition(NllRegionVariableOrigin::FreeRegion,0),definition(NllRegionVariableOrigin::FreeRegion,0),
        definition(NllRegionVariableOrigin::Existential,1),definition(NllRegionVariableOrigin::Placeholder(p),1)];
    let relations = UniversalRegionRelations::create(UniversalRegions::new(0,None,vec![(0,Class::Global),(1,Class::External)]),4,&[]);
    let tests = vec![TypeTest { generic_kind:subject,lower_bound:1,span:Span::default(),verify_bound:VerifyBound::IsEmpty },
        TypeTest { generic_kind:subject,lower_bound:2,span:Span::default(),verify_bound:VerifyBound::IsEmpty }];
    let lowered = compute_sccs_applying_placeholder_outlives_constraints(defs,constraints(&[(2,3)]),0);
    let cx = RegionInferenceContext::solve(&tcx,&crate::program::Program::new(&std::sync::Arc::new(crate::Session::default())),lowered,relations,LivenessValues::new(4,0),0,&tests,true);
    assert!(cx.errors.is_empty());
    assert_eq!(cx.propagated_type_requirements.iter().map(|r| (r.subject,r.outlived_free_region)).collect::<Vec<_>>(),vec![(subject,1),(subject,0)]);
}

#[test]
fn failed_type_tests_deduplicate_and_prefer_static_at_the_same_span() {
    let tcx = crate::tcx::Tcx::new();
    let subject = tcx.tys.intern(TyKind::Param(0));
    let tests: Vec<_> = [1,0,0].map(|lower_bound| TypeTest { generic_kind:subject,lower_bound,span:Span::default(),verify_bound:VerifyBound::IsEmpty }).into();
    let defs = vec![definition(NllRegionVariableOrigin::FreeRegion,0);2];
    let relations = UniversalRegionRelations::create(UniversalRegions::new(0,None,vec![(0,Class::Global),(1,Class::Local)]),2,&[]);
    let lowered = compute_sccs_applying_placeholder_outlives_constraints(defs,constraints(&[]),0);
    let cx = RegionInferenceContext::solve(&tcx,&crate::program::Program::new(&std::sync::Arc::new(crate::Session::default())),lowered,relations,LivenessValues::new(2,0),0,&tests,false);
    assert!(matches!(cx.errors.as_slice(),[RegionErrorKind::TypeTest { test:1 }]));
}

#[test]
fn opaque_members_exclude_parent_closure_arguments() {
    let tcx = crate::tcx::Tcx::new();
    let tys = &tcx.tys;
    let named = tys.intern_region(RegionKind::ReEarlyParam(0));
    let mut defs = vec![definition(NllRegionVariableOrigin::Existential,0);4];
    defs[0] = definition(NllRegionVariableOrigin::FreeRegion,0); defs[0].external_name = Some(tys.intern_region(RegionKind::ReStatic));
    defs[1] = definition(NllRegionVariableOrigin::FreeRegion,0); defs[1].external_name = Some(named);
    let relations = UniversalRegionRelations::create(UniversalRegions::new(0,None,vec![(0,Class::Global),(1,Class::Local)]),4,&[]);
    let unit = tys.intern(TyKind::Tuple(vec![]));
    let member = tys.intern(TyKind::Ref(false,unit,tys.intern_region(RegionKind::ReVar(2))));
    let owner = tys.intern(TyKind::FnDef(crate::program::DefId(2),vec![],tys.intern_region_args(&[tys.intern_region(RegionKind::ReVar(3))])));
    let signature = tys.intern(TyKind::FnPtr(vec![],unit,crate::types::FnHeader::RUST,0));
    let hidden_type = tys.intern(TyKind::Closure(0,0,signature,member,owner));
    let uses = vec![opaque_types::DefiningUse { def_id:crate::program::DefId(0),hidden_type,arg_regions:vec![0,1] }];
    let (hidden,errors) = opaque_types::compute_definition_site_hidden_types(&tcx,&crate::program::Program::new(&std::sync::Arc::new(crate::Session::default())),defs,&relations,constraints(&[(1,2)]),&uses);
    assert!(errors.is_empty());
    let TyKind::Closure(_,_,_,member,owner) = tys.kind(hidden[0].1) else { panic!() };
    assert!(matches!(tys.kind(*member),TyKind::Ref(_,_,r) if *r == named));
    let TyKind::FnDef(_,_,rs) = tys.kind(*owner) else { panic!() };
    assert_eq!(&*tys.region_args(*rs),&[RegionId::ERASED]);
}

// caudit interface witnesses. These tests exercise the typed interfaces directly;
// the live BIR producer is not a substitute for MIR/solver integration.
#[test]
fn v1_if_eq_ignores_bivariant_opaque_arguments() {
    use crate::types::variance::{GenericIndices, V};
    let tcx = crate::tcx::Tcx::new();
    let d = crate::program::DefId(40);
    tcx.opaques.insert((d,0),crate::tcx::OpaqueDecl {
        variances: Some((GenericIndices { lifetimes:vec![0], ..Default::default() },vec![V::Bi])),
        ..Default::default()
    });
    let opaque = |r| tcx.tys.intern(TyKind::Opaque(d,0,vec![],tcx.tys.intern_region_args(&[tcx.tys.intern_region(RegionKind::ReVar(r))])));
    let tests = [TypeTest { generic_kind:opaque(2), lower_bound:1,span:Span::default(),
        verify_bound:VerifyBound::IfEq { ty:opaque(1),bound:tcx.tys.intern_region(RegionKind::ReStatic) } }];
    let run = || {
        let defs = vec![definition(NllRegionVariableOrigin::FreeRegion,0);3];
        let relations = UniversalRegionRelations::create(UniversalRegions::new(0,None,vec![(0,Class::Global),(1,Class::Local),(2,Class::Local)]),3,&[]);
        RegionInferenceContext::solve(&tcx,&crate::program::Program::new(&std::sync::Arc::new(crate::Session::default())),compute_sccs_applying_placeholder_outlives_constraints(defs,constraints(&[]),0),relations,LivenessValues::new(3,1),1,&tests,false)
    };
    assert!(run().errors.is_empty());
    tcx.opaques.insert((d,0),crate::tcx::OpaqueDecl::default());
    assert!(matches!(run().errors.as_slice(),[RegionErrorKind::TypeTest { test:0 }]));
}
fn opaque_witness(tcx: &crate::tcx::Tcx, ty: TyId, universals: usize, edges: &[(usize,usize)]) -> (Vec<(crate::program::DefId,TyId)>,Vec<opaque_types::DeferredOpaqueTypeError>) {
    let defs = (0..universals).map(|i| RegionDefinition {
        external_name:Some(tcx.tys.intern_region(if i == 0 { RegionKind::ReStatic } else { RegionKind::ReEarlyParam(i as u32) })),
        ..definition(NllRegionVariableOrigin::FreeRegion,0)
    }).collect();
    let regions = (0..universals).map(|i| (i,if i == 0 { Class::Global } else { Class::Local })).collect();
    let relations = UniversalRegionRelations::create(UniversalRegions::new(0,None,regions),universals,&[]);
    opaque_types::compute_definition_site_hidden_types(tcx,&crate::program::Program::new(&std::sync::Arc::new(crate::Session::default())),defs,&relations,constraints(edges),&[
        opaque_types::DefiningUse { def_id:crate::program::DefId(0),hidden_type:ty,arg_regions:vec![0,1] }
    ])
}
#[test]
fn v2_nonmember_opaque_argument_is_skipped_and_erased() {
    use crate::types::variance::{GenericIndices,V};
    let tcx = crate::tcx::Tcx::new(); let d = crate::program::DefId(40);
    tcx.opaques.insert((d,0),crate::tcx::OpaqueDecl {
        variances:Some((GenericIndices { lifetimes:vec![0],..Default::default() },vec![V::Bi])),..Default::default()
    });
    let x = tcx.tys.intern_region(RegionKind::ReVar(2));
    let hidden = tcx.tys.intern(TyKind::Opaque(d,0,vec![],tcx.tys.intern_region_args(&[x])));
    let (types,errors) = opaque_witness(&tcx,hidden,3,&[]);
    assert!(errors.is_empty(),"{errors:?}");
    let TyKind::Opaque(_,_,_,rs) = tcx.tys.kind(types[0].1) else { panic!() };
    assert_eq!(&*tcx.tys.region_args(*rs),&[RegionId::ERASED]);
    // A captured occurrence of the same region must still fail.
    let member = tcx.tys.intern(TyKind::Ref(false,tcx.tys.unit,x));
    let tuple = tcx.tys.intern(TyKind::Tuple(vec![hidden,member]));
    assert!(matches!(opaque_witness(&tcx,tuple,3,&[]).1.as_slice(),
        [opaque_types::DeferredOpaqueTypeError::UnexpectedHiddenRegion { member_region:2,.. }]));
}
#[test]
fn v3_opaque_substitution_fails_on_first_unknown_region() {
    let tcx = crate::tcx::Tcx::new();
    let reference = |r| tcx.tys.intern(TyKind::Ref(false,tcx.tys.unit,tcx.tys.intern_region(RegionKind::ReVar(r))));
    let hidden = tcx.tys.intern(TyKind::Tuple(vec![reference(2),reference(3)]));
    let (types,errors) = opaque_witness(&tcx,hidden,4,&[]);
    assert!(types.is_empty());
    assert!(matches!(errors.as_slice(),[opaque_types::DeferredOpaqueTypeError::UnexpectedHiddenRegion { member_region:2,.. }]));
    // A later invalid (non-renumbered) region would panic if folding continued.
    let invalid = tcx.tys.intern(TyKind::Ref(false,tcx.tys.unit,tcx.tys.intern_region(RegionKind::ReEarlyParam(99))));
    let hidden = tcx.tys.intern(TyKind::Tuple(vec![reference(2),invalid]));
    // Test substitution directly: collection intentionally requires all members renumbered.
    opaque_types::test_fail_fast(&tcx,hidden);
}
#[test]
fn v8_relation_insertion_order_selects_nonlocal_representatives() {
    let relations = UniversalRegionRelations::create(UniversalRegions::new(0,None,
        vec![(0,Class::Global),(1,Class::External),(2,Class::External)]),3,&[(2,1),(1,2)]);
    assert_eq!(relations.non_local_lower_bounds(2),[2]);
    assert_eq!(relations.non_local_upper_bounds(2),[1]);
}
#[test]
fn reaudit_implicit_unsizing_to_trait_object_adt_is_blamed_for_static() {
    // N:region_infer/region_context.rs:711-727: interest 1 for an implicit unsizing
    // coercion to an ADT over a trait object, only when blaming `'static` and only
    // without a type annotation on the path.
    let tcx = crate::tcx::Tcx::new();
    let object = tcx.tys.intern(TyKind::Dyn(crate::program::DefId(1),vec![].into(),vec![].into(),tcx.tys.intern_region_args(&[]),RegionId::ERASED,0,vec![].into()));
    let boxed = tcx.tys.intern(TyKind::Adt(crate::program::DefId(2),vec![object],tcx.tys.intern_region_args(&[])));
    let unsize = ConstraintCategory::Cast { is_raw_ptr_dyn_type_cast: false, is_implicit_coercion: true, unsize_to: Some(boxed) };
    let defs = vec![definition(NllRegionVariableOrigin::FreeRegion,0),definition(NllRegionVariableOrigin::FreeRegion,0),
        definition(NllRegionVariableOrigin::Existential,0),definition(NllRegionVariableOrigin::Existential,0)];
    let universals = [(0,Class::Global),(1,Class::Local)];
    let run = |edges: &[(usize,usize,ConstraintCategory)], to: usize| {
        let mut set = OutlivesConstraintSet::default();
        for &(a,b,c) in edges { set.push(constraint(a,b,c)); }
        solve(defs.clone(),set,&universals,&[],LivenessValues::new(4,0),0).best_blame_constraint(&tcx,1,to).unwrap().category
    };
    // Blaming 'static: the unsizing cast wins over the later assignment.
    assert_eq!(run(&[(1,2,unsize),(2,0,ConstraintCategory::Assignment)],0),unsize);
    // A type annotation on the path disables it: the source-most interest-2 constraint.
    let annotation = ConstraintCategory::TypeAnnotation(AnnotationSource::Ascription);
    assert_eq!(run(&[(1,2,unsize),(2,3,annotation),(3,0,ConstraintCategory::Assignment)],0),ConstraintCategory::Assignment);
    // Not blaming 'static: ordinary interest.
    assert_eq!(run(&[(1,2,unsize),(2,3,ConstraintCategory::Assignment)],3),ConstraintCategory::Assignment);
    // An explicit cast (`as`) is not an implicit coercion.
    let explicit = ConstraintCategory::Cast { is_raw_ptr_dyn_type_cast: false, is_implicit_coercion: false, unsize_to: Some(boxed) };
    assert_eq!(run(&[(1,2,explicit),(2,0,ConstraintCategory::Assignment)],0),ConstraintCategory::Assignment);
}
