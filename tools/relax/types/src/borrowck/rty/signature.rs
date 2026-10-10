//! Typed signature-to-BIR producer adapter, retained until C0b.
//! Declaration identity (including unused parameters) precedes I/O traversal.
use super::{Rty, SigTmpl, SK_ELIDED, SK_FRESH, SK_NAMED, SK_PARAM, SR};
use crate::borrowck::implied_bounds::ImpliedBounds;
use crate::program::DefId;
use crate::tcx::{
    outlives::OutlivesPredicate,
};
use crate::types::{LateParamKind, RegionId, RegionKind, RegionScope, TyId, TyKind};

pub use crate::borrowck::universal_regions::{SignatureRegions, UniversalRegion, Identity, RegionClassification as Classification};

/// Read-only projection for the pre-A4c body/call consumers. No AST is consulted.
/// The vectors follow the existing body layout; the authoritative contract is
/// the collected typed signature and its predicates.
pub fn signature_template(rty: &Rty<'_>, d: DefId, args: &[TyId]) -> SigTmpl {
    signature_template_for(rty,d,args,false)
}
fn signature_template_for(rty: &Rty<'_>, d: DefId, args: &[TyId], body: bool) -> SigTmpl {
    let tcx = rty.tx.tcx;
    let u = if body { SignatureRegions::function(tcx,rty.tx.prog,d) } else { SignatureRegions::function_call(tcx,rty.tx.prog,d) };
    let (inputs, output, contract, universals) = if let Some(u) = u.clone() {
        (u.inputs, u.output, u.contract, u.regions)
    } else if let Some(t) = tcx.const_tys.get(&d) {
        (
            Vec::new(),
            *t,
            tcx.const_region_contracts
                .get(&d)
                .cloned()
                .unwrap_or_default(),
            Vec::new(),
        )
    } else {
        return empty();
    };
    let mut p = Projection {
        rty,
        args,
        regions: Vec::new(),
        params: Vec::new(),
        names: Vec::new(),
        kinds: Vec::new(),
    };
    for u in universals {
        if let Identity::Region(_, r) = u.identity {
            p.region(r, Some(&u.name));
        }
    }
    for (name, r) in &contract.regions {
        p.region(*r, Some(name));
    }
    let ins = inputs.iter().map(|t| p.ty(*t)).collect();
    let out = p.ty(output);
    let raw: Vec<_> = inputs.iter().copied().chain([output]).collect();
    let (mut assumed, normalized) = crate::borrowck::implied_bounds::mir_borrowck_implied_outlives_bounds(
        tcx,&rty.tx.cx,false,&contract.predicates,&raw,&contract.assumed_wf);
    assumed.instantiate_query_bounds(tcx,&[]);
    let implied = assumed
        .outlives
        .iter()
        .map(|(a, b)| (p.region(*a, None), p.region(*b, None)))
        .collect();
    let mut tparam_bounds = Vec::new();
    for (t, r) in &assumed.type_outlives {
        if let TyKind::Param(i) = tcx.tys.kind(*t) {
            tparam_bounds.push((*i, p.region(*r, None)));
        }
    }
    // Caller WF is a separate result; callee assumptions are never copied into
    // it. Both input and output WF and declared caller predicates are required.
    let caller = ImpliedBounds::create(
        tcx, rty.tx.prog,
        &contract.caller_predicates,
        &raw,
        &normalized,
        assumed.obligations.clone(),
    );
    let mut cons: Vec<_> = caller
        .outlives
        .iter()
        .map(|(a, b)| (p.region(*a, None), p.region(*b, None)))
        .collect();
    let mut call_bounds = Vec::new();
    for (t, r) in &caller.type_outlives {
        let sr = p.region(*r, None);
        if let TyKind::Param(i) = tcx.tys.kind(*t) {
            call_bounds.push((*i, sr));
        }
        for s in p.ty(*t) {
            cons.push((s, sr));
        }
    }
    for obligation in caller.obligations {
        match obligation {
            OutlivesPredicate::Region(a, b) => cons.push((p.region(a, None), p.region(b, None))),
            OutlivesPredicate::Type(t, r) => {
                let r = p.region(r, None);
                for s in p.ty(t) {
                    cons.push((s, r));
                }
            }
        }
    }
    // Monomorphic Fn-family predicates relate the closure's external input
    // positions to the type arguments used by the ordinary call inputs.
    {
        let bounds = tcx.callable_signatures(rty.tx.prog, d);
        for bound in bounds {
            let Some(actual) = args.get(bound.param as usize) else {
                continue;
            };
            let TyKind::Closure(file, expr, ..) = tcx.tys.kind(*actual) else {
                continue;
            };
            let Some(layout) = rty.closures.borrow().get(&(*file, *expr)).cloned() else {
                continue;
            };
            let TyKind::FnPtr(ps, ret, _, 0) = tcx.tys.kind(bound.signature) else {
                continue;
            };
            let closure = p.ty(tcx.tys.intern(TyKind::Param(bound.param)));
            let mut offset = layout.caps.iter().map(|t| rty.n_slots(*t)).sum::<usize>();
            for (i, _, slots) in &layout.params {
                let n = slots.len();
                if let Some(t) = ps.get(*i) {
                    let all = p.ty(*t);
                    let input: Vec<_> = slots.iter().filter_map(|&i| all.get(i).copied()).collect();
                    if input.len() == n && offset + n <= closure.len() {
                        for (a, b) in closure[offset..offset + n].iter().copied().zip(input) {
                            cons.extend([(a, b), (b, a)]);
                        }
                    }
                }
                offset += n;
            }
            let output = p.ty(*ret);
            if offset + output.len() == closure.len() {
                for (a, b) in closure[offset..].iter().copied().zip(output) {
                    cons.extend([(a, b), (b, a)]);
                }
            }
        }
    }
    let self_ty = contract
        .self_ty
        .map(|t| tcx.normalize(&rty.tx.cx, rty.tx.prog, tcx.tys.subst(t, args)));
    let self_slots = contract.self_ty.map(|t| p.ty(t)).unwrap_or_default();
    let trait_lts = contract
        .trait_regions
        .iter()
        .map(|r| p.region(*r, None))
        .collect();
    let trait_targs = contract
        .trait_types
        .iter()
        .map(|t| {
            let s = p.ty(*t);
            let t = tcx.normalize(&rty.tx.cx, rty.tx.prog, tcx.tys.subst(*t, args));
            Some((s, t))
        })
        .collect();
    let own_targs = contract
        .own_types
        .iter()
        .map(|i| {
            i.and_then(|i| {
                args.get(i as usize).map(|t| {
                    let s = p.ty(tcx.tys.intern(TyKind::Param(i)));
                    (s, tcx.normalize(&rty.tx.cx, rty.tx.prog, *t))
                })
            })
        })
        .collect();
    let proj_bounds = contract.predicates.iter().any(|p| matches!(p,OutlivesPredicate::Type(t,_) if matches!(tcx.tys.kind(*t),TyKind::Assoc(..))));
    SigTmpl {
        assumptions: assumed,
        universal: u,
        typed_regions: p.regions,
        n_syms: p.names.len() as u32,
        names: p.names,
        kinds: p.kinds,
        inputs: ins,
        output: out,
        cons,
        implied,
        ok: true,
        own_targs,
        trait_targs,
        trait_lts,
        tparam_bounds,
        tparam_names: contract.type_names,
        call_bounds,
        own_targ_index: contract.own_types,
        proj_bounds,
        self_ty,
        self_slots,
    }
}

fn empty() -> SigTmpl {
    SigTmpl {
        assumptions: ImpliedBounds::default(),
        universal: None,
        typed_regions: Vec::new(),
        n_syms: 0,
        names: Vec::new(),
        kinds: Vec::new(),
        inputs: Vec::new(),
        output: Vec::new(),
        cons: Vec::new(),
        implied: Vec::new(),
        ok: false,
        own_targs: Vec::new(),
        trait_targs: Vec::new(),
        trait_lts: Vec::new(),
        tparam_bounds: Vec::new(),
        tparam_names: Vec::new(),
        call_bounds: Vec::new(),
        own_targ_index: Vec::new(),
        proj_bounds: false,
        self_ty: None,
        self_slots: Vec::new(),
    }
}

struct Projection<'a, 'b> {
    rty: &'a Rty<'b>,
    args: &'a [TyId],
    regions: Vec<(RegionId, SR)>,
    params: Vec<(u32, Vec<SR>)>,
    names: Vec<String>,
    kinds: Vec<u8>,
}
impl Projection<'_, '_> {
    fn fresh(&mut self, name: &str, kind: u8) -> SR {
        let s = SR::Sym(self.names.len() as u32);
        self.names.push(name.into());
        self.kinds.push(kind);
        s
    }
    fn region(&mut self, r: RegionId, name: Option<&str>) -> SR {
        let kind = self.rty.tx.tcx.tys.region_kind(r);
        match kind {
            RegionKind::ReStatic => return SR::Static,
            RegionKind::ReErased | RegionKind::ReError | RegionKind::ReBound(..) => {
                return SR::Fresh
            }
            _ => {}
        }
        if let Some((_, s)) = self.regions.iter().find(|(a, _)| *a == r) {
            return *s;
        }
        let n = name.unwrap_or("'_");
        let k = if matches!(kind, RegionKind::ReVar(_)) {
            SK_FRESH
        } else if n != "'_" {
            SK_NAMED
        } else {
            SK_ELIDED
        };
        let s = self.fresh(n, k);
        self.regions.push((r, s));
        s
    }
    fn ty(&mut self, t: TyId) -> Vec<SR> {
        let tcx = self.rty.tx.tcx;
        match tcx.tys.kind(t).clone() {
            TyKind::Param(i) => {
                if let Some((_, s)) = self.params.iter().find(|(p, _)| *p == i) {
                    return s.clone();
                }
                let n = self.args.get(i as usize).map_or(0, |t| {
                    self.rty
                        .n_slots(tcx.normalize(&self.rty.tx.cx, self.rty.tx.prog, *t))
                });
                let s: Vec<_> = (0..n).map(|_| self.fresh("'_", SK_PARAM)).collect();
                self.params.push((i, s.clone()));
                s
            }
            TyKind::Ref(_, t, r) => {
                let mut s = vec![self.region(r, None)];
                s.extend(self.ty(t));
                s
            }
            TyKind::Ptr(_, t) | TyKind::Array(t, _) | TyKind::Slice(t) => self.ty(t),
            TyKind::Tuple(ts) => ts.into_iter().flat_map(|t| self.ty(t)).collect(),
            TyKind::Adt(_, ts, rs) => {
                let mut s = tcx
                    .tys
                    .region_args(rs)
                    .iter()
                    .map(|r| self.region(*r, None))
                    .collect::<Vec<_>>();
                for t in ts {
                    s.extend(self.ty(t));
                }
                s
            }
            TyKind::Dyn(_, ts, bs, _, r, _, _) => {
                let mut s = vec![self.region(r, None)];
                for t in ts {
                    s.extend(self.ty(t));
                }
                for (_, t, _) in bs {
                    s.extend(self.ty(t));
                }
                s
            }
            TyKind::Assoc(..) => {
                let n = tcx.normalize(&self.rty.tx.cx, self.rty.tx.prog, t);
                if n != t {
                    self.ty(n)
                } else {
                    Vec::new()
                }
            }
            TyKind::Opaque(_, _, ts, _) => ts.into_iter().flat_map(|t| self.ty(t)).collect(),
            // Nested function binders have no slots in the legacy body layout.
            TyKind::FnPtr(..) => Vec::new(),
            _ => Vec::new(),
        }
    }
}

/// Const children have no argument locals, but inherit their owner's assumptions.
/// Their return type is the existing typeck/builder output until A4c's MIR handoff.
pub fn body_template(rty: &Rty<'_>, bir: &crate::borrowck::bir::Bir) -> Option<std::rc::Rc<SigTmpl>> {
    if let Some(child) = bir.checked_body {
        if matches!(
            child.kind,
            crate::borrowck::body::BodyKind::InlineConst(_) | crate::borrowck::body::BodyKind::AnonConst(_)
        ) {
            let mut t = (*rty.sig_template(child.owner, &bir.args)).clone();
            t.inputs.clear();
            t.output.clear();
            if matches!(child.kind, crate::borrowck::body::BodyKind::InlineConst(_)) {
                if let Some(ret) = bir.locals.first() {
                    for _ in 0..rty.n_slots(ret.ty) {
                        t.output.push(SR::Sym(t.n_syms));
                        t.n_syms += 1;
                        t.names.push("'_".into());
                        t.kinds.push(SK_ELIDED);
                    }
                }
            }
            return t.ok.then(|| std::rc::Rc::new(t));
        }
    }
    let def = bir.def?;
    let t = if rty.tx.tcx.fn_item_sig(rty.tx.prog, def).is_some_and(|sig| sig.header.c_variadic) {
        std::rc::Rc::new(signature_template_for(rty,def,&bir.args,true))
    } else { rty.sig_template(def, &bir.args) };
    t.ok.then_some(t)
}

pub fn closure_template(rty: &Rty<'_>, bir: &crate::borrowck::bir::Bir) -> Option<SigTmpl> {
    let ce = bir.closure_expr?;
    let mut u = SignatureRegions::closure(rty, bir.owner?, ce)?;
    // Fn/FnMut borrow their environment; FnOnce receives it by value.
    if let Some(env) = bir.locals.get(1) {
        let tcx = rty.tx.tcx;
        if let TyKind::Ref(m, ct, _) = tcx.tys.kind(env.ty) {
            let scope = RegionScope::Closure {
                owner: bir.owner?,
                expr: ce,
            };
            let r = tcx
                .tys
                .intern_region(RegionKind::ReLateParam(scope, LateParamKind::ClosureEnv));
            u.regions.insert(
                u.fr_fn_body,
                UniversalRegion {
                    identity: Identity::Region(scope, r),
                    class: Classification::Local,
                    name: "'env".into(),
                },
            );
            u.fr_fn_body += 1;
            u.implicit_input = Some(tcx.tys.intern(TyKind::Ref(*m, *ct, r)));
        } else {
            u.implicit_input = Some(env.ty);
        }
    }
    let sig = *rty.closure_signatures.borrow().get(&ce)?;
    let mut p = Projection {
        rty,
        args: &bir.args,
        regions: Vec::new(),
        params: Vec::new(),
        names: Vec::new(),
        kinds: Vec::new(),
    };
    for region in &u.regions {
        if let Identity::Region(_, r) = region.identity {
            p.region(r, Some(&region.name));
        }
    }
    let inputs = u.inputs.iter().map(|t| p.ty(*t)).collect();
    let output = p.ty(u.output);
    let mut equality = Vec::new();
    if let Some((a, b)) = sig.annotation_eq {
        let tys = &rty.tx.tcx.tys;
        if let (TyKind::FnPtr(ap, ar, _, _), TyKind::FnPtr(bp, br, _, _)) =
            (tys.kind(a), tys.kind(b))
        {
            for (a, b) in ap.iter().chain([ar]).zip(bp.iter().chain([br])) {
                let a = p.ty(*a);
                let b = p.ty(*b);
                if a.len() == b.len() {
                    for (a, b) in a.into_iter().zip(b) {
                        equality.push((a, b));
                        equality.push((b, a));
                    }
                }
            }
        }
    }
    let mut t = empty();
    t.ok = true;
    t.inputs = inputs;
    t.output = output;
    t.cons = equality;
    t.tparam_names = u.contract.type_names.clone();
    let raw: Vec<_> = u.inputs.iter().copied().chain([u.output]).chain(u.implicit_input).collect();
    let (mut relations, _) = crate::borrowck::implied_bounds::mir_borrowck_implied_outlives_bounds(
        rty.tx.tcx,&rty.tx.cx,true,&u.contract.predicates,&raw,&u.contract.assumed_wf);
    // External ROOT query variables already have SR identities in this adapter.
    for &r in &u.query_placeholders { p.region(r,None); }
    relations.retain_instantiated_query_bounds(rty.tx.tcx,&u.query_placeholders);
    t.implied = relations
        .outlives
        .iter()
        .map(|(a, b)| (p.region(*a, None), p.region(*b, None)))
        .collect();
    t.tparam_bounds = relations
        .type_outlives
        .iter()
        .filter_map(|(t, r)| {
            if let TyKind::Param(i) = rty.tx.tcx.tys.kind(*t) {
                Some((*i, p.region(*r, None)))
            } else {
                None
            }
        })
        .collect();
    t.assumptions = relations;
    t.n_syms = p.names.len() as u32;
    t.names = p.names;
    t.kinds = p.kinds;
    t.typed_regions = p.regions;
    t.universal = Some(u);
    Some(t)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        program::Program,
        tcx::{Tcx, EvalCx, EvalState, TypingEnv},
    };

    #[test]
    fn declaration_universals_and_typed_assumptions() {
        let source = br#"
            #![no_std]
            struct S<T: 'static>(T);
            struct Host<'outer>(&'outer u32);
            impl<'outer> Host<'outer> { fn method<'unused>(&self) {} }
            fn signature<'unused, 'a>(x: &'a u32, f: for<'b> fn(&'a u32, &'b u32)) -> &'a u32 { x }
            fn early<'unused, 'a, T: 'a>(x: &'a T) where 'a: 'static {}
            fn output<'a,T>(x: &'a T) -> S<&'a T> { S(x) }
            fn parent<'unused, 'a>(x: &'a u32) { let c = |y: &u32| {}; let inferred = |z: &u32| { z }; }
        "#;
        let dir = std::env::temp_dir().join(format!("relax-a4b-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let file = dir.join("lib.rs");
        std::fs::write(&file, source).unwrap();
        let session = std::sync::Arc::new(crate::Session::default());
        let mut prog = Program::new(&session);
        prog.load_crate(
            "a4b",
            file.to_str().unwrap(),
            2021,
            crate::cfg::CfgSet::host(&session, &[]),
            Vec::new(),
        )
        .unwrap();
        let mut tcx = Tcx::new();
        tcx.collect(&prog);
        std::fs::remove_dir_all(&dir).unwrap();
        assert!(tcx.errors.is_empty(), "{:?}", tcx.errors);
        let def = |n| (0..prog.defs.len() as u32).map(DefId).find(|&d| prog.name(d) == n).unwrap();
        let u = SignatureRegions::function(&tcx,&prog, def("signature")).unwrap();
        assert!(u.regions.iter().any(|u| u.name == "'unused"));
        assert_eq!(u.regions[u.fr_static].class, Classification::Global);
        assert!(matches!(
            u.regions[u.fr_fn_body].identity,
            Identity::FnBody(_)
        ));
        let TyKind::Ref(_, _, a) = tcx.tys.kind(u.inputs[0]) else {
            panic!()
        };
        assert!(matches!(
            tcx.tys.region_kind(*a),
            RegionKind::ReLateParam(RegionScope::Item(_), _)
        ));
        assert!(matches!(tcx.tys.kind(u.output),TyKind::Ref(_,_,r) if r==a));
        let TyKind::FnPtr(ps, _, _, 1) = tcx.tys.kind(u.inputs[1]) else {
            panic!()
        };
        assert!(matches!(tcx.tys.kind(ps[0]),TyKind::Ref(_,_,r) if r==a));
        assert!(
            matches!(tcx.tys.kind(ps[1]),TyKind::Ref(_,_,r) if matches!(tcx.tys.region_kind(*r),RegionKind::ReBound(0,_)))
        );
        let method = SignatureRegions::function(&tcx,&prog, def("method")).unwrap();
        assert!(method.regions.iter().any(|u| u.name == "'outer"));
        assert!(method.regions.iter().any(|u| u.name == "'unused"));
        let early = SignatureRegions::function(&tcx,&prog, def("early")).unwrap();
        assert!(early.contract.predicates.iter().any(|p|matches!(p,OutlivesPredicate::Region(_,r) if tcx.tys.region_kind(*r)==RegionKind::ReStatic)));
        let out = SignatureRegions::function(&tcx,&prog, def("output")).unwrap();
        let raw = out
            .inputs
            .iter()
            .copied()
            .chain([out.output])
            .collect::<Vec<_>>();
        let rel =
            ImpliedBounds::create(&tcx,&prog, &out.contract.predicates, &raw, &raw, Vec::new());
        let TyKind::Ref(_, _, a) = tcx.tys.kind(out.inputs[0]) else {
            panic!()
        };
        let st = tcx.tys.intern_region(RegionKind::ReStatic);
        assert!(
            rel.outlives.contains(&(*a, st)),
            "return type WF must be an assumption"
        );
        assert!(rel
            .type_outlives
            .iter()
            .any(|(t, r)| matches!(tcx.tys.kind(*t), TyKind::Param(0)) && *r == st));
        let obligations = vec![OutlivesPredicate::Region(st, *a)];
        let isolated = ImpliedBounds::create(&tcx,&prog, &[], &[], &[], obligations.clone());
        assert_eq!(isolated.obligations, obligations);
        assert!(isolated.outlives.is_empty());
        let alias = tcx.tys.intern(TyKind::Assoc(
            def("output"),
            vec![tcx.tys.intern(TyKind::Param(0))],
            crate::types::RegionArgsId::EMPTY,
        ));
        let alias_rel = ImpliedBounds::create(
            &tcx, &prog,
            &[OutlivesPredicate::Type(alias, *a)],
            &[],
            &[],
            Vec::new(),
        );
        assert_eq!(
            alias_rel.type_outlives,
            vec![(alias, *a)],
            "alias subjects must survive until constraint conversion"
        );
        let normalized_only = ImpliedBounds::create(&tcx,&prog, &[], &[], &raw, Vec::new());
        assert!(normalized_only.outlives.contains(&(*a, st)));
        let state = EvalState::new();
        let cx = EvalCx::new(&prog, TypingEnv::fully_monomorphized(), &state);
        let owner = def("parent");
        let body = crate::typeck::check_fn_uncached(&cx, &prog, &tcx, owner, &[]);
        assert!(body.errors.is_empty(), "{:?}", body.errors);
        let tx = crate::borrowck::tyx::Tx::new(&prog, &tcx, TypingEnv::fully_monomorphized(), &state);
        let rty = Rty::new(&tx);
        *rty.closure_signatures.borrow_mut() = body.closure_sigs.clone();
        let inferred = body.closure_sigs[&body.closures[1]];
        let TyKind::FnPtr(_, ret, _, _) = tcx.tys.kind(inferred.liberated) else {
            panic!()
        };
        assert!(
            matches!(tcx.tys.kind(*ret),TyKind::Ref(_,_,r) if matches!(tcx.tys.region_kind(*r),RegionKind::ReVar(_))),
            "inferred output must not capture an input-only late lifetime"
        );
        let closure = SignatureRegions::closure(&rty, owner, body.closures[0]).unwrap();
        assert!(closure
            .regions
            .iter()
            .any(|r| r.name == "'unused" && r.class == Classification::External));
        assert!(closure.regions.iter().any(|r| matches!(
            r.identity,
            Identity::Region(RegionScope::Closure { .. }, _)
        ) && r.class == Classification::Local));
    }
}

/// The free subset of a closure input; bound positions are local to its call.
/// Nightly represents these as captured generic args. BIR carries slot indices.
pub fn external_closure_input_slots(rty: &Rty<'_>, expr: u32, input: usize) -> Vec<usize> {
    let sigs = rty.closure_signatures.borrow();
    let Some(sig) = sigs.get(&expr) else { return vec![]; };
    let TyKind::FnPtr(ps, _, _, _) = rty.tx.tcx.tys.kind(sig.bound) else { return vec![]; };
    let Some(&ty) = ps.get(input) else { return vec![]; };
    let mut projection = Projection { rty,args:&[],regions:vec![],params:vec![],names:vec![],kinds:vec![] };
    let tys = &rty.tx.tcx.tys;
    let ty = crate::borrowck::universal_regions::with_erased_adt_regions(rty.tx.tcx, ty);
    let ty = tys.map_regions(ty,&|r,depth| match tys.region_kind(r) {
        RegionKind::ReBound(d,v) if d > depth => tys.intern_region(RegionKind::RePlaceholder { universe:crate::types::UniverseIndex::ROOT,var:v }),
        _ => r,
    },0);
    let ty = crate::borrowck::implied_bounds::replace_erased_regions_with_placeholders(rty.tx.tcx,&[ty])[0];
    projection.ty(ty).iter().enumerate().filter_map(|(i,r)| (!matches!(r, SR::Fresh)).then_some(i)).collect()
}
