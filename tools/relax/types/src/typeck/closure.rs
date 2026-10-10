//! Closure signature construction (rustc_hir_typeck::closure). Bound signatures
//! survive typeck; the body is checked with their liberated counterpart. The
//! existing region-insensitive type inference still defers region equalities to
//! borrowck, which will consume these results in A4.
use super::*;
use crate::types::{BoundVar, LateParamKind, RegionId, RegionKind, RegionScope};

#[derive(Clone, Copy, Debug)]
pub struct ClosureSignatures {
    pub bound: TyId,
    /// FnSig encoded as a FnPtr with a dummy binder (no variables of its own).
    pub liberated: TyId,
    /// S' = E' from the successful, whole supplied/expected merge. Both sides
    /// have dummy binders. A4 must relate these types, including their regions.
    pub annotation_eq: Option<(TyId, TyId)>,
}

impl Fcx<'_> {
    pub(super) fn normalize_signature(&mut self, t: TyId) -> TyId {
        let t = self.resolve_region_vars(t);
        self.normalize_body_type(t)
    }

    pub(super) fn init_body_regions(&mut self) {
        let d = self.prog.def(self.b.def);
        if let ItemKind::Fn(sig, _, _) = &self.ast().item(d.item).kind {
            self.tcx.fn_region_env(&self.cx, self.prog, self.file, self.module, &mut self.env,
                self.prog.files[self.file as usize].ast.fn_sig(*sig), self.b.def);
        }
        for (_, r) in &mut self.env.regions.names {
            if let RegionKind::ReBound(0, var) = *r {
                *r = RegionKind::ReLateParam(RegionScope::Item(self.b.def), LateParamKind::Anon(var.0));
            }
        }
        self.env.regions.enter_body(self.region_vars.clone());
    }

    pub(super) fn fresh_region(&self) -> RegionId {
        let var = self.region_vars.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        self.tcx.tys.intern_region(RegionKind::ReVar(var))
    }

    /// Field substitution preserves bound FnPtr types in both the declaration
    /// and the receiver's type arguments. Lifetime arguments use declaration
    /// indices and shift only when escaping a nested binder.
    pub(super) fn instantiate_field_type(&self, ty: TyId, params: crate::types::RegionArgsId, regions: crate::types::RegionArgsId, args: &[TyId]) -> TyId {
        let params = self.tcx.tys.region_args(params);
        let regions = self.tcx.tys.region_args(regions);
        let ty = self.tcx.tys.map_regions(ty, &|r, depth| {
            if let RegionKind::ReEarlyParam(i) = self.tcx.tys.region_kind(r) {
                let r = params.iter().position(|r| self.tcx.tys.region_kind(*r) == RegionKind::ReEarlyParam(i))
                    .and_then(|j| regions.get(j).copied()).unwrap_or(RegionId::ERASED);
                match self.tcx.tys.region_kind(r) {
                    RegionKind::ReBound(d, v) => self.tcx.tys.intern_region(RegionKind::ReBound(d + depth, v)),
                    _ => r,
                }
            } else { r }
        }, 0);
        self.tcx.tys.subst(ty, args)
    }

    pub(super) fn body_signature(&mut self, sig: &FnSigT, args: &[TyId]) -> (Vec<TyId>, TyId) {
        let ps: Vec<_> = sig.params.iter().map(|t| self.tcx.tys.subst_at_depth(*t, args, 1)).collect();
        let ret = self.tcx.tys.subst_at_depth(sig.ret, args, 1);
        let vars: Vec<_> = (0..sig.bound_regions).map(|v| self.tcx.tys.intern_region(
            RegionKind::ReLateParam(RegionScope::Item(self.b.def), LateParamKind::Anon(v)))).collect();
        let (ps, ret) = self.instantiate_signature_parts(&ps, ret, &vars);
        // Most item signatures need no writeback. Keep the existing normalization
        // scope when they do, including its projection-depth limit.
        if ps.iter().chain(std::iter::once(&ret)).any(|t| self.tcx.tys.has_infer(*t) || self.tcx.tys.may_project(*t)) {
            let opened = self.tcx.tys.intern(TyKind::FnPtr(ps, ret, sig.header, 0));
            let opened = self.normalize_signature(opened);
            let TyKind::FnPtr(ps, ret, _, _) = self.tcx.tys.kind(opened).clone() else { unreachable!() };
            (ps, ret)
        } else {
            (ps, ret)
        }
    }

    // rustc anonymize_bound_vars: number used variables in encounter order,
    // dropping unused names. Nested binders retain their own variable indices.
    fn anonymize_signature(&self, sig: TyId) -> TyId {
        let TyKind::FnPtr(ps, ret, c, _) = self.tcx.tys.kind(sig) else { unreachable!() };
        let vars = std::cell::RefCell::new(HashMap::default());
        let rename = |r, depth| match self.tcx.tys.region_kind(r) {
            RegionKind::ReBound(d, var) if d == depth => {
                let mut vars = vars.borrow_mut();
                let next = vars.len() as u32;
                let new = *vars.entry(var).or_insert(next);
                self.tcx.tys.intern_region(RegionKind::ReBound(d, BoundVar(new)))
            }
            _ => r,
        };
        let ps = ps.iter().map(|t| self.tcx.tys.map_regions(*t, &rename, 0)).collect();
        let ret = self.tcx.tys.map_regions(*ret, &rename, 0);
        let count = vars.borrow().len() as u32;
        self.tcx.tys.intern(TyKind::FnPtr(ps, ret, *c, count))
    }

    /// Instantiate a call's item signature and its direct Fn-family bounds
    /// together. Early parameters belong to this call; the Fn bound's own late
    /// parameters stay bound. Register the projections before checking arguments
    /// so deduction also works through blocks, borrows, and pending Self vars.
    pub(super) fn instantiate_call_signature(&mut self, d: DefId, args: &[TyId], sig: &FnSigT) -> (Vec<TyId>, TyId) {
        let early = std::cell::RefCell::new(HashMap::default());
        let instantiate_early = |t| self.tcx.tys.map_regions(t, &|r, _| {
            if let RegionKind::ReEarlyParam(i) = self.tcx.tys.region_kind(r) {
                *early.borrow_mut().entry(i).or_insert_with(|| self.fresh_region())
            } else { r }
        }, 0);
        // A call consumes the inputs/output, not a FnPtr type. Interning whole
        // signatures here retains every temporary early/substituted/opened
        // signature for the lifetime of the interner. Substitute under the
        // skipped binder, then open its payload directly.
        let ps: Vec<_> = sig.params.iter().map(|t| instantiate_early(*t)).collect();
        let ret = instantiate_early(sig.ret);
        let ps: Vec<_> = ps.iter().map(|t| self.tcx.tys.subst_at_depth(*t, args, 1)).collect();
        let ret = self.tcx.tys.subst_at_depth(ret, args, 1);
        let vars: Vec<_> = (0..sig.bound_regions).map(|_| self.fresh_region()).collect();
        let opened = self.instantiate_signature_parts(&ps, ret, &vars);
        let mut expectations = Vec::new();
        {
            let bounds = self.tcx.callable_signatures(self.prog, d);
            for bound in bounds {
                if let Some(self_ty) = args.get(bound.param as usize) {
                    let sig = instantiate_early(bound.signature);
                    let sig = self.tcx.tys.subst(sig, args);
                    let kind = match self.prog.name(bound.trait_def) {
                        "Fn" | "AsyncFn" => crate::upvar::ClosureKind::Fn,
                        "FnMut" | "AsyncFnMut" => crate::upvar::ClosureKind::FnMut,
                        _ => crate::upvar::ClosureKind::FnOnce,
                    };
                    expectations.push((*self_ty, sig, kind));
                }
            }
        }
        self.fn_expectations.extend(expectations);
        opened
    }

    /// Remove exactly one binder. Nested binders protect their own variables;
    /// escaping variables shift down, as in rustc's BoundVarReplacer.
    pub(super) fn instantiate_signature(&self, sig: TyId, regions: &[RegionId]) -> TyId {
        let TyKind::FnPtr(ps, ret, c, _) = self.tcx.tys.kind(sig) else { unreachable!() };
        let (ps, ret) = self.instantiate_signature_parts(ps, *ret, regions);
        self.tcx.tys.intern(TyKind::FnPtr(ps, ret, *c, 0))
    }

    /// Item calls/bodies only need the payload; closure typeck results also
    /// retain the FnPtr constructed by `instantiate_signature` above.
    fn instantiate_signature_parts(&self, ps: &[TyId], ret: TyId, regions: &[RegionId]) -> (Vec<TyId>, TyId) {
        let replace = |r, depth| match self.tcx.tys.region_kind(r) {
            RegionKind::ReBound(d, var) if d == depth => regions[var.0 as usize],
            RegionKind::ReBound(d, var) if d > depth => self.tcx.tys.intern_region(RegionKind::ReBound(d - 1, var)),
            _ => r,
        };
        let ty = |t| self.tcx.tys.map_regions(t, &replace, 0);
        (ps.iter().map(|t| ty(*t)).collect(), ty(ret))
    }

    fn closure_sigs(&mut self, e: ExprId, bound: TyId) -> ClosureSignatures {
        let TyKind::FnPtr(_, _, _, n) = self.tcx.tys.kind(bound) else { unreachable!() };
        let scope = RegionScope::Closure { owner: self.b.def, expr: e.0 };
        let regions: Vec<_> = (0..*n).map(|v| self.tcx.tys.intern_region(
            RegionKind::ReLateParam(scope, LateParamKind::Anon(v)))).collect();
        let liberated = self.instantiate_signature(bound, &regions);
        let liberated = self.normalize_signature(liberated);
        ClosureSignatures { bound, liberated, annotation_eq: None }
    }

    /// rustc closure.rs:876: annotations share one binder; absent types create
    /// inference variables. Elided references in separate inputs are distinct.
    fn supplied_closure_signature(&mut self, params: &[ClosureParam], ret: Option<crate::ast::TyId>) -> TyId {
        let outer = self.env.regions.clone();
        self.env.regions = outer.binder(&self.tcx.tys, self.prog, self.file, List::new(0, 0));
        let mut ps = Vec::new();
        for p in params {
            ps.push(match p.ty { Some(t) => self.lower_ty(t), None => self.fresh(0) });
        }
        let bound = self.env.regions.bound_count();
        // rustc_resolve/late.rs:1186-1196: closure output elision is Infer,
        // not the function signature's single-input elision rule.
        self.env.regions.enter_body(self.region_vars.clone());
        let ret = match ret { Some(t) => self.lower_ty(t), None => self.fresh(0) };
        self.env.regions = outer;
        let sig = self.tcx.tys.intern(TyKind::FnPtr(ps, ret, FnHeader::RUST, bound));
        self.normalize_signature(sig)
    }

    /// rustc closure.rs:300-520: a function pointer or Fn-family Output
    /// projection determines the expected signature from ordinary callable clauses.
    /// Declaration region contracts retain binders alongside selection clauses.
    pub(super) fn deduce_closure_signature(&mut self, expected: TyId) -> Option<(TyId, Option<crate::upvar::ClosureKind>)> {
        let expected = self.shallow_region_vars(expected);
        match self.tcx.tys.kind(expected).clone() {
            TyKind::FnPtr(..) => Some((expected, None)),
            TyKind::Dyn(td, args, ..) if self.is_fn_trait(td) => {
                let (ps, ret) = self.tcx.callable_sig(&self.cx, expected, td, &args)?;
                Some((self.tcx.tys.intern(TyKind::FnPtr(ps, ret, FnHeader::RUST, 0)), None))
            }
            TyKind::Infer(v) => {
                for i in 0..self.fn_expectations.len() {
                    let (self_ty, sig, kind) = self.fn_expectations[i];
                    if self.shallow_region_vars(self_ty) == expected && !self.occurs(v, sig, 0) {
                        return Some((sig, Some(kind)));
                    }
                }
                // Keep the existing opaque-bound inference. Its declaration
                // table has no predicate binder yet (arch's solver work).
                let opaque = self.opaque_vars.iter().find(|x| self.shallow_vars(x.1) == expected).map(|x| x.0)?;
                let (ps, r) = self.opaque_fn_sig(opaque)?;
                Some((self.tcx.tys.intern(TyKind::FnPtr(ps, r, FnHeader::RUST, 0)), None))
            }
            TyKind::Dyn(td, args, ..) => {
                // Likewise preserve today's supertrait inference until the
                // trait predicate representation carries its binders.
                let (ps, r) = self.dyn_super_fn_sig(td, expected, &args)?;
                Some((self.tcx.tys.intern(TyKind::FnPtr(ps, r, FnHeader::RUST, 0)), None))
            }
            _ => None,
        }
    }

    pub(super) fn closure_signatures(&mut self, e: ExprId, params: &[ClosureParam], ret: Option<crate::ast::TyId>, expected: Option<TyId>) -> ClosureSignatures {
        let expected = expected.and_then(|t| self.deduce_closure_signature(t)).map(|(sig, kind)| {
            // The same direct Fn-family bound supplies the signature and the
            // kind that can force a move async closure's coroutine captures.
            if let Some(kind) = kind { self.expected_closure_kinds.insert(e.0, kind); }
            self.normalize_signature(sig)
        });
        let supplied = self.supplied_closure_signature(params, ret);
        let Some(expected) = expected else { return self.closure_sigs(e, supplied) };
        let TyKind::FnPtr(ps, r, _, n) = self.tcx.tys.kind(expected).clone() else { unreachable!() };
        if ps.len() != params.len() { return self.closure_sigs(e, supplied); }
        // This signature uses the safe Rust header of a reified closure pointer
        // (rustc_hir_typeck/src/coercion.rs:1083).
        // Bound regions already use anonymous variable indices.
        // Error recovery must not make the closure body's return type rigid.
        let r = if r == self.tcx.tys.error { self.fresh(0) } else { r };
        let expected = self.tcx.tys.intern(TyKind::FnPtr(ps, r, FnHeader::RUST, n));
        let expected = self.anonymize_signature(expected);
        let mut sigs = self.closure_sigs(e, expected);
        let TyKind::FnPtr(_, _, _, n) = self.tcx.tys.kind(supplied) else { unreachable!() };
        let vars: Vec<_> = (0..*n).map(|_| self.fresh_region()).collect();
        let instantiated = self.instantiate_signature(supplied, &vars);
        // rustc closure.rs:822 commit_if_ok: rollback the *whole* merge if
        // either an input or the output fails, then use the supplied signature.
        let mark = self.snapshot();
        if self.unify(sigs.liberated, instantiated) {
            sigs.annotation_eq = Some((instantiated, sigs.liberated));
            // rustc closure.rs:856-865 checks the body using the resolved
            // supplied inputs and supplied output, after equating S' and E'.
            sigs.liberated = self.resolve_region_vars(instantiated);
            sigs
        } else {
            self.rollback(mark);
            self.closure_sigs(e, supplied)
        }
    }

    pub(super) fn finish_closure_signatures(&mut self) {
        for (e, mut sig) in std::mem::take(&mut self.b.closure_sigs) {
            sig.bound = self.normalize_signature(sig.bound);
            sig.liberated = self.normalize_signature(sig.liberated);
            // Type inference resolves an unannotated output's type by copying
            // the body's result type. Its free regions must remain inferred in
            // the parent, not become the closure's input-only late parameters.
            // A declared/expected bound output is still ReBound in `bound`.
            if sig.annotation_eq.is_none() {
                let scope = RegionScope::Closure { owner:self.b.def, expr:e };
                let replacements = std::cell::RefCell::new(HashMap::default());
                if let TyKind::FnPtr(_,ret,_,_) = self.tcx.tys.kind(sig.bound) {
                    self.tcx.tys.map_regions(*ret,&|r,_| {
                        if matches!(self.tcx.tys.region_kind(r),RegionKind::ReLateParam(s,_) if s==scope) {
                            replacements.borrow_mut().entry(r).or_insert_with(||self.fresh_region());
                        } r
                    },0);
                }
                let replacements = replacements.into_inner();
                let replace_output = |t| {
                    let TyKind::FnPtr(ps,ret,c,n) = self.tcx.tys.kind(t) else { return t; };
                    let ret=self.tcx.tys.map_regions(*ret,&|r,_|replacements.get(&r).copied().unwrap_or(r),0);
                    self.tcx.tys.intern(TyKind::FnPtr(ps.clone(),ret,*c,*n))
                };
                sig.bound=replace_output(sig.bound);
                sig.liberated=replace_output(sig.liberated);
            }
            sig.annotation_eq = sig.annotation_eq.map(|(a, b)| (self.normalize_signature(a), self.normalize_signature(b)));
            self.b.closure_sigs.insert(e, sig);
        }
        for (e, t) in std::mem::take(&mut self.b.inline_const_types) {
            let t = self.normalize_signature(t);
            self.b.inline_const_types.insert(e, t);
        }
    }
}
