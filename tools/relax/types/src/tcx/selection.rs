//! Query entry points for callers without a body inference owner.
//! rustc_trait_selection/src/traits/select/mod.rs:1354; rustc_traits/src/codegen.rs:40.
use super::*;
use crate::solve::{SelectionResult, Selected};
use crate::solve::canonical::InferDelegate;
use crate::solve::goal::{CandidateSource, Certainty, NoSolution, TraitPredicate, TraitRef, PredicatePolarity};
use crate::solve::infer::Inference;

/// Method lookup preserves selection certainty until its owning analysis handles it.
#[derive(Debug)]
pub enum MethodResolution {
    Resolved(DefId, Vec<TyId>),
    Ambiguous(crate::solve::goal::Goal, crate::solve::goal::MaybeCause),
    NoSolution(crate::solve::goal::Goal),
}

impl MethodResolution {
    /// rustc_traits/src/codegen.rs:40-46: dispatch is already proven by checking.
    pub fn expect_dispatch(self) -> (DefId, Vec<TyId>) {
        match self {
            Self::Resolved(def, args) => (def, args),
            result => panic!("relax: established method dispatch failed: {result:?}"),
        }
    }
}

impl Tcx {
    /// Instantiate impl parameters before relating its header, as selection does.
    /// rustc_trait_selection/src/traits/select/mod.rs:2534-2578.
    pub(super) fn relate_impl_pattern(&self, cx: &EvalCx<'_>, pat: TyId, ty: TyId, bindings: &mut Vec<Option<TyId>>) -> bool {
        use crate::types::fold::{TypeFolder, super_fold_ty};
        use crate::solve::relate::TypeRelation;
        struct Parameters { count: usize }
        impl TypeFolder for Parameters {
            fn fold_ty(&mut self, tys: &Types, ty: TyId, depth: u32) -> TyId {
                if let TyKind::Param(i) = tys.kind(ty) { self.count = self.count.max(*i as usize + 1); }
                super_fold_ty(tys, ty, self, depth)
            }
        }
        let mut parameters = Parameters { count: bindings.len() };
        self.tys.fold_with(pat, &mut parameters);
        let mut inputs = vec![ty];
        for t in bindings.iter().flatten() { inputs.push(*t); }
        let mut infcx = Inference::with_inputs(&self.tys, cx, &inputs);
        let mut args = Vec::new();
        for i in 0..parameters.count {
            args.push(bindings.get(i).copied().flatten().unwrap_or_else(|| infcx.fresh_ty(crate::solve::canonical::TyVariableKind::General)));
        }
        if !infcx.relate(self.tys.subst_for_inference(pat, &args), ty) { return false; }
        bindings.resize(args.len(), None);
        for (i, arg) in args.into_iter().enumerate() {
            let value = infcx.resolve_deep(arg);
            if !matches!(self.tys.kind(value), TyKind::Infer(_)) { bindings[i] = Some(value); }
        }
        true
    }

    pub fn select_trait(&self, cx: &EvalCx<'_>, td: DefId, ty: TyId, args: &[TyId]) -> SelectionResult {
        cx.state.impl_read.set(true);
        let mut all = vec![ty]; all.extend_from_slice(args);
        let predicate = TraitPredicate { trait_ref: TraitRef { def: td, args: all.clone() }, polarity: PredicatePolarity::Positive };
        let key = (cx.typing_env, td, ty, args.to_vec());
        let cacheable = !cx.state.par_impls.get() && self.norm_ready.load(std::sync::atomic::Ordering::Acquire)
            && all.iter().all(|t| !self.tys.has_infer(*t));
        if cacheable { if let Some(result) = self.selection_cache.get(&key) { return result; } }
        let mut infcx = Inference::with_inputs(&self.tys, cx, &all);
        let result = crate::solve::select::select_fulfilled(self, cx, &mut infcx, predicate);
        let definite = match &result {
            SelectionResult::Ok(selected) => selected.args.iter().all(|t| !self.tys.has_infer(*t)),
            SelectionResult::NoSolution => true,
            SelectionResult::Ambiguous(_) => false,
        };
        if cacheable && definite { self.selection_cache.insert(key, result.clone()); }
        result
    }

    pub fn evaluate_impl(&self, cx: &EvalCx<'_>, imp: DefId, bindings: &[Option<TyId>]) -> Result<Certainty, NoSolution> {
        let mut inputs = Vec::new();
        for t in bindings { if let Some(t) = t { inputs.push(*t); } }
        let mut infcx = Inference::with_inputs(&self.tys, cx, &inputs);
        let mut args = Vec::new();
        for t in bindings { args.push(t.unwrap_or_else(|| infcx.fresh_ty(crate::solve::canonical::TyVariableKind::General))); }
        let goals = crate::solve::select::impl_goals(self, cx, &mut infcx, imp, &args);
        let mut certainty = Certainty::Yes;
        for goal in goals { certainty = certainty.and(crate::solve::evaluate(self, cx, &mut infcx, goal)?); }
        Ok(certainty)
    }

    pub fn select_dispatch(&self, cx: &EvalCx<'_>, td: DefId, ty: TyId, args: &[TyId]) -> Selected {
        match self.select_trait(cx, td, ty, args) {
            SelectionResult::Ok(selected) => selected,
            result => panic!("relax: established dispatch failed for {:?}: {:?}", crate::solve::select::trait_goal(cx, td, ty, args), result),
        }
    }
}

impl Selected {
    /// Existing method lowering uses NO_DEF for a bound/object and DERIVED_IMPL
    /// for compiler-generated derives. Selection retains the actual source.
    pub fn method_owner(&self) -> DefId {
        match self.source {
            CandidateSource::Impl(def) => def,
            CandidateSource::BuiltinImpl(crate::solve::goal::BuiltinImplKind::Derived) => DERIVED_IMPL,
            _ => crate::program::NO_DEF,
        }
    }
}
