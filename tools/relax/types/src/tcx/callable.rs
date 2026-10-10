//! Callable sugar is a trait reference plus an Output projection, as in
//! rustc_type_ir/src/predicate.rs:128,906. Regions remain erased until T-infer.
use super::*;
use crate::solve::goal::{AliasKind, AliasTerm, Clause, ProjectionPredicate, PredicatePolarity, Term, TraitPredicate, TraitRef};

/// Declaration signature collected alongside its selection predicates.
#[derive(Clone, Debug)]
pub struct CallableSignature {
    pub param: u32,
    pub trait_def: DefId,
    pub signature: TyId,
}

impl Tcx {
    pub fn callable_trait(&self, def: DefId) -> bool {
        matches!(self.lang_items.by_def.get(&def), Some(LangItem::Fn | LangItem::FnMut | LangItem::FnOnce | LangItem::AsyncFn | LangItem::AsyncFnMut | LangItem::AsyncFnOnce))
    }

    pub fn async_callable_trait(&self, def: DefId) -> bool {
        matches!(self.lang_items.by_def.get(&def), Some(LangItem::AsyncFn | LangItem::AsyncFnMut | LangItem::AsyncFnOnce))
    }

    pub fn callable_output(&self, def: DefId) -> Option<DefId> {
        let item = match self.lang_items.by_def.get(&def) {
            Some(LangItem::AsyncFn | LangItem::AsyncFnMut | LangItem::AsyncFnOnce) => LangItem::AsyncFnOnceOutput,
            Some(LangItem::Fn | LangItem::FnMut | LangItem::FnOnce) => LangItem::FnOnceOutput,
            _ => return None,
        };
        self.lang_items.get(item)
    }

    pub(super) fn push_callable_clauses(&self, out: &mut Vec<Clause>, param: u32, def: DefId, signature: TyId) {
        let signature = self.tys.erase_all_regions(signature);
        let TyKind::FnPtr(ps, ret, _, _) = self.tys.kind(signature) else { return; };
        let args = vec![self.tys.intern(TyKind::Param(param)), self.tys.intern(TyKind::Tuple(ps.clone()))];
        out.push(Clause::Trait(TraitPredicate { trait_ref: TraitRef { def, args: args.clone() }, polarity: PredicatePolarity::Positive }));
        if let Some(output) = self.callable_output(def) {
            out.push(Clause::Projection(ProjectionPredicate {
                alias: AliasTerm { kind: AliasKind::Projection, def: output, args }, term: Term::Ty(*ret),
            }));
        }
    }

    pub fn callable_signatures(&self, prog: &Program, item: DefId) -> Vec<CallableSignature> {
        let Some(sig) = self.fn_item_sig(prog, item) else { return vec![]; };
        sig.region_contract.callable_signatures.iter().filter_map(|bound| {
            let mut bound = bound.clone();
            if self.async_callable_trait(bound.trait_def) {
                let future = self.lang_items.get(LangItem::CallOnceFuture)?;
                let TyKind::FnPtr(ps, _, header, n) = self.tys.kind(bound.signature) else { return None; };
                let args = vec![self.tys.intern(TyKind::Param(bound.param)), self.tys.intern(TyKind::Tuple(ps.clone()))];
                let ret = self.tys.intern(TyKind::Assoc(future, args, RegionArgsId::EMPTY));
                bound.signature = self.tys.intern(TyKind::FnPtr(ps.clone(), ret, *header, *n));
            }
            Some(bound)
        }).collect()
    }

    pub fn callable_sig(&self, cx: &EvalCx<'_>, ty: TyId, def: DefId, args: &[TyId]) -> Option<(Vec<TyId>, TyId)> {
        if !self.callable_trait(def) { return None; }
        let TyKind::Tuple(ps) = self.tys.kind(*args.first()?) else { return None; };
        let output = if self.async_callable_trait(def) { self.lang_items.get(LangItem::CallOnceFuture)? } else { self.callable_output(def)? };
        let mut pa = vec![ty]; pa.extend_from_slice(args);
        let projection = self.tys.intern(TyKind::Assoc(output, pa, RegionArgsId::EMPTY));
        Some((ps.clone(), self.normalize(cx, cx.prog, projection)))
    }
}
