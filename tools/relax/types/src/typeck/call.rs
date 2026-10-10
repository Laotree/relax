//! Call receiver adjustments belong to the generic body, not its instances.
use super::*;
use crate::{borrowck::tyx::Tx, lang_items::LangItem, upvar::ClosureKind};

#[derive(Clone, Copy)]
pub struct CallTrait {
    pub trait_def: DefId,
    pub derefs: u8,
    pub from_param: bool,
    /// FnOnce consumes a non-Copy generic receiver even if its instance is Copy.
    pub by_move: bool,
}

fn trait_order(tcx: &Tcx, td: DefId) -> Option<u8> {
    Some(match tcx.lang_items.by_def.get(&td)? {
        LangItem::Fn => 0, LangItem::FnMut => 1, LangItem::FnOnce => 2,
        LangItem::AsyncFn => 3, LangItem::AsyncFnMut => 4, LangItem::AsyncFnOnce => 5,
        _ => return None,
    })
}

impl Fcx<'_> {
    pub(super) fn record_call_trait(&mut self, e: ExprId, t: TyId, derefs: u8) {
        // Reuse the generic body's expression types: this covers destructuring,
        // fields, returned values and autoderef without reverse-substituting a
        // concrete type (two different parameters can have the same instance).
        let identity = self.b.args.iter().enumerate().all(|(i, a)| matches!(self.tcx.tys.kind(*a), TyKind::Param(k) if *k == i as u32));
        if !identity {
            if let Some(body) = self.polymorphic_body() {
                if let Some(selection) = body.call_traits.get(&e.0).filter(|s| s.from_param) {
                    self.b.call_traits.insert(e.0, *selection);
                    return;
                }
            }
        }
        let from_param = matches!(self.tcx.tys.kind(t), TyKind::Param(_));
        let mut candidates = match self.tcx.tys.kind(t).clone() {
            TyKind::Param(k) => {
                let mut defs: Vec<_> = self.tcx.callable_signatures(self.prog, self.b.def).into_iter()
                    .filter(|b| b.param == k).map(|b| b.trait_def).collect();
                defs.extend(self.param_bounds(t).into_iter().map(|(d, _)| d));
                // Callable sugar on an enclosing impl is in its item environment.
                for (param, file, path) in &self.env.bounds {
                    if *param == k {
                        if let Some(td) = self.tcx.resolve_type_path_def(self.prog, *file, self.module, path) { defs.push(td); }
                    }
                }
                defs
            }
            TyKind::Dyn(td, args, ..) => {
                let mut defs = vec![td];
                let mut todo = self.tcx.trait_super_refs_of(&self.cx, self.prog, td, t, &args);
                while let Some((td, args)) = todo.pop() {
                    if defs.contains(&td) { continue; }
                    defs.push(td);
                    todo.extend(self.tcx.trait_super_refs_of(&self.cx, self.prog, td, t, &args));
                }
                defs
            }
            _ => return,
        };
        // rustc_hir_typeck::callee::try_overloaded_call_traits: first Fn,
        // then FnMut, then FnOnce (and the AsyncFn family for ordinary types).
        candidates.retain(|td| trait_order(self.tcx, *td).is_some());
        let Some(td) = candidates.into_iter().min_by_key(|td| trait_order(self.tcx, *td)) else { return };
        let tx = Tx::new(self.prog, self.tcx, self.cx.typing_env, self.cx.state);
        let by_move = from_param && !tx.is_copy(t);
        self.b.call_traits.insert(e.0, CallTrait { trait_def: td, derefs, from_param, by_move });
    }
}

impl Body {
    /// One source of receiver semantics for expr-use/upvars and borrowck. Concrete
    /// closures are resolved after their owner's capture analysis has completed.
    pub(crate) fn call_kind(&self, tx: &Tx<'_>, e: ExprId, t: TyId) -> Option<ClosureKind> {
        if let Some(selection) = self.call_traits.get(&e.0) {
            return trait_order(tx.tcx, selection.trait_def).map(|order| match order % 3 {
                0 => ClosureKind::Fn, 1 => ClosureKind::FnMut, _ => ClosureKind::FnOnce,
            });
        }
        match tx.kind(t) {
            TyKind::Closure(file, ce, _, _, owner) => crate::upvar::closure_properties(&tx.cx, tx.prog, tx.tcx, self, file, ce, owner).map(|(k, _)| k),
            TyKind::FnDef(..) | TyKind::FnPtr(..) => Some(ClosureKind::FnOnce),
            _ => None,
        }
    }
}
