// ported from N:rustc_trait_selection/src/solve/delegate.rs @8d1a764
use super::*;
use crate::infer::fresh_args::ArgFolder;
use crate::program::Program;
use crate::tcx::Tcx;
use crate::types::{TyKind, RegionArgsId};

impl Tcx {
    pub fn complete_args(&self, prog: &Program, def: DefId, compact: &[TyId], regions: RegionArgsId) -> Vec<GenericArg> {
        let indices = self.generic_indices_of(prog, def);
        let regions = self.tys.region_args(regions);
        assert_eq!(compact.len(), indices.types_consts.len(), "generic type/const slots for {}", prog.def_path(def));
        assert_eq!(regions.len(), indices.lifetimes.len(), "generic lifetime slots for {}", prog.def_path(def));
        let mut args = Vec::with_capacity(compact.len() + regions.len());
        for index in 0..(compact.len() + regions.len()) as u32 {
            if let Some(pos) = indices.lifetimes.iter().position(|&i| i == index) {
                args.push(GenericArg::Lifetime(regions[pos]));
            } else {
                let pos = indices.types_consts.iter().position(|&i| i == index).expect("generic declaration index");
                args.push(match self.tys.kind(compact[pos]) {
                    TyKind::Const(ct) => GenericArg::Const(*ct),
                    _ => GenericArg::Type(compact[pos]),
                });
            }
        }
        args
    }
    pub fn instantiate_ty(&self, prog: &Program, def: DefId, args: &[GenericArg], ty: TyId) -> TyId {
        crate::types::fold::EarlyBinder::bind(&self.tys, ty).instantiate(&self.tys, &self.generic_indices_of(prog, def), args)
    }
    pub fn instantiate_predicate(&self, prog: &Program, def: DefId, args: &[GenericArg], p: &Predicate) -> Predicate {
        fold::fold_predicate(&self.tys, p, &mut ArgFolder { indices: &self.generic_indices_of(prog, def), args })
    }
    pub fn impl_trait_ref(&self, prog: &Program, imp: DefId, args: &[GenericArg]) -> TraitRef {
        let def_id = self.impl_trait[&imp];
        let mut compact = vec![self.impl_self[&imp]];
        compact.extend_from_slice(self.impl_trait_args.get(&imp).map_or(&[], |a| a.as_slice()));
        let regions = self.impl_trait_regions.get(&imp).copied().unwrap_or(RegionArgsId::EMPTY);
        let identity = self.complete_args(prog, def_id, &compact, regions);
        let mut f = ArgFolder { indices: &self.generic_indices_of(prog, imp), args };
        let mut result = Vec::with_capacity(identity.len());
        for arg in identity { result.push(fold::fold_arg(&self.tys, arg, &mut f, 0)); }
        TraitRef { def_id, args: result }
    }
}

impl Tcx {
    /// rustc_trait_selection/src/solve/delegate.rs:439-488, final LeafDef path.
    /// DEBLOAT(round9): collection rejects specialization, so every impl is a
    /// leaf and an omitted item uses the trait's definition in every typing mode.
    pub fn fetch_eligible_assoc_item(&self, prog: &Program, trait_assoc_def_id: DefId, impl_def_id: DefId) -> DefId {
        let trait_item = prog.def(trait_assoc_def_id);
        debug_assert_eq!(self.impl_trait.get(&impl_def_id), Some(&trait_item.parent));
        let imp = &prog.impls[prog.def(impl_def_id).sub as usize];
        for &item in &imp.items {
            if prog.trait_item_def_id.get(&item) == Some(&trait_assoc_def_id) { return item; }
        }
        trait_assoc_def_id
    }
}

#[cfg(test)]
mod tests;
