// ported from compiler/rustc_type_ir/src/relate/solver_relating.rs @8d1a764
//! Inference owner for selection outside a body. Constructor equality is shared
//! with Fcx, following rustc_trait_selection/src/traits/select/mod.rs:2527.
use super::canonical::*;
use crate::types::RegionId;
use super::relate::{relate_structural, TypeRelation};
use crate::types::fold::{super_fold_ty, TypeFolder};
use crate::types::{PlaceholderType, RegionKind, TyId, TyKind, Types};

#[derive(Clone, Copy)]
struct Variable {
    value: Option<TyId>,
    kind: TyVariableKind,
    universe: UniverseIndex,
}

pub struct Inference<'a> {
    tys: &'a Types,
    vars: Vec<Variable>,
    undo: Vec<(u32, Variable)>,
    relations: Vec<(TyId, TyId)>,
    universe: UniverseIndex,
    regions: Vec<UniverseIndex>,
    /// variables 0..inputs stand for the caller's (a body's) inference variables of the same
    /// index; later ones exist only here
    inputs: u32,
}

impl<'a> Inference<'a> {
    pub fn new(tys: &'a Types) -> Self {
        Self { tys, vars: Vec::new(), undo: Vec::new(), relations: Vec::new(),
            universe: UniverseIndex::ROOT, regions: Vec::new(), inputs: 0 }
    }

    pub fn with_inputs(tys: &'a Types, cx: &crate::tcx::EvalCx<'_>, inputs: &[TyId]) -> Self {
        struct Scan { max: Option<u32> }
        impl TypeFolder for Scan {
            fn fold_ty(&mut self, tys: &Types, ty: TyId, depth: u32) -> TyId {
                if let TyKind::Infer(v) = tys.kind(ty) { self.max = Some(self.max.map_or(*v, |n| n.max(*v))); }
                super_fold_ty(tys, ty, self, depth)
            }
        }
        let mut scan = Scan { max: None };
        for t in inputs { tys.fold_with(*t, &mut scan); }
        let mut result = Self::new(tys);
        if let Some(max) = scan.max {
            assert!(max != u32::MAX, "wildcard inference variable is not an inference owner");
            for i in 0..=max {
                let kind = match cx.lit_vars.borrow().get(i as usize) { Some(1) => TyVariableKind::Int, Some(2) => TyVariableKind::Float, _ => TyVariableKind::General };
                result.fresh_ty(kind);
            }
            result.inputs = max + 1;
        }
        result
    }

    /// Whether `value` (resolved here) is an answer in the caller's terms: no input variable
    /// was constrained here and it mentions no variable created here. This context is a
    /// query without its caller's inference owner, so it cannot hand back constraints on the
    /// caller's variables nor the variables it made (rustc maps a canonical query's response
    /// into the caller's context through var_values: canonical/query_response.rs); an answer
    /// that needs either is the caller's to compute in its own context.
    pub fn answer_in_inputs(&mut self, value: TyId) -> bool {
        struct Local { inputs: u32, found: bool }
        impl TypeFolder for Local {
            fn fold_ty(&mut self, tys: &Types, ty: TyId, depth: u32) -> TyId {
                if let TyKind::Infer(v) = tys.kind(ty) { self.found |= *v >= self.inputs; }
                super_fold_ty(tys, ty, self, depth)
            }
        }
        if self.vars[..self.inputs as usize].iter().any(|v| v.value.is_some()) { return false; }
        let value = self.resolve_deep(value);
        let mut local = Local { inputs: self.inputs, found: false };
        self.tys.fold_with(value, &mut local);
        !local.found
    }

    fn set(&mut self, var: u32, value: TyId) {
        self.undo.push((var, self.vars[var as usize]));
        self.vars[var as usize].value = Some(value);
    }

    fn bind(&mut self, var: u32, value: TyId) -> bool {
        let value = self.resolve_deep(value);
        let info = self.vars[var as usize];
        let mut occurs = Occurs { var, universe: info.universe, invalid: false };
        self.tys.fold_with(value, &mut occurs);
        if occurs.invalid { return false; }
        match self.tys.kind(value) {
            TyKind::Infer(other) => {
                let other = *other;
                let rhs = self.vars[other as usize];
                if info.kind != TyVariableKind::General && rhs.kind != TyVariableKind::General && info.kind != rhs.kind {
                    return false;
                }
                if info.kind != TyVariableKind::General && rhs.kind == TyVariableKind::General {
                    self.set(other, self.tys.intern(TyKind::Infer(var)));
                } else {
                    self.set(var, value);
                }
                true
            }
            TyKind::Int(_) if info.kind != TyVariableKind::Float => { self.set(var, value); true }
            TyKind::Float(_) if info.kind != TyVariableKind::Int => { self.set(var, value); true }
            _ if info.kind == TyVariableKind::General => { self.set(var, value); true }
            _ => false,
        }
    }
}

impl TypeRelation for Inference<'_> {
    fn relate(&mut self, a: TyId, b: TyId) -> bool {
        let a = self.resolve_ty(a);
        let b = self.resolve_ty(b);
        if self.tys.eq_mod_regions(a, b) { return true; }
        let tys = self.tys;
        if let Some(result) = relate_structural(tys, self, a, b) { return result; }
        match (tys.kind(a).clone(), tys.kind(b).clone()) {
            (TyKind::Error, _) | (_, TyKind::Error) => true,
            // An alias can normalize to the variable it mentions. Defer its
            // equality before binding/occurs checking, as solver_relating.rs:198-220
            // does for projection goals (`?I = <Range<?I> as Iterator>::Item`).
            (TyKind::Assoc(..), _) | (_, TyKind::Assoc(..)) => { self.relations.push((a, b)); true }
            (TyKind::Infer(v), _) => self.bind(v, b),
            (_, TyKind::Infer(v)) => self.bind(v, a),
            _ => false,
        }
    }
}

struct Occurs { var: u32, universe: UniverseIndex, invalid: bool }
impl TypeFolder for Occurs {
    fn fold_ty(&mut self, tys: &Types, t: TyId, depth: u32) -> TyId {
        match tys.kind(t) {
            TyKind::Infer(v) if *v == self.var => self.invalid = true,
            TyKind::Placeholder(p) if !self.universe.can_name(p.universe) => self.invalid = true,
            TyKind::Bound(d, _) if *d >= depth => self.invalid = true,
            _ => { super_fold_ty(tys, t, self, depth); }
        }
        t
    }
}

impl TypeFolder for Inference<'_> {
    fn fold_ty(&mut self, tys: &Types, t: TyId, depth: u32) -> TyId {
        let t = self.resolve_ty(t);
        super_fold_ty(tys, t, self, depth)
    }
}

impl InferDelegate for Inference<'_> {
    fn relate_rigid(&mut self, a: TyId, b: TyId) -> bool {
        let a = self.resolve_ty(a);
        let b = self.resolve_ty(b);
        match (self.tys.kind(a).clone(), self.tys.kind(b).clone()) {
            (TyKind::Infer(v), TyKind::Assoc(..)) => self.bind(v, b),
            (TyKind::Assoc(..), TyKind::Infer(v)) => self.bind(v, a),
            _ => self.relate(a, b),
        }
    }
    fn is_const_arg(&self, _: crate::program::DefId, _: u32) -> bool { false }
    fn snapshot(&self) -> Snapshot { Snapshot { bindings: self.undo.len(), relations: self.relations.len() } }
    fn rollback(&mut self, snapshot: Snapshot) {
        while self.undo.len() > snapshot.bindings {
            let (var, old) = self.undo.pop().unwrap();
            self.vars[var as usize] = old;
        }
        self.relations.truncate(snapshot.relations);
    }
    fn fresh_ty(&mut self, kind: TyVariableKind) -> TyId {
        let var = self.vars.len() as u32;
        self.vars.push(Variable { value: None, kind, universe: self.universe });
        self.tys.intern(TyKind::Infer(var))
    }
    fn resolve_deep(&mut self, ty: TyId) -> TyId { self.tys.fold_with(ty, self) }
    fn take_relations_since(&mut self, snapshot: Snapshot) -> Vec<(TyId, TyId)> { self.relations.split_off(snapshot.relations) }
    fn resolve_ty(&mut self, mut ty: TyId) -> TyId {
        while let TyKind::Infer(var) = self.tys.kind(ty) {
            match self.vars[*var as usize].value { Some(t) => ty = t, None => break }
        }
        ty
    }
    fn resolve_const(&mut self, ty: TyId) -> TyId { self.resolve_ty(ty) }
    fn resolve_region(&mut self, r: RegionId) -> RegionId { r }
    fn ty_variable(&self, var: u32) -> TyVariableInfo {
        let mut root = var;
        while let Some(t) = self.vars[root as usize].value {
            match self.tys.kind(t) { TyKind::Infer(v) => root = *v, _ => break }
        }
        let v = self.vars[root as usize];
        TyVariableInfo { root, sub_root: root, kind: v.kind, universe: v.universe }
    }
    fn const_variable_root(&self, var: u32) -> u32 { self.ty_variable(var).root }
    fn const_variable_universe(&self, var: u32) -> UniverseIndex { self.ty_variable(var).universe }
    fn region_variable_root(&self, var: u32) -> u32 { var }
    fn region_variable_universe(&self, var: u32) -> UniverseIndex { self.regions[var as usize] }
    fn universe(&self) -> UniverseIndex { self.universe }
    fn create_next_universe(&mut self) -> UniverseIndex { self.universe.0 += 1; self.universe }
    fn instantiate_var(&mut self, kind: CanonicalVarKind) -> GenericArg {
        match kind {
            CanonicalVarKind::Ty { universe, kind, .. } => {
                let t = self.fresh_ty(kind);
                if let TyKind::Infer(v) = self.tys.kind(t) { self.vars[*v as usize].universe = universe; }
                GenericArg::Ty(t)
            }
            CanonicalVarKind::Const(universe) => {
                let t = self.fresh_ty(TyVariableKind::General);
                if let TyKind::Infer(v) = self.tys.kind(t) { self.vars[*v as usize].universe = universe; }
                GenericArg::Const(t)
            }
            CanonicalVarKind::PlaceholderTy(p) | CanonicalVarKind::PlaceholderConst(p) => {
                let t = self.tys.intern(TyKind::Placeholder(PlaceholderType { universe: p.universe, bound: p.var }));
                if matches!(kind, CanonicalVarKind::PlaceholderConst(_)) { GenericArg::Const(t) } else { GenericArg::Ty(t) }
            }
            CanonicalVarKind::Region(universe) => {
                let var = self.regions.len() as u32;
                self.regions.push(universe);
                GenericArg::Region(RegionId(self.tys.intern_region(RegionKind::ReVar(var)).0))
            }
            CanonicalVarKind::PlaceholderRegion(p) => GenericArg::Region(RegionId(self.tys.intern_region(RegionKind::RePlaceholder { universe: p.universe, var: p.var }).0)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn projection_equality_precedes_occurs_check() {
        let tys = Types::new();
        for kind in [TyVariableKind::General, TyVariableKind::Int, TyVariableKind::Float] {
            let mut infcx = Inference::new(&tys);
            let variable = infcx.fresh_ty(kind);
            let alias = tys.intern(TyKind::Assoc(crate::program::DefId(0), vec![variable], crate::types::RegionArgsId::EMPTY));
            for (a, b) in [(variable, alias), (alias, variable)] {
                let mark = infcx.snapshot();
                assert!(infcx.relate(a, b));
                assert_eq!(infcx.resolve_ty(variable), variable);
                assert_eq!(infcx.take_relations_since(mark), vec![(a, b)]);
                infcx.rollback(mark);
            }
            let recursive = tys.intern(TyKind::Tuple(vec![variable]));
            assert!(!infcx.relate(variable, recursive));
        }
    }
}
