//! Canonical variable metadata and fresh-context instantiation.
//! rustc_type_ir/src/canonical.rs:38,96,226; rustc_infer/src/infer/canonical/mod.rs:51.

use crate::types::{RegionId, TyId};

pub use crate::types::{BoundVar, UniverseIndex};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Placeholder {
    pub universe: UniverseIndex,
    pub var: BoundVar,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum TyVariableKind {
    General,
    Int,
    Float,
}

/// Numeric variables must use ROOT. `sub_root` is the first canonical variable
/// sub-unified with this variable (itself if none), as in canonical.rs:102.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum CanonicalVarKind {
    Ty {
        universe: UniverseIndex,
        kind: TyVariableKind,
        sub_root: BoundVar,
    },
    Region(UniverseIndex),
    Const(UniverseIndex),
    PlaceholderTy(Placeholder),
    PlaceholderRegion(Placeholder),
    PlaceholderConst(Placeholder),
}

impl CanonicalVarKind {
    pub fn universe(self) -> UniverseIndex {
        match self {
            Self::Ty { universe, .. } | Self::Region(universe) | Self::Const(universe) => universe,
            Self::PlaceholderTy(p) | Self::PlaceholderRegion(p) | Self::PlaceholderConst(p) => {
                p.universe
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Canonical<T> {
    pub value: T,
    pub max_universe: UniverseIndex,
    pub variables: Vec<CanonicalVarKind>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum GenericArg {
    Ty(TyId),
    Region(RegionId),
    Const(TyId),
}

/// Positional values for the canonical variables, including regions and consts.
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct CanonicalVarValues {
    pub values: Vec<GenericArg>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TyVariableInfo {
    pub root: u32,
    pub sub_root: u32,
    pub kind: TyVariableKind,
    pub universe: UniverseIndex,
}

/// The inference context supplies resolution and variable metadata explicitly.
/// rustc_type_ir/src/infer_ctxt.rs:338-378 and
/// rustc_next_trait_solver/src/canonical/canonicalizer.rs:319-403.
/// Resolution is shallow; the canonicalization folder recursively visits children.
#[derive(Clone, Copy)]
pub struct Snapshot {
    pub bindings: usize,
    pub relations: usize,
}

pub trait InferDelegate: super::relate::TypeRelation {
    fn snapshot(&self) -> Snapshot;
    fn rollback(&mut self, snapshot: Snapshot);
    fn fresh_ty(&mut self, kind: TyVariableKind) -> TyId;
    fn resolve_deep(&mut self, ty: TyId) -> TyId;
    /// Transfer relation obligations to the solver, leaving earlier equations
    /// and their rollback records intact. They must not also enter body fulfillment.
    /// rustc_infer/src/infer/at.rs:245 returns InferOk's owned obligations.
    fn take_relations_since(&mut self, snapshot: Snapshot) -> Vec<(TyId, TyId)>;
    /// Declaration index among type/const args (including Self for traits).
    fn is_const_arg(&self, def: crate::program::DefId, index: u32) -> bool;
    fn resolve_ty(&mut self, ty: TyId) -> TyId;
    fn resolve_const(&mut self, value: TyId) -> TyId;
    fn resolve_region(&mut self, region: RegionId) -> RegionId;
    fn ty_variable(&self, var: u32) -> TyVariableInfo;
    fn const_variable_root(&self, var: u32) -> u32;
    fn const_variable_universe(&self, var: u32) -> UniverseIndex;
    fn region_variable_root(&self, var: u32) -> u32;
    fn region_variable_universe(&self, var: u32) -> UniverseIndex;
    fn universe(&self) -> UniverseIndex;
    fn create_next_universe(&mut self) -> UniverseIndex;
    /// `kind` has already had its universe remapped into this context. Return a
    /// fresh existential of the requested class, or the specified placeholder.
    /// Sub-unification links are restored by the future instantiator once all
    /// positional values exist, not by this single-variable allocation method.
    fn instantiate_var(&mut self, kind: CanonicalVarKind) -> GenericArg;
    /// Equality with a rigid alias on one side (it normalizes to itself; alias_relate.rs:63-92,
    /// relate_rigid_alias_non_alias): a variable on the other side is bound to the alias, where
    /// `relate` would return the pair as another alias-relate obligation (and its proof would
    /// relate the same pair again, until overflow).
    fn relate_rigid(&mut self, a: TyId, b: TyId) -> bool { self.relate(a, b) }
}

impl CanonicalVarKind {
    pub fn with_universe(self, universe: UniverseIndex) -> Self {
        match self {
            Self::Ty { kind, sub_root, .. } => Self::Ty {
                universe,
                kind,
                sub_root,
            },
            Self::Const(_) => Self::Const(universe),
            Self::Region(_) => Self::Region(universe),
            Self::PlaceholderTy(p) => Self::PlaceholderTy(Placeholder { universe, ..p }),
            Self::PlaceholderConst(p) => Self::PlaceholderConst(Placeholder { universe, ..p }),
            Self::PlaceholderRegion(p) => Self::PlaceholderRegion(Placeholder { universe, ..p }),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum InstantiateError {
    /// Restoring subtype components requires T-infer's separate relation table.
    NontrivialSubRoot,
    InvalidUniverse,
}

/// Allocate in the current universe, creating fresh universes for higher indices.
/// Numeric inference variables remain in ROOT even when the context is not ROOT.
/// rustc_infer/src/infer/canonical/mod.rs:51,86.
fn instantiate_variables(
    infcx: &mut dyn InferDelegate,
    max_universe: UniverseIndex,
    kinds: &[CanonicalVarKind],
) -> Result<CanonicalVarValues, InstantiateError> {
    // Validate before mutating the inference context. T-infer will replace this
    // restriction with sub_unify_ty_vids_raw (rustc canonical/mod.rs:94).
    for (i, kind) in kinds.iter().enumerate() {
        if kind.universe() > max_universe {
            return Err(InstantiateError::InvalidUniverse);
        }
        if let CanonicalVarKind::Ty {
            kind,
            sub_root,
            universe,
        } = *kind
        {
            if kind == TyVariableKind::General && sub_root != BoundVar(i as u32) {
                return Err(InstantiateError::NontrivialSubRoot);
            }
            if kind != TyVariableKind::General && universe != UniverseIndex::ROOT {
                return Err(InstantiateError::InvalidUniverse);
            }
        }
    }
    let mut universes = vec![infcx.universe()];
    for _ in 0..max_universe.0 {
        universes.push(infcx.create_next_universe());
    }
    let mut values = CanonicalVarValues::default();
    for kind in kinds {
        let universe = match kind {
            CanonicalVarKind::Ty {
                kind: TyVariableKind::Int | TyVariableKind::Float,
                ..
            } => UniverseIndex::ROOT,
            _ => universes[kind.universe().0 as usize],
        };
        values
            .values
            .push(infcx.instantiate_var(kind.with_universe(universe)));
    }
    Ok(values)
}

fn replacement_region(values: &CanonicalVarValues, var: BoundVar) -> RegionId {
    match values.values[var.0 as usize] {
        GenericArg::Region(r) => r,
        _ => panic!("type/const value for bound region"),
    }
}

fn replacement_ty(values: &CanonicalVarValues, bound: crate::types::BoundTy) -> TyId {
    match values.values[bound.var.0 as usize] {
        GenericArg::Ty(t) | GenericArg::Const(t) => t,
        _ => panic!("region value for bound type/const"),
    }
}

/// Substitute the canonical binder using A3's shifting/instantiation folder.
/// Useful for restoring original inputs as well as fresh-context instantiation.
pub fn substitute_goal(
    tys: &crate::types::Types,
    envs: &mut super::goal::ParamEnvInterner,
    goal: &super::goal::Goal,
    values: &CanonicalVarValues,
) -> super::goal::Goal {
    let mut f = crate::types::fold::BoundVarReplacer::new(
        |var| replacement_region(values, var),
        |bound| replacement_ty(values, bound),
    );
    let clauses = super::canonicalizer::fold_clauses(tys, envs.get(goal.param_env), &mut f);
    super::goal::Goal {
        param_env: envs.intern(clauses),
        predicate: super::canonicalizer::fold_predicate(tys, &goal.predicate, &mut f),
    }
}

pub fn instantiate_canonical(
    infcx: &mut dyn InferDelegate,
    tys: &crate::types::Types,
    envs: &mut super::goal::ParamEnvInterner,
    canonical: &Canonical<super::goal::Goal>,
) -> Result<(super::goal::Goal, CanonicalVarValues), InstantiateError> {
    let values = instantiate_variables(infcx, canonical.max_universe, &canonical.variables)?;
    Ok((
        substitute_goal(tys, envs, &canonical.value, &values),
        values,
    ))
}

pub fn instantiate_canonical_values(
    infcx: &mut dyn InferDelegate,
    tys: &crate::types::Types,
    canonical: &Canonical<CanonicalVarValues>,
) -> Result<(CanonicalVarValues, CanonicalVarValues), InstantiateError> {
    let values = instantiate_variables(infcx, canonical.max_universe, &canonical.variables)?;
    let mut f = crate::types::fold::BoundVarReplacer::new(
        |var| replacement_region(&values, var),
        |bound| replacement_ty(&values, bound),
    );
    let value = super::canonicalizer::fold_values(tys, &canonical.value, &mut f);
    Ok((value, values))
}
