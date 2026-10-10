//! Executable canonicalization following
//! rustc_next_trait_solver/src/canonical/canonicalizer.rs:188,237,279,319,405,538.
//! A3's folder owns traversal and binder depth; const positions select its const
//! callback because Relax stores type and const arguments in the same arena.
//! Covers LEN_TY array lengths, declared const generic positions, and tagged
//! const terms/values. Unevaluated const expressions and typed const payloads
//! have no distinct representation in this arena and are not introduced here.

use super::canonical::*;
use super::goal::*;
use crate::types::fold::{super_fold_ty, TypeFolder};
use crate::types::*;
use std::collections::HashMap;

#[derive(Clone, Copy, Debug)]
pub enum CanonicalizeMode {
    Input,
    Response { max_input_universe: UniverseIndex },
}

struct Canonicalizer<'a> {
    infcx: &'a mut dyn InferDelegate,
    mode: CanonicalizeMode,
    in_param_env: bool,
    originals: CanonicalVarValues,
    variables: Vec<CanonicalVarKind>,
    lookup: HashMap<GenericArg, BoundVar>,
    sub_roots: HashMap<u32, BoundVar>,
    cache: HashMap<(TyId, DebruijnIndex, bool), TyId>,
}

impl<'a> Canonicalizer<'a> {
    fn new(infcx: &'a mut dyn InferDelegate, mode: CanonicalizeMode) -> Self {
        Self {
            infcx,
            mode,
            in_param_env: false,
            originals: CanonicalVarValues::default(),
            variables: Vec::new(),
            lookup: HashMap::new(),
            sub_roots: HashMap::new(),
            cache: HashMap::new(),
        }
    }

    fn universe(&self, universe: UniverseIndex) -> UniverseIndex {
        match self.mode {
            CanonicalizeMode::Input => UniverseIndex::ROOT,
            CanonicalizeMode::Response { max_input_universe } => {
                UniverseIndex(universe.0.saturating_sub(max_input_universe.0))
            }
        }
    }

    fn placeholder(&self, universe: UniverseIndex, var: BoundVar) -> Placeholder {
        match self.mode {
            CanonicalizeMode::Input => Placeholder {
                universe: UniverseIndex::ROOT,
                var: BoundVar(self.variables.len() as u32),
            },
            CanonicalizeMode::Response { .. } => Placeholder {
                universe: self.universe(universe),
                var,
            },
        }
    }

    fn insert(&mut self, arg: GenericArg, kind: CanonicalVarKind) -> BoundVar {
        if let Some(var) = self.lookup.get(&arg) {
            return *var;
        }
        let var =
            BoundVar(u32::try_from(self.variables.len()).expect("too many canonical variables"));
        self.originals.values.push(arg);
        self.variables.push(kind);
        self.lookup.insert(arg, var);
        var
    }

    fn max_universe(&self) -> UniverseIndex {
        let mut max = UniverseIndex::ROOT;
        for kind in &self.variables {
            max = max.max(kind.universe());
        }
        max
    }

    fn fold_value(&mut self, tys: &Types, t: TyId, depth: DebruijnIndex, is_const: bool) -> TyId {
        let t = if is_const {
            self.infcx.resolve_const(t)
        } else {
            self.infcx.resolve_ty(t)
        };
        if let Some(result) = self.cache.get(&(t, depth, is_const)) {
            return *result;
        }
        let mut original = t;
        let kind = match *tys.kind(t) {
            TyKind::Infer(v) if is_const => {
                original = tys.intern(TyKind::Infer(self.infcx.const_variable_root(v)));
                Some(CanonicalVarKind::Const(
                    self.universe(self.infcx.const_variable_universe(v)),
                ))
            }
            TyKind::Infer(v) => {
                let info = self.infcx.ty_variable(v);
                original = tys.intern(TyKind::Infer(info.root));
                let sub_root = if info.kind == TyVariableKind::General {
                    *self
                        .sub_roots
                        .entry(info.sub_root)
                        .or_insert(BoundVar(self.variables.len() as u32))
                } else {
                    BoundVar(self.variables.len() as u32)
                };
                let universe = if info.kind == TyVariableKind::General {
                    self.universe(info.universe)
                } else {
                    UniverseIndex::ROOT
                };
                Some(CanonicalVarKind::Ty {
                    universe,
                    kind: info.kind,
                    sub_root,
                })
            }
            TyKind::Param(_) => {
                assert!(
                    matches!(self.mode, CanonicalizeMode::Input),
                    "parameter in canonical response"
                );
                let p = self.placeholder(UniverseIndex::ROOT, BoundVar(0));
                Some(if is_const {
                    CanonicalVarKind::PlaceholderConst(p)
                } else {
                    CanonicalVarKind::PlaceholderTy(p)
                })
            }
            TyKind::Placeholder(p) => {
                let p = self.placeholder(p.universe, p.bound);
                Some(if is_const {
                    CanonicalVarKind::PlaceholderConst(p)
                } else {
                    CanonicalVarKind::PlaceholderTy(p)
                })
            }
            // Canonicalization introduces an outer binder. Preexisting escaping
            // variables require a surrounding binder and are invalid goal inputs.
            TyKind::Bound(d, _) => {
                assert!(d < depth, "escaping bound variable in canonical input");
                None
            }
            _ => None,
        };
        let result = match kind {
            Some(kind) => {
                let arg = if is_const {
                    GenericArg::Const(original)
                } else {
                    GenericArg::Ty(original)
                };
                let var = self.insert(arg, kind);
                tys.intern(TyKind::Bound(
                    depth,
                    BoundTy {
                        var,
                        kind: BoundTyKind::Anon,
                    },
                ))
            }
            None => super_fold_ty(tys, t, self, depth),
        };
        self.cache.insert((t, depth, is_const), result);
        result
    }
}

impl TypeFolder for Canonicalizer<'_> {
    fn fold_ty(&mut self, tys: &Types, t: TyId, depth: DebruijnIndex) -> TyId {
        self.fold_value(tys, t, depth, false)
    }

    fn fold_const(&mut self, tys: &Types, t: TyId, depth: DebruijnIndex) -> TyId {
        self.fold_value(tys, t, depth, true)
    }

    fn fold_args(
        &mut self,
        tys: &Types,
        def: crate::program::DefId,
        args: &[TyId],
        offset: u32,
        depth: DebruijnIndex,
    ) -> Vec<TyId> {
        let mut result = Vec::with_capacity(args.len());
        for (i, t) in args.iter().enumerate() {
            let is_const = self.infcx.is_const_arg(def, i as u32 + offset);
            result.push(self.fold_value(tys, *t, depth, is_const));
        }
        result
    }

    fn fold_region(&mut self, tys: &Types, r: RegionId, depth: DebruijnIndex) -> RegionId {
        let mut r = self.infcx.resolve_region(r);
        let kind = match tys.region_kind(r) {
            RegionKind::ReBound(d, _) => {
                assert!(d < depth, "escaping bound region in canonical input");
                return r;
            }
            RegionKind::ReStatic
                if self.in_param_env || matches!(self.mode, CanonicalizeMode::Response { .. }) =>
            {
                return r
            }
            RegionKind::ReErased | RegionKind::ReError
                if matches!(self.mode, CanonicalizeMode::Response { .. }) =>
            {
                return r
            }
            RegionKind::ReEarlyParam(_) | RegionKind::ReLateParam(..) => {
                assert!(
                    matches!(self.mode, CanonicalizeMode::Input),
                    "parameter region in canonical response"
                );
                CanonicalVarKind::PlaceholderRegion(
                    self.placeholder(UniverseIndex::ROOT, BoundVar(0)),
                )
            }
            RegionKind::RePlaceholder { universe, var } => {
                if let CanonicalizeMode::Response { max_input_universe } = self.mode {
                    assert!(
                        universe == UniverseIndex::ROOT || universe > max_input_universe,
                        "non-root input placeholder region in response"
                    );
                }
                CanonicalVarKind::PlaceholderRegion(self.placeholder(universe, var))
            }
            RegionKind::ReVar(var) => {
                let root = self.infcx.region_variable_root(var);
                r = tys.intern_region(RegionKind::ReVar(root));
                match self.mode {
                    CanonicalizeMode::Input => CanonicalVarKind::PlaceholderRegion(
                        self.placeholder(UniverseIndex::ROOT, BoundVar(0)),
                    ),
                    CanonicalizeMode::Response { .. } => CanonicalVarKind::Region(
                        self.universe(self.infcx.region_variable_universe(root)),
                    ),
                }
            }
            RegionKind::ReStatic | RegionKind::ReErased | RegionKind::ReError => {
                CanonicalVarKind::PlaceholderRegion(
                    self.placeholder(UniverseIndex::ROOT, BoundVar(0)),
                )
            }
        };
        let var = self.insert(GenericArg::Region(r), kind);
        tys.intern_region(RegionKind::ReBound(depth, var))
    }
}

/// Fold the environment first, preserving its order and `'static`, then the
/// predicate. rustc_next_trait_solver/src/canonical/canonicalizer.rs:188.
pub fn canonicalize_goal(
    infcx: &mut dyn InferDelegate,
    tys: &Types,
    envs: &mut ParamEnvInterner,
    goal: &Goal,
    mode: CanonicalizeMode,
) -> (Canonical<Goal>, CanonicalVarValues) {
    let mut f = Canonicalizer::new(infcx, mode);
    f.in_param_env = true;
    let clauses = fold_clauses(tys, envs.get(goal.param_env), &mut f);
    let param_env = envs.intern(clauses);
    f.in_param_env = false;
    f.cache.clear();
    let predicate = fold_predicate(tys, &goal.predicate, &mut f);
    (
        Canonical {
            value: Goal {
                param_env,
                predicate,
            },
            max_universe: f.max_universe(),
            variables: f.variables,
        },
        f.originals,
    )
}

/// Canonicalize response values. External constraints have no owning interner
/// here yet and must be folded by their eventual owner using the same folder;
/// this API deliberately does not accept an opaque Response constraint handle.
pub fn canonicalize_response_values(
    infcx: &mut dyn InferDelegate,
    tys: &Types,
    values: &CanonicalVarValues,
    max_input_universe: UniverseIndex,
) -> Canonical<CanonicalVarValues> {
    let mut f = Canonicalizer::new(infcx, CanonicalizeMode::Response { max_input_universe });
    let value = fold_values(tys, values, &mut f);
    Canonical {
        value,
        max_universe: f.max_universe(),
        variables: f.variables,
    }
}

pub(super) fn fold_values(
    tys: &Types,
    values: &CanonicalVarValues,
    f: &mut dyn TypeFolder,
) -> CanonicalVarValues {
    let mut result = CanonicalVarValues::default();
    for value in &values.values {
        result.values.push(match *value {
            GenericArg::Ty(t) => GenericArg::Ty(f.fold_ty(tys, t, 0)),
            GenericArg::Const(t) => GenericArg::Const(f.fold_const(tys, t, 0)),
            GenericArg::Region(r) => GenericArg::Region(f.fold_region(tys, r, 0)),
        });
    }
    result
}

fn fold_term(tys: &Types, term: Term, f: &mut dyn TypeFolder) -> Term {
    match term {
        Term::Ty(t) => Term::Ty(f.fold_ty(tys, t, 0)),
        Term::Const(t) => Term::Const(f.fold_const(tys, t, 0)),
    }
}

fn fold_alias(tys: &Types, alias: &AliasTerm, f: &mut dyn TypeFolder) -> AliasTerm {
    AliasTerm {
        kind: alias.kind,
        def: alias.def,
        args: f.fold_args(tys, alias.def, &alias.args, 0, 0),
    }
}

fn fold_clause(tys: &Types, clause: &Clause, f: &mut dyn TypeFolder) -> Clause {
    match clause {
        Clause::Trait(p) => Clause::Trait(TraitPredicate {
            trait_ref: TraitRef {
                def: p.trait_ref.def,
                args: f.fold_args(tys, p.trait_ref.def, &p.trait_ref.args, 0, 0),
            },
            polarity: p.polarity,
        }),
        Clause::Projection(p) => Clause::Projection(ProjectionPredicate {
            alias: fold_alias(tys, &p.alias, f),
            term: fold_term(tys, p.term, f),
        }),
        Clause::RegionOutlives(a, b) => {
            Clause::RegionOutlives(f.fold_region(tys, *a, 0), f.fold_region(tys, *b, 0))
        }
        Clause::TypeOutlives(t, r) => {
            Clause::TypeOutlives(f.fold_ty(tys, *t, 0), f.fold_region(tys, *r, 0))
        }
        Clause::WellFormed(t) => Clause::WellFormed(fold_term(tys, *t, f)),
        Clause::ConstEvaluatable(t) => Clause::ConstEvaluatable(f.fold_const(tys, *t, 0)),
        Clause::ConstArgHasType(c, t) => {
            Clause::ConstArgHasType(f.fold_const(tys, *c, 0), f.fold_ty(tys, *t, 0))
        }
    }
}

pub(super) fn fold_clauses(tys: &Types, clauses: &[Clause], f: &mut dyn TypeFolder) -> Vec<Clause> {
    let mut result = Vec::with_capacity(clauses.len());
    for clause in clauses {
        result.push(fold_clause(tys, clause, f));
    }
    result
}

pub(super) fn fold_predicate(tys: &Types, p: &Predicate, f: &mut dyn TypeFolder) -> Predicate {
    match p {
        Predicate::Clause(c) => Predicate::Clause(fold_clause(tys, c, f)),
        Predicate::NormalizesTo(n) => Predicate::NormalizesTo(NormalizesTo {
            alias: fold_alias(tys, &n.alias, f),
            term: fold_term(tys, n.term, f),
        }),
        Predicate::AliasRelate(a, b, direction) => {
            Predicate::AliasRelate(fold_term(tys, *a, f), fold_term(tys, *b, f), *direction)
        }
        Predicate::Subtype(p) => Predicate::Subtype(SubtypePredicate {
            a_is_expected: p.a_is_expected,
            a: f.fold_ty(tys, p.a, 0),
            b: f.fold_ty(tys, p.b, 0),
        }),
        Predicate::Coerce(p) => Predicate::Coerce(CoercePredicate {
            a: f.fold_ty(tys, p.a, 0),
            b: f.fold_ty(tys, p.b, 0),
        }),
        Predicate::ConstEquate(a, b) => {
            Predicate::ConstEquate(f.fold_const(tys, *a, 0), f.fold_const(tys, *b, 0))
        }
        Predicate::DynCompatible(d) => Predicate::DynCompatible(*d),
        Predicate::Ambiguous => Predicate::Ambiguous,
    }
}
