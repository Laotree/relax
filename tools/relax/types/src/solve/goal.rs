//! Predicate data follows rustc_type_ir/src/{predicate.rs:205,predicate_kind.rs:18},
//! goals/responses follow solve/mod.rs:369,573. No ambient parameter environment.

use super::canonical::{Canonical, CanonicalVarValues};
use crate::program::DefId;
use crate::types::{RegionId, TyId};
use std::collections::HashMap;

/// Const terms use the current type interner's const-valued TyIds (types.rs:18,42).
/// The tag preserves the type/const distinction even though their storage is shared.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Term {
    Ty(TyId),
    Const(TyId),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct TraitRef {
    pub def: DefId,
    /// Self is argument zero.
    pub args: Vec<TyId>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum PredicatePolarity {
    Positive,
    Negative,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct TraitPredicate {
    pub trait_ref: TraitRef,
    pub polarity: PredicatePolarity,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum AliasKind {
    Projection,
    Opaque,
    Inherent,
    Free,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct AliasTerm {
    pub kind: AliasKind,
    pub def: DefId,
    pub args: Vec<TyId>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ProjectionPredicate {
    pub alias: AliasTerm,
    pub term: Term,
}

/// rustc_type_ir/src/predicate.rs:969: `term` must be an unconstrained output
/// inference variable, unlike a projection equality from a where-clause.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct NormalizesTo {
    pub alias: AliasTerm,
    pub term: Term,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum AliasRelationDirection {
    Equate,
    Subtype,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct SubtypePredicate {
    pub a_is_expected: bool,
    pub a: TyId,
    pub b: TyId,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct CoercePredicate {
    pub a: TyId,
    pub b: TyId,
}

/// Only clauses can enter a ParamEnv, as in predicate_kind.rs:18. Selection
/// uses region-erased clauses until the coordinated region-inference migration.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Clause {
    Trait(TraitPredicate),
    Projection(ProjectionPredicate),
    RegionOutlives(RegionId, RegionId),
    TypeOutlives(TyId, RegionId),
    WellFormed(Term),
    ConstEvaluatable(TyId),
    ConstArgHasType(TyId, TyId),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Predicate {
    Clause(Clause),
    NormalizesTo(NormalizesTo),
    AliasRelate(Term, Term, AliasRelationDirection),
    DynCompatible(DefId),
    Subtype(SubtypePredicate),
    Coerce(CoercePredicate),
    ConstEquate(TyId, TyId),
    Ambiguous,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ParamEnvId(pub u32);

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Goal {
    pub param_env: ParamEnvId,
    pub predicate: Predicate,
}

/// IDs are local to this interner. Clause order is significant: ParamEnv candidate
/// indices refer to this order. No sorting, deduplication, or thread-local storage.
#[derive(Default)]
pub struct ParamEnvInterner {
    clauses: Vec<Vec<Clause>>,
    ids: HashMap<Vec<Clause>, ParamEnvId>,
}

impl ParamEnvInterner {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn intern(&mut self, clauses: Vec<Clause>) -> ParamEnvId {
        if let Some(&id) = self.ids.get(&clauses) {
            return id;
        }
        let id = ParamEnvId(u32::try_from(self.clauses.len()).expect("too many parameter environments"));
        self.ids.insert(clauses.clone(), id);
        self.clauses.push(clauses);
        id
    }
    pub fn get(&self, id: ParamEnvId) -> &[Clause] {
        &self.clauses[id.0 as usize]
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Certainty {
    Yes,
    Maybe(MaybeCause),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum MaybeCause {
    Ambiguity,
    /// rustc_type_ir/src/solve/mod.rs:856: stack overflow can suggest a larger
    /// recursion limit; fixpoint overflow cannot. Constraint retention is explicit.
    Overflow {
        suggest_increasing_limit: bool,
        keep_constraints: bool,
    },
}

impl Certainty {
    pub const fn overflow(suggest_increasing_limit: bool) -> Self {
        Self::Maybe(MaybeCause::Overflow {
            suggest_increasing_limit,
            keep_constraints: false,
        })
    }

    /// Conjunction of nested goals, rustc_type_ir/src/solve/mod.rs:832,866.
    pub fn and(self, other: Self) -> Self {
        use MaybeCause::{Ambiguity, Overflow};
        match (self, other) {
            (Self::Yes, b) => b,
            (a, Self::Yes) => a,
            (Self::Maybe(Ambiguity), b) => b,
            (a, Self::Maybe(Ambiguity)) => a,
            (
                Self::Maybe(Overflow {
                    suggest_increasing_limit: a,
                    keep_constraints: x,
                }),
                Self::Maybe(Overflow {
                    suggest_increasing_limit: b,
                    keep_constraints: y,
                }),
            ) => Self::Maybe(Overflow {
                suggest_increasing_limit: a && b,
                keep_constraints: x && y,
            }),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct NoSolution;

/// The future evaluation context owns the external-constraint interner. This is
/// its opaque key, matching rustc's Response::external_constraints interner handle.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ExternalConstraintsId(pub u32);

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Response {
    pub certainty: Certainty,
    pub var_values: CanonicalVarValues,
    pub external_constraints: ExternalConstraintsId,
}

pub type QueryResult = Result<Canonical<Response>, NoSolution>;

/// rustc_type_ir/src/solve/mod.rs:464,547; this step retains the brief's explicit
/// environment clause index for later candidate assembly.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum CandidateSource {
    Impl(DefId),
    BuiltinImpl(BuiltinImplKind),
    ParamEnv(u32),
    AliasBound,
    CoherenceUnknowable,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum BuiltinImplKind {
    Derived,
    Trivial,
    Misc,
    Object(u32),
    TraitUpcasting(u32),
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn environment_interning_preserves_order_and_identity() {
        let mut envs = ParamEnvInterner::new();
        let a = Clause::Trait(TraitPredicate {
            trait_ref: TraitRef {
                def: DefId(3),
                args: vec![TyId(7)],
            },
            polarity: PredicatePolarity::Positive,
        });
        let b = Clause::TypeOutlives(TyId(7), RegionId(1));
        let empty = envs.intern(vec![]);
        assert_eq!(empty, envs.intern(vec![]));
        let ab = envs.intern(vec![a.clone(), b.clone()]);
        assert_eq!(ab, envs.intern(vec![a.clone(), b.clone()]));
        let ba = envs.intern(vec![b.clone(), a.clone()]);
        assert_ne!(ab, ba);
        assert_eq!(envs.get(ab), &[a.clone(), b]);
        let duplicate = envs.intern(vec![a.clone(), a.clone()]);
        assert_eq!(envs.get(duplicate), &[a.clone(), a.clone()]);
        let goal = Goal {
            param_env: ab,
            predicate: Predicate::Clause(a),
        };
        let mut goals = HashMap::new();
        goals.insert(goal.clone(), 9);
        assert_eq!(goals.get(&goal), Some(&9));
        assert_eq!(
            goals.get(&Goal {
                param_env: ba,
                ..goal
            }),
            None
        );
        assert!(envs.get(empty).is_empty());
    }

    #[test]
    fn predicate_polarity_and_normalization_are_distinct() {
        let positive = TraitPredicate {
            trait_ref: TraitRef {
                def: DefId(1),
                args: vec![TyId(2)],
            },
            polarity: PredicatePolarity::Positive,
        };
        let negative = TraitPredicate {
            polarity: PredicatePolarity::Negative,
            ..positive.clone()
        };
        assert_ne!(positive, negative);
        let alias = AliasTerm {
            kind: AliasKind::Projection,
            def: DefId(4),
            args: vec![TyId(2)],
        };
        let term = Term::Ty(TyId(5));
        let projection = Predicate::Clause(Clause::Projection(ProjectionPredicate {
            alias: alias.clone(),
            term,
        }));
        let normalize = Predicate::NormalizesTo(NormalizesTo { alias, term });
        assert_ne!(projection, normalize);
        assert_ne!(term, Term::Const(TyId(5)));
    }

    #[test]
    fn certainty_preserves_overflow_cause() {
        let ambiguous = Certainty::Maybe(MaybeCause::Ambiguity);
        assert_eq!(Certainty::Yes.and(ambiguous), ambiguous);
        assert_eq!(
            ambiguous.and(Certainty::overflow(true)),
            Certainty::overflow(true)
        );
        assert_eq!(
            Certainty::overflow(true).and(Certainty::overflow(false)),
            Certainty::overflow(false)
        );
    }
}
