// ported from N:rustc_type_ir/src/solve/inspect.rs @8d1a764
// ported from N:rustc_next_trait_solver/src/solve/inspect/build.rs @8d1a764
// ported from N:rustc_trait_selection/src/solve/inspect/analyse.rs @8d1a764
use super::*;
use super::assembly::CandidateSource;
use crate::infer::InferCtxt;
use crate::types::UniverseIndex;

#[derive(Clone)]
pub enum StateData { Unit, Goal(Goal), Args(Vec<GenericArg>) }
#[derive(Clone)]
pub struct State { pub var_values: Vec<GenericArg>, pub data: StateData }
pub type CanonicalState = canonical::Canonical<State>;
#[derive(Clone)]
pub enum ProbeKind {
    Root { result: QueryResult },
    TraitCandidate { source: CandidateSource, result: QueryResult },
    NormalizedSelfTyAssembly, UnsizeAssembly, ProjectionCompatibility, ShadowedEnvProbing,
    OpaqueTypeStorageLookup { result: QueryResult }, RigidAlias { result: QueryResult },
}
#[derive(Clone)]
pub enum ProbeStep {
    AddGoal(GoalSource, CanonicalState), NestedProbe(Probe),
    RecordImplArgs { impl_args: CanonicalState }, MakeCanonicalResponse { shallow_certainty: Certainty },
}
#[derive(Clone)]
pub struct Probe { pub steps: Vec<ProbeStep>, pub kind: ProbeKind, pub final_state: CanonicalState }
pub struct GoalEvaluation {
    pub uncanonicalized_goal: Goal, pub orig_values: Vec<GenericArg>, pub final_revision: Probe, pub result: QueryResult, pub required_depth: super::search_graph::RequiredDepth,
}
#[derive(Default)]
pub(crate) struct ProofTreeBuilder { state: Option<Option<Probe>> }
impl ProofTreeBuilder {
    pub fn new() -> Self { Self { state: Some(None) } }
    pub fn is_noop(&self) -> bool { self.state.is_none() }
    pub fn new_evaluation_step(&self, var_values: Vec<GenericArg>) -> EvaluationStepBuilder {
        EvaluationStepBuilder { state: self.state.as_ref().map(|_| Box::new(WipEvaluationStep {
            evaluation: WipProbe::new(var_values.len()), var_values, probe_depth: 0,
        })) }
    }
    pub fn finish_evaluation_step(&mut self, step: EvaluationStepBuilder) {
        if let Some(state) = &mut self.state { *state = Some(step.state.unwrap().evaluation.finalize()); }
    }
    pub fn unwrap(self) -> Probe { self.state.unwrap().unwrap() }
}
#[derive(Default)]
pub(crate) struct EvaluationStepBuilder { state: Option<Box<WipEvaluationStep>> }
struct WipEvaluationStep { var_values: Vec<GenericArg>, probe_depth: usize, evaluation: WipProbe }
struct WipProbe { initial_num_var_values: usize, steps: Vec<WipProbeStep>, kind: Option<ProbeKind>, final_state: Option<CanonicalState> }
enum WipProbeStep { Step(ProbeStep), NestedProbe(WipProbe) }
impl WipProbe {
    fn new(initial_num_var_values: usize) -> Self { Self { initial_num_var_values, steps: Vec::new(), kind: None, final_state: None } }
    fn finalize(self) -> Probe {
        let mut steps = Vec::new();
        for step in self.steps { steps.push(match step { WipProbeStep::Step(s) => s, WipProbeStep::NestedProbe(p) => ProbeStep::NestedProbe(p.finalize()) }); }
        Probe { steps, kind: self.kind.expect("probe kind"), final_state: self.final_state.expect("probe final state") }
    }
}
impl WipEvaluationStep {
    fn current_evaluation_scope(&mut self) -> &mut WipProbe {
        let mut current = &mut self.evaluation;
        for _ in 0..self.probe_depth { let Some(WipProbeStep::NestedProbe(p)) = current.steps.last_mut() else { unreachable!() }; current = p; }
        current
    }
}
impl EvaluationStepBuilder {
    pub fn take_and_enter_probe(&mut self) -> Self {
        let mut nested = Self { state: self.state.take() };
        if let Some(s) = &mut nested.state {
            let probe = WipProbe::new(s.var_values.len());
            s.current_evaluation_scope().steps.push(WipProbeStep::NestedProbe(probe)); s.probe_depth += 1;
        }
        nested
    }
    pub fn candidate_source(&mut self, source: CandidateSource) {
        if let Some(s) = &mut self.state {
            let Some(WipProbeStep::NestedProbe(p)) = s.current_evaluation_scope().steps.last_mut() else { unreachable!() };
            let Some(ProbeKind::TraitCandidate { source: slot, .. }) = &mut p.kind else { unreachable!() };
            *slot = source;
        }
    }
    pub fn add_var_value(&mut self, value: GenericArg) { if let Some(s) = &mut self.state { s.var_values.push(value); } }
    pub fn probe_kind(&mut self, kind: ProbeKind) {
        if let Some(s) = &mut self.state { assert!(s.current_evaluation_scope().kind.replace(kind).is_none()); }
    }
    pub fn probe_final_state(&mut self, infcx: &InferCtxt<'_>, universe: UniverseIndex) {
        if let Some(s) = &mut self.state {
            let state = canonical::make_canonical_state(infcx, &s.var_values, universe, StateData::Unit);
            assert!(s.current_evaluation_scope().final_state.replace(state).is_none());
        }
    }
    pub fn add_goal(&mut self, infcx: &InferCtxt<'_>, universe: UniverseIndex, source: GoalSource, goal: Goal) {
        if let Some(s) = &mut self.state {
            let state = canonical::make_canonical_state(infcx, &s.var_values, universe, StateData::Goal(goal));
            s.current_evaluation_scope().steps.push(WipProbeStep::Step(ProbeStep::AddGoal(source, state)));
        }
    }
    pub fn record_impl_args(&mut self, infcx: &InferCtxt<'_>, universe: UniverseIndex, args: Vec<GenericArg>) {
        if let Some(s) = &mut self.state {
            let impl_args = canonical::make_canonical_state(infcx, &s.var_values, universe, StateData::Args(args));
            s.current_evaluation_scope().steps.push(WipProbeStep::Step(ProbeStep::RecordImplArgs { impl_args }));
        }
    }
    pub fn make_canonical_response(&mut self, shallow_certainty: Certainty) {
        if let Some(s) = &mut self.state { s.current_evaluation_scope().steps.push(WipProbeStep::Step(ProbeStep::MakeCanonicalResponse { shallow_certainty })); }
    }
    pub fn finish_probe(mut self) -> Self {
        if let Some(s) = &mut self.state {
            assert_ne!(s.probe_depth, 0); let n = s.current_evaluation_scope().initial_num_var_values;
            s.var_values.truncate(n); s.probe_depth -= 1;
        }
        self
    }
}

pub struct InspectGoal<'a, 'tcx> {
    pub infcx: &'a InferCtxt<'tcx>, pub prog: &'a crate::program::Program, pub goal: Goal, orig_values: Vec<GenericArg>, prev_universe: UniverseIndex,
    final_revision: Probe, pub result: Result<Certainty, NoSolution>,
}
pub struct InspectCandidate<'a, 'tcx> {
    pub goal: &'a InspectGoal<'a, 'tcx>, pub kind: &'a ProbeKind, steps: Vec<&'a ProbeStep>,
    final_state: &'a CanonicalState, pub shallow_certainty: Certainty, pub result: Result<Certainty, NoSolution>,
}
impl<'a, 'tcx> InspectGoal<'a, 'tcx> {
    pub fn new(infcx: &'a InferCtxt<'tcx>, prog: &'a crate::program::Program, root: GoalEvaluation) -> Self {
        Self { infcx, prog, prev_universe: infcx.universe(), goal: fold::fold_goal(infcx.tcx, &root.uncanonicalized_goal, &mut crate::infer::resolve::DeepVariableResolver::new(infcx)), orig_values: root.orig_values,
            final_revision: root.final_revision, result: root.result.map(|r| r.value.certainty) }
    }
    fn candidates_recur(&'a self, candidates: &mut Vec<InspectCandidate<'a, 'tcx>>, steps: &mut Vec<&'a ProbeStep>, probe: &'a Probe) {
        let mut shallow_certainty = None;
        for step in &probe.steps {
            match step {
                ProbeStep::AddGoal(..) | ProbeStep::RecordImplArgs { .. } => steps.push(step),
                ProbeStep::MakeCanonicalResponse { shallow_certainty: c } => { assert!(shallow_certainty.replace(*c).is_none()); }
                ProbeStep::NestedProbe(p) => {
                    if matches!(p.kind, ProbeKind::ProjectionCompatibility | ProbeKind::ShadowedEnvProbing) { continue; }
                    let n = steps.len(); self.candidates_recur(candidates, steps, p); steps.truncate(n);
                }
            }
        }
        let result = match &probe.kind {
            ProbeKind::Root { result } | ProbeKind::TraitCandidate { result, .. } | ProbeKind::OpaqueTypeStorageLookup { result } | ProbeKind::RigidAlias { result } => result,
            ProbeKind::NormalizedSelfTyAssembly | ProbeKind::UnsizeAssembly => return,
            ProbeKind::ProjectionCompatibility | ProbeKind::ShadowedEnvProbing => panic!("non-candidate probe"),
        };
        if let Some(shallow_certainty) = shallow_certainty { candidates.push(InspectCandidate {
            goal: self, kind: &probe.kind, steps: steps.clone(), final_state: &probe.final_state,
            shallow_certainty, result: result.as_ref().map(|r| r.value.certainty).map_err(|e| *e),
        }); }
    }
    /// rustc_trait_selection/src/solve/inspect/analyse.rs:325-331.
    pub fn unique_applicable_candidate(&'a self) -> Option<InspectCandidate<'a, 'tcx>> {
        let mut candidates = self.candidates();
        candidates.retain(|c| c.result.is_ok());
        let candidate = candidates.pop();
        if candidates.is_empty() { candidate } else { None }
    }
    pub fn candidates(&'a self) -> Vec<InspectCandidate<'a, 'tcx>> {
        let mut candidates = Vec::new(); self.candidates_recur(&mut candidates, &mut Vec::new(), &self.final_revision); candidates
    }
}
impl InspectCandidate<'_, '_> {
    pub fn instantiate_nested_goals(&self) -> Vec<Goal> {
        let mut values = self.goal.orig_values.clone(); let mut goals = Vec::new();
        for step in &self.steps {
            if let ProbeStep::AddGoal(_, state) = step {
                let StateData::Goal(goal) = canonical::instantiate_canonical_state(self.goal.infcx, self.goal.prog, self.goal.prev_universe, &mut values, state) else { unreachable!() };
                goals.push(goal);
            }
        }
        canonical::instantiate_canonical_state(self.goal.infcx, self.goal.prog, self.goal.prev_universe, &mut values, self.final_state);
        goals
    }
    pub fn instantiate_impl_args(&self) -> Vec<GenericArg> {
        let infcx = self.goal.infcx; let mut values = self.goal.orig_values.clone();
        for step in &self.steps {
            if let ProbeStep::RecordImplArgs { impl_args } = step {
                let StateData::Args(args) = canonical::instantiate_canonical_state(infcx, self.goal.prog, self.goal.prev_universe, &mut values, impl_args) else { unreachable!() };
                canonical::instantiate_canonical_state(infcx, self.goal.prog, self.goal.prev_universe, &mut values, self.final_state);
                let mut resolver = crate::infer::resolve::DeepVariableResolver::new(infcx);
                let mut resolved = Vec::with_capacity(args.len());
                for arg in args { resolved.push(fold::fold_arg(&infcx.tcx.tys, arg, &mut resolver, 0)); }
                return resolved;
            }
        }
        panic!("impl candidate without recorded arguments")
    }
}
