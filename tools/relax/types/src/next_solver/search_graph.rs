// ported from N:rustc_next_trait_solver/src/solve/search_graph.rs @8d1a764
use super::*;
use super::canonical::*;
use super::eval_ctxt::EvalCtxt;
use crate::program::Program;
mod graph;
pub use graph::{SearchGraph, SearchGraphConfig, PathKind, LowerAvailableDepth, CandidateHeadUsages, RequiredDepth};
use crate::tcx::Tcx;
use std::collections::HashMap;

// Kept audit design: rustc_type_ir/src/search_graph/global_cache.rs:47-72.
// Interned IDs preserve equality and dep-node reads; storage lives for this Tcx revision.
#[derive(Default)]
pub(crate) struct SolverCache {
    pub(super) proof_trees: HashMap<(u32, usize), ProofTreeCacheEntry>,
    inputs: Vec<CanonicalQueryInput>,
    input_ids: HashMap<CanonicalQueryInput, u32>,
    results: Vec<(QueryResult, AccessedOpaques)>,
    result_ids: HashMap<(QueryResult, AccessedOpaques), u32>,
    global_cache: graph::GlobalCache,
}

#[derive(Clone)]
pub(super) struct ProofTreeCacheEntry {
    pub result: QueryResult, pub final_revision: super::inspect::Probe,
    pub required_depth: graph::RequiredDepth, pub dep_node: crate::query::DepNodeIndex,
}
impl SolverCache {
    pub(crate) fn len(&self) -> usize { self.inputs.len() + self.proof_trees.len() }
}
pub struct SolverDelegate<'a> { pub limit: crate::tcx::RecursionLimit, pub tcx: &'a Tcx, pub prog: &'a Program, pub cause: super::fulfill::ObligationCause }
impl<'a> SolverDelegate<'a> {
    pub fn new(tcx: &'a Tcx, prog: &'a Program) -> Self { Self { tcx, prog, limit: Default::default(), cause: Default::default() } }
    pub fn input(&mut self, input: CanonicalQueryInput) -> u32 {
        let mut cache = self.tcx.queries.solver.lock().unwrap();
        if let Some(&id) = cache.input_ids.get(&input) { return id; }
        let id = cache.inputs.len() as u32;
        cache.inputs.push(input.clone()); cache.input_ids.insert(input, id); id
    }
    fn result_id(&mut self, result: (QueryResult, AccessedOpaques)) -> u32 {
        let mut cache = self.tcx.queries.solver.lock().unwrap();
        if let Some(&id) = cache.result_ids.get(&result) { return id; }
        let id = cache.results.len() as u32;
        cache.results.push(result.clone()); cache.result_ids.insert(result, id); id
    }
    pub fn result(&self, id: u32) -> (QueryResult, AccessedOpaques) { self.tcx.queries.solver.lock().unwrap().results[id as usize].clone() }
    fn query_input(&self, id: u32) -> CanonicalQueryInput { self.tcx.queries.solver.lock().unwrap().inputs[id as usize].clone() }
    fn unconstrained(&mut self, input: u32, certainty: Certainty) -> u32 {
        let input = self.query_input(input);
        let response = response_no_constraints_raw(&self.tcx.tys, input.canonical.max_universe,
            &input.canonical.var_kinds, certainty);
        self.result_id((Ok(response), Default::default()))
    }
}
impl SolverDelegate<'_> {
    fn initial_provisional_result(&mut self, kind: PathKind, input: u32) -> u32 {
        let certainty = match kind {
            PathKind::Coinductive => Certainty::Yes,
            PathKind::Unknown | PathKind::ForcedAmbiguity => Certainty::overflow(false),
            PathKind::Inductive => unreachable!(),
        };
        self.unconstrained(input, certainty)
    }
    fn is_initial_provisional_result(&self, result: u32) -> Option<PathKind> {
        match self.result(result).0 {
            Ok(response) if has_no_inference_or_external_constraints(&self.tcx.tys, &response) => {
                if response.value.certainty == Certainty::Yes { Some(PathKind::Coinductive) }
                else if response.value.certainty == Certainty::overflow(false) { Some(PathKind::Unknown) }
                else { None }
            }
            Err(NoSolution) => Some(PathKind::Inductive),
            _ => None,
        }
    }
    fn stack_overflow_result(&mut self, input: u32) -> u32 { self.unconstrained(input, Certainty::overflow(true)) }
    fn fixpoint_overflow_result(&mut self, input: u32) -> u32 { self.unconstrained(input, Certainty::overflow(false)) }
    fn is_ambiguous_result(&self, result: u32) -> Option<Certainty> {
        let response = self.result(result).0.ok()?;
        if !has_no_inference_or_external_constraints(&self.tcx.tys, &response) { return None; }
        match response.value.certainty {
            Certainty::Yes => None,
            certainty @ Certainty::Maybe(_) => Some(certainty),
        }
    }
    fn compute(&mut self, graph: &mut SearchGraph, input: u32, inspect: &mut super::inspect::ProofTreeBuilder) -> u32 {
        let input = self.query_input(input);
        // No declaration input is read here (lead decision 52 R1): every query provider
        // reads its key's declaration inputs before it can reach the solver, and
        // QueryCx::collected drops this global cache on every declaration change, so an
        // entry only ever serves the declarations it was computed on.
        let result = EvalCtxt::enter_canonical(self, graph, &input, inspect);
        self.result_id(result)
    }
}

impl SolverDelegate<'_> {
    pub(super) fn evaluate_root_goal_for_proof_tree_raw_provider(&mut self, input: u32, root_depth: usize) -> ProofTreeCacheEntry {
        let cached = self.tcx.queries.solver.lock().unwrap().proof_trees.get(&(input, root_depth)).cloned();
        if let Some(cached) = cached { self.tcx.queries.engine.read_index(cached.dep_node); return cached; }
        let engine = &self.tcx.queries.engine;
        let ((result, final_revision, required_depth), dep_node) = engine.with_anon_task(&mut || {
            let mut inspect = super::inspect::ProofTreeBuilder::new();
            let (id, required_depth) = SearchGraph::evaluate_root_goal_for_proof_tree(self, root_depth, input, &mut inspect);
            let (result, accessed_opaques) = self.result(id); assert!(!accessed_opaques.might_rerun());
            (result, inspect.unwrap(), required_depth)
        });
        let entry = ProofTreeCacheEntry { result, final_revision, required_depth, dep_node };
        self.tcx.queries.solver.lock().unwrap().proof_trees.insert((input, root_depth), entry.clone()); entry
    }
}

#[cfg(test)]
pub(crate) use graph::CANDIDATE_PAIRS;
