// ported from N:rustc_next_trait_solver/src/solve/search_graph.rs @8d1a764
use super::*;
use super::canonical::*;
use super::eval_ctxt::EvalCtxt;
use crate::program::Program;
mod graph;
pub use graph::{SearchGraph, SearchGraphConfig, PathKind, LowerAvailableDepth, CandidateHeadUsages, RequiredDepth};
use crate::tcx::Tcx;

// Kept audit design: rustc_type_ir/src/search_graph/global_cache.rs:47-72.
// Interned IDs preserve equality and dep-node reads; storage lives for this Tcx revision.
// Shared by every thread that type-checks (a parallel `relax check`): interned inputs and
// results are append-only arenas read without a lock with sharded lookup maps, a lock only to
// intern a new one; the global cache is sharded by input. One Mutex over all of it was the top
// contended lock of the check after the region interner.
pub(crate) struct SolverCache {
    pub(super) proof_trees: crate::conc::ShardMap<(u32, usize), ProofTreeCacheEntry>,
    inputs: crate::conc::AppendVec<CanonicalQueryInput>,
    input_ids: crate::conc::ShardMap<CanonicalQueryInput, u32>,
    results: crate::conc::AppendVec<(QueryResult, AccessedOpaques)>,
    result_ids: crate::conc::ShardMap<(QueryResult, AccessedOpaques), u32>,
    intern: std::sync::Mutex<()>,
    global_cache: Box<[std::sync::Mutex<graph::GlobalCache>]>,
}
const SOLVER_CAP: usize = 1 << 26;
const GLOBAL_SHARDS: usize = 64;
impl Default for SolverCache {
    fn default() -> Self {
        SolverCache { proof_trees: Default::default(), inputs: crate::conc::AppendVec::with_capacity(SOLVER_CAP), input_ids: Default::default(),
            results: crate::conc::AppendVec::with_capacity(SOLVER_CAP), result_ids: Default::default(), intern: Default::default(),
            global_cache: (0..GLOBAL_SHARDS).map(|_| Default::default()).collect() }
    }
}

#[derive(Clone)]
pub(super) struct ProofTreeCacheEntry {
    pub result: u32, pub final_revision: super::inspect::Probe,
    pub required_depth: graph::RequiredDepth, pub dep_node: crate::query::DepNodeIndex,
    pub misses: std::sync::Arc<Vec<(u32, String)>>,
}
impl SolverCache {
    pub(crate) fn len(&self) -> usize { self.inputs.len() + self.proof_trees.len() }
    /// The global cache shard holding `input`'s entries.
    fn global(&self, input: u32) -> std::sync::MutexGuard<'_, graph::GlobalCache> {
        crate::solver_work::count(crate::solver_work::SOLVER_GLOBAL_LOCKS);
        self.global_cache[input as usize % GLOBAL_SHARDS].lock().unwrap_or_else(|e| e.into_inner())
    }
    pub(crate) fn cached_len(&self) -> usize {
        self.global_cache.iter().map(|g| g.lock().unwrap_or_else(|e| e.into_inner()).len()).sum::<usize>() + self.proof_trees.len()
    }
    pub(crate) fn remove_misses(&mut self) {
        for g in self.global_cache.iter_mut() { g.get_mut().unwrap_or_else(|e| e.into_inner()).remove_misses(); }
        self.proof_trees.retain(|_, entry| entry.misses.is_empty());
    }
}
pub struct SolverDelegate<'a> { pub limit: crate::tcx::RecursionLimit, pub tcx: &'a Tcx, pub prog: &'a Program, pub cause: super::fulfill::ObligationCause }
impl<'a> SolverDelegate<'a> {
    pub fn new(tcx: &'a Tcx, prog: &'a Program) -> Self { Self { tcx, prog, limit: Default::default(), cause: Default::default() } }
    pub fn input(&mut self, input: CanonicalQueryInput) -> u32 {
        let cache = &self.tcx.queries.solver;
        crate::solver_work::count(crate::solver_work::SOLVER_MAP_LOCKS);
        if let Some(id) = cache.input_ids.get(&input) { return id; }
        crate::solver_work::count(crate::solver_work::SOLVER_INTERN_LOCKS);
        let _g = cache.intern.lock().unwrap_or_else(|e| e.into_inner());
        crate::solver_work::count(crate::solver_work::SOLVER_MAP_LOCKS);
        if let Some(id) = cache.input_ids.get(&input) { return id; }
        let id = cache.inputs.push(input.clone()) as u32;
        crate::solver_work::count(crate::solver_work::SOLVER_MAP_LOCKS);
        cache.input_ids.insert(input, id); id
    }
    fn result_id(&mut self, result: (QueryResult, AccessedOpaques)) -> u32 {
        let cache = &self.tcx.queries.solver;
        crate::solver_work::count(crate::solver_work::SOLVER_MAP_LOCKS);
        if let Some(id) = cache.result_ids.get(&result) { return id; }
        crate::solver_work::count(crate::solver_work::SOLVER_INTERN_LOCKS);
        let _g = cache.intern.lock().unwrap_or_else(|e| e.into_inner());
        crate::solver_work::count(crate::solver_work::SOLVER_MAP_LOCKS);
        if let Some(id) = cache.result_ids.get(&result) { return id; }
        let id = cache.results.push(result.clone()) as u32;
        crate::solver_work::count(crate::solver_work::SOLVER_MAP_LOCKS);
        cache.result_ids.insert(result, id); id
    }
    // Entries are immutable and live for the borrowed Tcx, including across nested evaluations.
    pub fn result(&self, id: u32) -> &'a (QueryResult, AccessedOpaques) { crate::solver_work::count(crate::solver_work::RESULT_READS); &self.tcx.queries.solver.results[id as usize] }
    fn query_input(&self, id: u32) -> &'a CanonicalQueryInput { &self.tcx.queries.solver.inputs[id as usize] }
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
        match &self.result(result).0 {
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
        let response = self.result(result).0.as_ref().ok()?;
        if !has_no_inference_or_external_constraints(&self.tcx.tys, &response) { return None; }
        match response.value.certainty {
            Certainty::Yes => None,
            certainty @ Certainty::Maybe(_) => Some(certainty),
        }
    }
    fn compute(&mut self, graph: &mut SearchGraph, input: u32, inspect: &mut super::inspect::ProofTreeBuilder) -> u32 {
        let input = self.query_input(input);
        // Append-only publication preserves this cache only when no existing impl set
        // changes. Entries with deferred misses (including nested hits) are evicted.
        let result = EvalCtxt::enter_canonical(self, graph, &input, inspect);
        self.result_id(result)
    }
}

impl SolverDelegate<'_> {
    pub(super) fn evaluate_root_goal_for_proof_tree_raw_provider(&mut self, input: u32, root_depth: usize) -> ProofTreeCacheEntry {
        let cached = self.tcx.queries.solver.proof_trees.get(&(input, root_depth));
        if let Some(cached) = cached { crate::program::note_misses(&cached.misses); self.tcx.queries.engine.read_index(cached.dep_node); return cached; }
        let engine = &self.tcx.queries.engine;
        let (((result, final_revision, required_depth), misses), dep_node) = engine.with_anon_task(&mut || crate::type_queries::with_misses(|| {
            let mut inspect = super::inspect::ProofTreeBuilder::new();
            let (id, required_depth) = SearchGraph::evaluate_root_goal_for_proof_tree(self, root_depth, input, &mut inspect);
            let (_, accessed_opaques) = self.result(id); assert!(!accessed_opaques.might_rerun());
            (id, inspect.unwrap(), required_depth)
        }));
        let entry = ProofTreeCacheEntry { result, final_revision, required_depth, dep_node, misses };
        self.tcx.queries.solver.proof_trees.insert((input, root_depth), entry.clone()); entry
    }
}

#[cfg(test)]
pub(crate) use graph::CANDIDATE_PAIRS;
