use super::*;

const NO: u32 = 0;
const YES: u32 = 1;
const AMBIGUOUS: u32 = 2;
const STACK_OVERFLOW: u32 = 3;
const FIXPOINT_OVERFLOW: u32 = 4;

#[derive(Clone, Copy)]
enum Operation {
    All,
    Constant(u32),
    Grow(u32),
    Toggle,
    IgnoreCandidates,
    ReadIfYes(u32),
}

#[derive(Clone)]
struct Node {
    edges: Vec<(u32, PathKind)>,
    operation: Operation,
}

impl Node {
    fn all(edges: &[(u32, PathKind)]) -> Self {
        Self {
            edges: edges.to_vec(),
            operation: Operation::All,
        }
    }
    fn constant(result: u32) -> Self {
        Self {
            edges: Vec::new(),
            operation: Operation::Constant(result),
        }
    }
}

struct Toy {
    nodes: Vec<Node>,
    calls: Vec<u32>,
    observed: Vec<(u32, u32, u32)>,
    ambiguity_propagations: Vec<(u32, u32)>,
    fixpoint_overflows: Vec<u32>,
    cache_ambiguity: bool,
}

impl Toy {
    fn new(nodes: Vec<Node>) -> Self {
        Self {
            calls: vec![0; nodes.len()],
            nodes,
            observed: Vec::new(),
            ambiguity_propagations: Vec::new(),
            fixpoint_overflows: Vec::new(),
            cache_ambiguity: true,
        }
    }
}

impl SearchGraphDelegate for Toy {
    fn can_cache_global(&self, _: u32, result: u32) -> bool {
        self.cache_ambiguity || result <= YES
    }
    fn is_coinductive(&self, _: u32) -> bool {
        false
    }
    fn initial_provisional_result(&mut self, path: PathKind, _: u32) -> u32 {
        match path {
            PathKind::Inductive => NO,
            PathKind::Coinductive => YES,
            PathKind::Unknown | PathKind::ForcedAmbiguity => AMBIGUOUS,
        }
    }
    fn is_initial_provisional_result(&self, result: u32) -> Option<PathKind> {
        match result {
            NO => Some(PathKind::Inductive),
            YES => Some(PathKind::Coinductive),
            AMBIGUOUS => Some(PathKind::Unknown),
            _ => None,
        }
    }
    fn stack_overflow_result(&mut self, _: u32) -> u32 {
        STACK_OVERFLOW
    }
    fn fixpoint_overflow_result(&mut self, input: u32) -> u32 {
        self.fixpoint_overflows.push(input);
        FIXPOINT_OVERFLOW
    }
    fn is_ambiguous_result(&self, result: u32) -> Option<u32> {
        match result {
            AMBIGUOUS | STACK_OVERFLOW | FIXPOINT_OVERFLOW => Some(result + 100),
            _ => None,
        }
    }
    fn propagate_ambiguity(&mut self, input: u32, ambiguity: u32) -> u32 {
        self.ambiguity_propagations.push((input, ambiguity));
        ambiguity - 100
    }
    fn compute(&mut self, graph: &mut SearchGraph, input: u32) -> u32 {
        self.calls[input as usize] += 1;
        let node = self.nodes[input as usize].clone();
        let mut result = YES;
        let mut candidates = CandidateHeadUsages::default();
        for (child, step) in node.edges {
            if matches!(node.operation, Operation::IgnoreCandidates) {
                graph.enter_single_candidate();
            }
            let child_result = graph.evaluate_goal(self, child, step);
            if matches!(node.operation, Operation::IgnoreCandidates) {
                candidates.merge_usages(graph.finish_single_candidate());
            }
            self.observed.push((input, child, child_result));
            if result != NO {
                if child_result == NO {
                    result = NO;
                } else {
                    result = result.max(child_result);
                }
            }
        }
        match node.operation {
            Operation::ReadIfYes(child) => {
                if result == YES {
                    let response = graph.evaluate_goal(self, child, I);
                    self.observed.push((input, child, response));
                }
                10
            }
            Operation::All => result,
            Operation::Constant(value) => value,
            Operation::Grow(limit) => (result + 1).max(10).min(limit),
            Operation::Toggle => {
                if result == 10 {
                    11
                } else {
                    10
                }
            }
            Operation::IgnoreCandidates => {
                graph.ignore_candidate_head_usages(candidates);
                10
            }
        }
    }
}

fn make_graph(depth: usize) -> SearchGraph {
    SearchGraph::new(SearchGraphConfig {
        recursion_limit: depth,
        ..SearchGraphConfig::default()
    })
}

use PathKind::{Coinductive as C, ForcedAmbiguity as F, Inductive as I, Unknown as U};

#[test]
fn inductive_cycle_has_no_solution() {
    let mut toy = Toy::new(vec![Node::all(&[(1, I)]), Node::all(&[(0, I)])]);
    let mut graph = make_graph(8);
    assert_eq!(graph.evaluate(&mut toy, 0), NO);
    assert_eq!(toy.calls, [1, 1]);
    assert!(graph.is_empty());
    assert!(graph.global_cache.entries.contains_key(&0));
    assert!(!graph.global_cache.entries.contains_key(&1));
}

#[test]
fn coinductive_cycle_holds_with_one_productive_edge() {
    let mut toy = Toy::new(vec![Node::all(&[(1, I)]), Node::all(&[(0, C)])]);
    let mut graph = make_graph(8);
    assert_eq!(graph.evaluate(&mut toy, 0), YES);
    assert_eq!(toy.calls, [1, 1]);
    assert!(graph.is_empty());
}

#[test]
fn unknown_and_forced_paths_are_ambiguous() {
    for step in [U, F] {
        let mut toy = Toy::new(vec![Node::all(&[(0, step)])]);
        assert_eq!(make_graph(8).evaluate(&mut toy, 0), AMBIGUOUS);
        assert_eq!(toy.calls, [1]);
    }
    let mut toy = Toy::new(vec![Node::all(&[(1, C)]), Node::all(&[(0, F)])]);
    assert_eq!(make_graph(8).evaluate(&mut toy, 0), AMBIGUOUS);
}

#[test]
fn changed_response_reruns_and_invalidates_participants() {
    let mut toy = Toy::new(vec![
        Node {
            edges: vec![(1, C)],
            operation: Operation::Constant(10),
        },
        Node::all(&[(0, C)]),
    ]);
    let mut graph = make_graph(8);
    assert_eq!(graph.evaluate(&mut toy, 0), 10);
    assert_eq!(toy.calls, [2, 2]);
    assert!(toy.observed.contains(&(1, 0, YES)));
    assert!(toy.observed.contains(&(1, 0, 10)));
    assert!(graph.is_empty());
}

#[test]
fn every_cycle_head_reaches_its_fixpoint() {
    // Invariant from mod.rs:1340 (fixpoint-rerun-all-cycle-heads): B must
    // converge even while it also depends on A, the outer cycle head.
    let mut toy = Toy::new(vec![
        Node::all(&[(1, C)]),
        Node {
            edges: vec![(0, C), (1, C)],
            operation: Operation::Grow(13),
        },
    ]);
    let mut graph = make_graph(32);
    assert_eq!(graph.evaluate(&mut toy, 0), 13);
    assert_eq!(toy.calls, [2, 7]);
    assert!(graph.is_empty());
}

#[test]
fn distinct_stack_and_fixpoint_overflow() {
    let mut toy = Toy::new(vec![
        Node::all(&[(1, I)]),
        Node::all(&[(2, I)]),
        Node::constant(YES),
    ]);
    assert_eq!(make_graph(1).evaluate(&mut toy, 0), STACK_OVERFLOW);
    assert_eq!(toy.calls, [1, 1, 0]);
    let mut toy = Toy::new(vec![Node {
        edges: vec![(0, C)],
        operation: Operation::Toggle,
    }]);
    let mut graph = make_graph(32);
    assert_eq!(graph.evaluate(&mut toy, 0), FIXPOINT_OVERFLOW);
    assert_eq!(toy.calls, [8]);
    assert!(graph.global_cache.entries[&0].success.is_some());
    assert!(graph.global_cache.entries[&0].with_overflow.is_empty());
}

#[test]
fn global_cache_hits_across_roots() {
    let mut toy = Toy::new(vec![
        Node::all(&[(2, I)]),
        Node::all(&[(2, I)]),
        Node::constant(YES),
    ]);
    let mut graph = make_graph(16);
    assert_eq!(graph.evaluate(&mut toy, 0), YES);
    assert_eq!(graph.evaluate(&mut toy, 1), YES);
    assert_eq!(graph.evaluate(&mut toy, 0), YES);
    assert_eq!(toy.calls, [1, 1, 1]);
    assert!(graph.is_empty());
}

#[test]
fn successful_cache_entry_requires_enough_depth() {
    let mut toy = Toy::new(vec![
        Node::all(&[(1, I)]),
        Node::all(&[(2, I)]),
        Node::constant(YES),
        Node::all(&[(4, I)]),
        Node::all(&[(0, I)]),
    ]);
    let mut graph = make_graph(2);
    assert_eq!(graph.evaluate(&mut toy, 0), YES);
    assert_eq!(graph.evaluate(&mut toy, 3), STACK_OVERFLOW);
    assert_eq!(toy.calls[0], 2);
    assert_eq!(graph.evaluate(&mut toy, 0), YES);
    assert_eq!(toy.calls[0], 2);
}

#[test]
fn overflow_cache_requires_exact_available_depth() {
    let mut toy = Toy::new(vec![
        Node::all(&[(1, I)]),
        Node::all(&[(2, I)]),
        Node::constant(YES),
        Node::all(&[(4, I)]),
        Node::all(&[(0, I)]),
        Node::all(&[(0, I)]),
    ]);
    let mut graph = make_graph(2);
    assert_eq!(graph.evaluate(&mut toy, 3), STACK_OVERFLOW);
    assert_eq!(graph.evaluate(&mut toy, 5), STACK_OVERFLOW);
    assert_eq!(toy.calls[0], 2);
    assert_eq!(graph.global_cache.entries[&0].with_overflow.len(), 2);
    assert_eq!(graph.evaluate(&mut toy, 0), YES);
    assert_eq!(toy.calls[0], 3);
}

#[test]
fn overflow_reduces_later_sibling_depth() {
    let mut nodes = Vec::new();
    for i in 0..12 {
        nodes.push(Node::all(&[(i + 1, I)]));
    }
    nodes.push(Node::constant(YES));
    nodes[0].edges.push((8, I));
    let mut toy = Toy::new(nodes);
    let mut graph = make_graph(8);
    assert_eq!(graph.evaluate(&mut toy, 0), STACK_OVERFLOW);
    // After the first overflow, the second child gets depth 8/4 = 2.
    assert!(graph.global_cache.entries[&8].with_overflow.contains_key(&2));
    assert_eq!(toy.calls[11], 0);
}

#[test]
fn cycle_root_cache_is_rejected_under_a_participant() {
    let mut toy = Toy::new(vec![Node::all(&[(1, C)]), Node::all(&[(0, C)])]);
    let mut graph = make_graph(16);
    assert_eq!(graph.evaluate(&mut toy, 0), YES);
    assert_eq!(graph.evaluate(&mut toy, 1), YES);
    assert_eq!(toy.calls, [2, 2]);
    assert!(graph.is_empty());
}

#[test]
fn provisional_hit_and_rebase_to_outer_head() {
    let mut toy = Toy::new(vec![
        Node::all(&[(1, C), (2, C)]),
        Node::all(&[(2, C), (0, C)]),
        Node::all(&[(1, C)]),
    ]);
    let mut graph = make_graph(16);
    assert_eq!(graph.evaluate(&mut toy, 0), YES);
    assert_eq!(toy.calls, [1, 1, 1]);
    assert!(graph.is_empty());
}

#[test]
fn ambiguous_head_taints_rebased_responses() {
    let mut toy = Toy::new(vec![
        Node::all(&[(1, C), (2, C)]),
        Node {
            edges: vec![(2, C), (0, C)],
            operation: Operation::Constant(AMBIGUOUS),
        },
        Node::all(&[(1, C)]),
    ]);
    let mut graph = make_graph(16);
    assert_eq!(graph.evaluate(&mut toy, 0), AMBIGUOUS);
    assert_eq!(toy.calls, [1, 1, 1]);
    assert!(toy.ambiguity_propagations.contains(&(2, AMBIGUOUS + 100)));
    assert!(toy.observed.contains(&(0, 2, AMBIGUOUS)));
    assert!(graph.is_empty());
}

#[test]
fn fixpoint_overflow_taints_rebased_responses() {
    let mut toy = Toy::new(vec![
        Node::all(&[(1, C), (2, C)]),
        Node {
            edges: vec![(2, C), (0, C)],
            operation: Operation::Toggle,
        },
        Node::all(&[(1, C)]),
    ]);
    let mut graph = make_graph(32);
    assert_eq!(graph.evaluate(&mut toy, 0), FIXPOINT_OVERFLOW);
    assert!(toy.fixpoint_overflows.contains(&1));
    assert!(toy.fixpoint_overflows.contains(&2));
    assert!(toy.observed.contains(&(0, 2, FIXPOINT_OVERFLOW)));
    assert!(graph.is_empty());
}

#[test]
fn ignored_candidates_keep_self_usages_and_remove_ancestor_usages() {
    let mut toy = Toy::new(vec![Node {
        edges: vec![(0, C), (0, I)],
        operation: Operation::IgnoreCandidates,
    }]);
    let mut graph = make_graph(8);
    assert_eq!(graph.evaluate(&mut toy, 0), 10);
    assert_eq!(toy.calls, [2]);
    let cached = graph.global_cache.entries[&0].success.as_ref().unwrap();
    assert!(cached.nested_goals.0.contains_key(&0));
    let mut toy = Toy::new(vec![
        Node::all(&[(1, C)]),
        Node {
            edges: vec![(0, C), (0, I)],
            operation: Operation::IgnoreCandidates,
        },
    ]);
    let mut graph = make_graph(8);
    assert_eq!(graph.evaluate(&mut toy, 0), 10);
    assert_eq!(toy.calls, [1, 1]);
}

fn stack_entry(input: u32, step: PathKind) -> StackEntry {
    StackEntry {
        input,
        step,
        available_depth: 16,
        required_depth: 0,
        provisional_result: None,
        heads: CycleHeads::default(),
        encountered_overflow: false,
        usages: None,
        candidate_usages: None,
        nested_goals: NestedGoals::default(),
    }
}

fn one_head(index: usize, path: PathKind, used: bool) -> CycleHeads {
    let mut heads = CycleHeads::default();
    let mut usages = HeadUsages::default();
    if used {
        usages.add_usage(path);
    }
    heads.insert(index, PathsToNested::from_path(path), usages);
    heads
}

#[test]
fn cache_applicability_checks_provisional_paths() {
    let mut graph = make_graph(16);
    graph.stack.push(stack_entry(0, I));
    graph.provisional_cache.insert(
        1,
        vec![ProvisionalCacheEntry {
            encountered_overflow: false,
            heads: one_head(0, I, true),
            path_from_head: C,
            result: YES,
        }],
    );
    let mut nested = NestedGoals::default();
    nested.insert(1, PathsToNested::from_path(I));
    assert!(graph.candidate_is_applicable(I, &nested));
    assert!(!graph.candidate_is_applicable(C, &nested));
    graph.provisional_cache.get_mut(&1).unwrap()[0].encountered_overflow = true;
    assert!(graph.candidate_is_applicable(C, &nested));
    nested.insert(0, PathsToNested::EMPTY);
    assert!(!graph.candidate_is_applicable(I, &nested));
}

#[test]
fn overflow_provisional_hit_requires_existing_cycle_dependency() {
    let mut graph = make_graph(16);
    graph.stack.push(stack_entry(0, I));
    graph.stack.push(stack_entry(1, C));
    graph.provisional_cache.insert(
        2,
        vec![ProvisionalCacheEntry {
            encountered_overflow: true,
            heads: one_head(0, C, true),
            path_from_head: C,
            result: STACK_OVERFLOW,
        }],
    );
    assert_eq!(graph.lookup_provisional(2, C), None);
    graph.stack[1].heads = one_head(0, C, true);
    assert_eq!(graph.lookup_provisional(2, C), Some(STACK_OVERFLOW));
    assert!(graph.stack[1].encountered_overflow);
    assert_eq!(graph.stack[1].required_depth, 1);
}

#[test]
fn rebase_rejects_changed_cycle_kinds() {
    let mut graph = make_graph(16);
    graph.stack.push(stack_entry(0, I));
    let mut popped = stack_entry(1, I);
    popped.heads = one_head(0, I, true);
    graph.provisional_cache.insert(
        2,
        vec![ProvisionalCacheEntry {
            encountered_overflow: false,
            heads: one_head(1, C, true),
            path_from_head: C,
            result: YES,
        }],
    );
    graph.rebase(
        &mut Toy::new(vec![]),
        &popped,
        RebaseReason::ReachedFixpoint(None),
    );
    assert!(graph.provisional_cache.is_empty());
}

#[test]
fn rebase_validates_initial_result_usage_kind() {
    let mut graph = make_graph(16);
    graph.stack.push(stack_entry(0, C));
    let mut popped = stack_entry(1, C);
    popped.heads = one_head(0, C, true);
    graph.provisional_cache.insert(
        2,
        vec![ProvisionalCacheEntry {
            encountered_overflow: false,
            heads: one_head(1, I, true),
            path_from_head: C,
            result: YES,
        }],
    );
    graph.rebase(
        &mut Toy::new(vec![]),
        &popped,
        RebaseReason::ReachedFixpoint(Some(C)),
    );
    assert!(graph.provisional_cache.is_empty());
}

#[test]
fn unused_dependencies_survive_rerun_but_leave_no_global_entry() {
    let mut graph = make_graph(16);
    graph.stack.push(stack_entry(0, C));
    let mut popped = stack_entry(1, C);
    popped.heads = one_head(0, C, true);
    for (input, used) in [(2, false), (3, true)] {
        graph.provisional_cache.insert(
            input,
            vec![ProvisionalCacheEntry {
                encountered_overflow: false,
                heads: one_head(1, C, used),
                path_from_head: C,
                result: 10,
            }],
        );
    }
    graph.clear_dependent_provisional_results();
    assert!(graph.provisional_cache.contains_key(&2));
    assert!(!graph.provisional_cache.contains_key(&3));
    graph.rebase(&mut Toy::new(vec![]), &popped, RebaseReason::NoCycleUsages);
    let entry = &graph.provisional_cache[&2][0];
    assert_eq!(entry.heads.highest(), Some(0));
    assert!(entry.heads.0[&0].usages.is_empty());
    assert_eq!(entry.result, 10);
}

#[test]
fn path_sets_follow_path_precedence() {
    for a in PATHS {
        for b in PATHS {
            assert_eq!(a.extend(b), b.extend(a));
            assert_eq!(
                PathsToNested::from_path(a).extend(b).0,
                PathsToNested::from_path(a.extend(b)).0
            );
            assert_eq!(PathsToNested::EMPTY.extend(a).0, PathsToNested::from_path(a).0);
        }
    }
    let mut set = PathsToNested::from_path(I);
    set.union(PathsToNested::from_path(C));
    let extended = set.extend(U);
    assert!(!extended.contains(I));
    assert!(extended.contains(U));
    assert!(extended.contains(C));
    assert_eq!(extended.extend(F).0, PathsToNested::from_path(F).0);
}

#[test]
fn overflow_cannot_hide_a_cycle_through_a_cached_goal() {
    // mod.rs:896 names hidden-by-overflow.rs: B overflows under A, but holds
    // under C where evaluating B encounters a coinductive cycle with C.
    let mut toy = Toy::new(vec![
        Node::all(&[(1, I)]),
        Node::all(&[(2, C)]),
        Node::all(&[(1, C)]),
    ]);
    let mut graph = make_graph(2);
    assert_eq!(graph.evaluate(&mut toy, 0), STACK_OVERFLOW);
    assert!(graph.global_cache.entries[&1].with_overflow.contains_key(&1));
    assert_eq!(graph.evaluate(&mut toy, 2), YES);
    assert_eq!(toy.calls, [1, 2, 2]);
    assert!(graph.is_empty());
}

#[test]
fn overflow_metadata_survives_fixpoint_iterations() {
    let mut toy = Toy::new(vec![
        Node {
            edges: vec![(0, C)],
            operation: Operation::ReadIfYes(1),
        },
        Node::all(&[(2, I)]),
        Node::all(&[(3, I)]),
        Node::constant(YES),
    ]);
    let mut graph = make_graph(2);
    assert_eq!(graph.evaluate(&mut toy, 0), 10);
    assert_eq!(toy.calls, [2, 1, 1, 0]);
    let cached = &graph.global_cache.entries[&0];
    assert!(cached.success.is_none());
    assert_eq!(cached.with_overflow[&2].result, 10);
    assert!(cached.with_overflow[&2].nested_goals.0.contains_key(&2));
    assert_eq!(graph.evaluate(&mut toy, 0), 10);
    assert_eq!(toy.calls[0], 2);
}

#[test]
fn rebase_without_cycle_usages_discards_dependent_responses() {
    let mut graph = make_graph(16);
    graph.stack.push(stack_entry(0, C));
    let mut popped = stack_entry(1, C);
    popped.heads = one_head(0, C, true);
    graph.provisional_cache.insert(
        2,
        vec![ProvisionalCacheEntry {
            encountered_overflow: false,
            heads: one_head(1, C, true),
            path_from_head: C,
            result: 10,
        }],
    );
    graph.rebase(&mut Toy::new(vec![]), &popped, RebaseReason::NoCycleUsages);
    assert!(graph.provisional_cache.is_empty());
}

#[test]
fn selection_delegate_can_exclude_ambiguous_global_answers() {
    let mut toy = Toy::new(vec![Node::constant(AMBIGUOUS), Node::constant(YES), Node::constant(NO)]);
    toy.cache_ambiguity = false;
    let mut graph = make_graph(8);
    for _ in 0..2 {
        assert_eq!(graph.evaluate(&mut toy, 0), AMBIGUOUS);
        assert_eq!(graph.evaluate(&mut toy, 1), YES);
        assert_eq!(graph.evaluate(&mut toy, 2), NO);
    }
    assert_eq!(toy.calls, vec![2, 1, 1]);
}
