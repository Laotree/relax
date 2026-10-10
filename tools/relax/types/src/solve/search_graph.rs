//! Concrete port of rustc_type_ir/src/search_graph/{mod,stack,global_cache}.rs.
//! Inputs and responses are interned IDs owned by the caller: equal canonical
//! inputs/responses must have equal IDs, including across fixpoint iterations.
//! A graph and its cache belong to one immutable solver context (including
//! typing mode); discard them when that context changes. Dependency tracking and proof trees belong to
//! their future consumers, not to this standalone graph.

use std::collections::{BTreeMap, HashMap};

/// rustc_type_ir/src/search_graph/mod.rs:122: forced ambiguity dominates;
/// otherwise a single coinductive step makes the whole path coinductive.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum PathKind {
    Inductive,
    Unknown,
    Coinductive,
    ForcedAmbiguity,
}

impl PathKind {
    pub fn extend(self, rest: Self) -> Self {
        match (self, rest) {
            (Self::ForcedAmbiguity, _) | (_, Self::ForcedAmbiguity) => Self::ForcedAmbiguity,
            (Self::Coinductive, _) | (_, Self::Coinductive) => Self::Coinductive,
            (Self::Unknown, _) | (_, Self::Unknown) => Self::Unknown,
            _ => Self::Inductive,
        }
    }
}

const PATHS: [PathKind; 4] = [
    PathKind::Inductive,
    PathKind::Unknown,
    PathKind::Coinductive,
    PathKind::ForcedAmbiguity,
];

/// rustc_type_ir/src/search_graph/mod.rs:60. All result classification must be
/// semantic, including absence of constraints for initial/ambiguous responses.
/// `compute` may recurse through `evaluate_goal` with the same delegate.
pub trait SearchGraphDelegate {
    /// Selection before canonicalization must not persist inference-dependent or
    /// ambiguous answers (rustc_trait_selection/src/traits/select/mod.rs:1354).
    fn can_cache_global(&self, _input: u32, _result: u32) -> bool { true }
    fn is_coinductive(&self, input: u32) -> bool;
    fn initial_provisional_result(&mut self, kind: PathKind, input: u32) -> u32;
    fn is_initial_provisional_result(&self, result: u32) -> Option<PathKind>;
    fn stack_overflow_result(&mut self, input: u32) -> u32;
    fn fixpoint_overflow_result(&mut self, input: u32) -> u32;
    /// An opaque ambiguity-info ID, not necessarily the response ID.
    fn is_ambiguous_result(&self, result: u32) -> Option<u32>;
    fn propagate_ambiguity(&mut self, input: u32, ambiguity: u32) -> u32;
    fn compute(&mut self, graph: &mut SearchGraph, input: u32) -> u32;
}

#[derive(Debug, Clone, Copy)]
pub struct SearchGraphConfig {
    pub recursion_limit: usize,
    pub fixpoint_step_limit: usize,
    pub divide_depth_on_overflow: usize,
}

impl Default for SearchGraphConfig {
    fn default() -> Self {
        // rustc_next_trait_solver/src/solve/{mod.rs:46,search_graph.rs:46}.
        Self {
            recursion_limit: 128,
            fixpoint_step_limit: 8,
            divide_depth_on_overflow: 4,
        }
    }
}

#[derive(Debug, Default, Clone, Copy)]
struct HeadUsages([u32; 4]);

impl HeadUsages {
    fn add_usage(&mut self, path: PathKind) {
        self.0[path as usize] += 1;
    }
    fn add_nested(&mut self, usages: Self) {
        for i in 0..4 {
            self.0[i] += u32::from(usages.0[i] != 0);
        }
    }
    fn add(&mut self, usages: Self) {
        for i in 0..4 {
            self.0[i] += usages.0[i];
        }
    }
    fn ignore(&mut self, usages: Self) {
        for i in 0..4 {
            self.0[i] = self.0[i].checked_sub(usages.0[i]).unwrap();
        }
    }
    fn is_empty(self) -> bool {
        self.0 == [0; 4]
    }
    fn is_single(self, path: PathKind) -> bool {
        for i in 0..4 {
            if i != path as usize && self.0[i] != 0 {
                return false;
            }
        }
        true
    }
}

#[derive(Debug, Default)]
pub struct CandidateHeadUsages {
    usages: BTreeMap<usize, HeadUsages>,
}

impl CandidateHeadUsages {
    pub fn merge_usages(&mut self, other: Self) {
        for (head, usages) in other.usages {
            self.usages.entry(head).or_default().add(usages);
        }
    }
}

/// Empty denotes the zero-length path, distinct from an inductive edge.
/// rustc_type_ir/src/search_graph/mod.rs:366.
#[derive(Debug, Clone, Copy)]
struct PathsToNested(u8);

impl PathsToNested {
    const EMPTY: Self = Self(1);
    fn from_path(path: PathKind) -> Self {
        Self(2 << path as u8)
    }
    fn contains(self, path: PathKind) -> bool {
        self.0 & Self::from_path(path).0 != 0
    }
    fn union(&mut self, other: Self) {
        self.0 |= other.0;
    }
    fn extend(self, path: PathKind) -> Self {
        let bit = Self::from_path(path).0;
        let weaker = bit - 1;
        if self.0 & weaker != 0 {
            Self((self.0 & !weaker) | bit)
        } else {
            self
        }
    }
    fn extend_paths(self, paths: Self) -> Self {
        let mut result = Self(0);
        for path in PATHS {
            if paths.contains(path) {
                result.union(self.extend(path));
            }
        }
        result
    }
}

#[derive(Debug, Clone, Copy)]
struct CycleHead {
    paths: PathsToNested,
    usages: HeadUsages,
}

#[derive(Debug, Default, Clone)]
struct CycleHeads(BTreeMap<usize, CycleHead>);

impl CycleHeads {
    fn highest(&self) -> Option<usize> {
        self.0.last_key_value().map(|(i, _)| *i)
    }
    fn lowest(&self) -> Option<usize> {
        self.0.first_key_value().map(|(i, _)| *i)
    }
    fn insert(&mut self, index: usize, paths: PathsToNested, usages: HeadUsages) {
        match self.0.get_mut(&index) {
            Some(head) => {
                head.paths.union(paths);
                head.usages.add_nested(usages);
            }
            None => {
                self.0.insert(index, CycleHead { paths, usages });
            }
        }
    }
}

#[derive(Debug, Default, Clone)]
struct NestedGoals(HashMap<u32, PathsToNested>);

impl NestedGoals {
    fn insert(&mut self, input: u32, paths: PathsToNested) {
        self.0
            .entry(input)
            .and_modify(|p| p.union(paths))
            .or_insert(paths);
    }
    fn extend_child(&mut self, step: PathKind, nested: &Self) {
        for (&input, &paths) in &nested.0 {
            self.insert(input, paths.extend(step));
        }
    }
}

/// rustc_type_ir/src/search_graph/stack.rs:19: only the top entry is mutated;
/// child metadata is propagated when returning (including cache hits).
#[derive(Debug)]
struct StackEntry {
    input: u32,
    step: PathKind,
    available_depth: usize,
    required_depth: usize,
    provisional_result: Option<u32>,
    heads: CycleHeads,
    encountered_overflow: bool,
    usages: Option<HeadUsages>,
    candidate_usages: Option<CandidateHeadUsages>,
    nested_goals: NestedGoals,
}

#[derive(Debug)]
struct ProvisionalCacheEntry {
    encountered_overflow: bool,
    heads: CycleHeads,
    path_from_head: PathKind,
    result: u32,
}

struct EvaluationResult {
    encountered_overflow: bool,
    required_depth: usize,
    heads: CycleHeads,
    nested_goals: NestedGoals,
    result: u32,
}

impl EvaluationResult {
    fn finalize(entry: StackEntry, encountered_overflow: bool, result: u32) -> Self {
        Self {
            encountered_overflow,
            required_depth: entry.required_depth,
            heads: entry.heads,
            nested_goals: entry.nested_goals,
            result,
        }
    }
}

struct CachedResult {
    required_depth: usize,
    nested_goals: NestedGoals,
    result: u32,
}

#[derive(Default)]
struct CacheEntry {
    success: Option<CachedResult>,
    with_overflow: HashMap<usize, CachedResult>,
}

/// rustc_type_ir/src/search_graph/global_cache.rs:19,80: success requires enough
/// depth; stack overflow requires exactly the same available depth.
#[derive(Default)]
struct GlobalCache {
    entries: HashMap<u32, CacheEntry>,
}

pub struct SearchGraph {
    config: SearchGraphConfig,
    stack: Vec<StackEntry>,
    provisional_cache: HashMap<u32, Vec<ProvisionalCacheEntry>>,
    global_cache: GlobalCache,
}

enum UpdateParent<'a> {
    Ordinary(&'a NestedGoals),
    CycleOnStack(u32),
    ProvisionalCacheHit,
}

#[derive(Clone, Copy)]
enum RebaseReason {
    NoCycleUsages,
    Ambiguity(u32),
    Overflow,
    ReachedFixpoint(Option<PathKind>),
}

impl SearchGraph {
    pub fn new(config: SearchGraphConfig) -> Self {
        assert!(config.fixpoint_step_limit > 0);
        assert!(config.divide_depth_on_overflow > 0);
        Self {
            config,
            stack: Vec::new(),
            provisional_cache: HashMap::new(),
            global_cache: GlobalCache::default(),
        }
    }

    pub fn is_empty(&self) -> bool {
        if self.stack.is_empty() {
            assert!(self.provisional_cache.is_empty());
            true
        } else {
            false
        }
    }

    pub fn debug_current_depth(&self) -> usize {
        self.stack.len()
    }

    pub fn evaluate(&mut self, delegate: &mut dyn SearchGraphDelegate, input: u32) -> u32 {
        let step = if delegate.is_coinductive(input) {
            PathKind::Coinductive
        } else {
            PathKind::Inductive
        };
        self.evaluate_goal(delegate, input, step)
    }

    fn cycle_path_kind(stack: &[StackEntry], step: PathKind, head: usize) -> PathKind {
        let mut path = step;
        for entry in &stack[head + 1..] {
            path = path.extend(entry.step);
        }
        path
    }

    /// rustc_type_ir/src/search_graph/mod.rs:619. A provisional hit intentionally
    /// carries no nested goals: its applicability is already deterministic.
    fn update_parent(
        stack: &mut [StackEntry],
        step: PathKind,
        required_depth: usize,
        heads: &CycleHeads,
        overflow: bool,
        context: UpdateParent<'_>,
    ) {
        let parent_index = match stack.len().checked_sub(1) {
            Some(i) => i,
            None => return,
        };
        let parent = &mut stack[parent_index];
        parent.required_depth = parent.required_depth.max(required_depth + 1);
        parent.encountered_overflow |= overflow;
        for (&index, head) in &heads.0 {
            if let Some(candidate) = &mut parent.candidate_usages {
                candidate.usages.entry(index).or_default().add_nested(head.usages);
            }
            if index < parent_index {
                parent.heads.insert(index, head.paths.extend(step), head.usages);
            } else {
                assert_eq!(index, parent_index);
                parent.usages.get_or_insert_default().add_nested(head.usages);
            }
        }
        let depends_on_cycle = match context {
            UpdateParent::Ordinary(nested) => {
                parent.nested_goals.extend_child(step, nested);
                !nested.0.is_empty()
            }
            UpdateParent::CycleOnStack(head) => {
                parent.nested_goals.insert(head, PathsToNested::from_path(step));
                true
            }
            UpdateParent::ProvisionalCacheHit => true,
        };
        if depends_on_cycle {
            parent.nested_goals.insert(parent.input, PathsToNested::EMPTY);
        }
    }

    /// A candidate of the current goal is being evaluated (between enter_single_candidate and
    /// finish_single_candidate).
    pub fn in_single_candidate(&self) -> bool {
        self.stack.last().map_or(false, |e| e.candidate_usages.is_some())
    }

    pub fn enter_single_candidate(&mut self) {
        let previous = self
            .stack
            .last_mut()
            .unwrap()
            .candidate_usages
            .replace(CandidateHeadUsages::default());
        assert!(previous.is_none());
    }

    pub fn finish_single_candidate(&mut self) -> CandidateHeadUsages {
        self.stack.last_mut().unwrap().candidate_usages.take().unwrap()
    }

    /// Deliberately mirror rustc_type_ir/src/search_graph/mod.rs:721's copy
    /// semantics: self-head usages are kept; ancestor usages are removed.
    pub fn ignore_candidate_head_usages(&mut self, candidate: CandidateHeadUsages) {
        let index = self.stack.len() - 1;
        let entry = &mut self.stack[index];
        for (head_index, usages) in candidate.usages {
            if head_index == index {
                entry.usages.unwrap().ignore(usages);
            } else {
                entry.heads.0.get_mut(&head_index).unwrap().usages.ignore(usages);
            }
        }
    }

    /// Explicit paths support coherence's unknown steps and forced ambiguity.
    /// rustc_type_ir/src/search_graph/mod.rs:759: depth, provisional cache,
    /// global cache, stack cycle, computation, then cache insertion in that order.
    pub fn evaluate_goal(
        &mut self,
        delegate: &mut dyn SearchGraphDelegate,
        input: u32,
        step: PathKind,
    ) -> u32 {
        let available_depth = match self.stack.last() {
            None => self.config.recursion_limit,
            Some(parent) if parent.available_depth == 0 => {
                let parent = self.stack.last_mut().unwrap();
                parent.encountered_overflow = true;
                parent.nested_goals.insert(parent.input, PathsToNested::EMPTY);
                return delegate.stack_overflow_result(input);
            }
            Some(parent) if parent.encountered_overflow => {
                parent.available_depth / self.config.divide_depth_on_overflow
            }
            Some(parent) => parent.available_depth - 1,
        };
        if let Some(result) = self.lookup_provisional(input, step) {
            return result;
        }
        if let Some(result) = self.lookup_global(input, step, available_depth) {
            return result;
        }
        if let Some(result) = self.check_cycle(delegate, input, step) {
            return result;
        }
        self.stack.push(StackEntry {
            input,
            step,
            available_depth,
            required_depth: 0,
            provisional_result: None,
            heads: CycleHeads::default(),
            encountered_overflow: false,
            usages: None,
            candidate_usages: None,
            nested_goals: NestedGoals::default(),
        });
        let evaluation = self.evaluate_fixpoint(delegate, input);
        Self::update_parent(
            &mut self.stack,
            step,
            evaluation.required_depth,
            &evaluation.heads,
            evaluation.encountered_overflow,
            UpdateParent::Ordinary(&evaluation.nested_goals),
        );
        let result = evaluation.result;
        if evaluation.heads.0.is_empty() {
            if !delegate.can_cache_global(input, result) { return result; }
            let entry = self.global_cache.entries.entry(input).or_default();
            let cached = CachedResult {
                result,
                required_depth: evaluation.required_depth,
                nested_goals: evaluation.nested_goals,
            };
            let previous = if evaluation.encountered_overflow {
                entry.with_overflow.insert(evaluation.required_depth, cached)
            } else {
                entry.success.replace(cached)
            };
            if let Some(previous) = previous {
                assert_eq!(previous.result, result);
            }
        } else {
            let path_from_head =
                Self::cycle_path_kind(&self.stack, step, evaluation.heads.highest().unwrap());
            self.provisional_cache
                .entry(input)
                .or_default()
                .push(ProvisionalCacheEntry {
                    encountered_overflow: evaluation.encountered_overflow,
                    heads: evaluation.heads,
                    path_from_head,
                    result,
                });
        }
        result
    }

    fn check_cycle(
        &mut self,
        delegate: &mut dyn SearchGraphDelegate,
        input: u32,
        step: PathKind,
    ) -> Option<u32> {
        let mut head_index = None;
        for i in 0..self.stack.len() {
            if self.stack[i].input == input {
                head_index = Some(i);
                break;
            }
        }
        let index = head_index?;
        let path = Self::cycle_path_kind(&self.stack, step, index);
        let mut usages = HeadUsages::default();
        usages.add_usage(path);
        let mut heads = CycleHeads::default();
        heads.insert(index, PathsToNested::from_path(step), usages);
        Self::update_parent(
            &mut self.stack,
            step,
            0,
            &heads,
            false,
            UpdateParent::CycleOnStack(input),
        );
        Some(match self.stack[index].provisional_result {
            Some(result) => result,
            None => delegate.initial_provisional_result(path, input),
        })
    }

    fn lookup_provisional(&mut self, input: u32, step: PathKind) -> Option<u32> {
        let entries = self.provisional_cache.get(&input)?;
        for entry in entries {
            let head_index = entry.heads.highest().unwrap();
            if entry.encountered_overflow {
                match self.stack.last().unwrap().heads.lowest() {
                    Some(lowest) if lowest <= head_index => {}
                    _ => continue,
                }
            }
            if entry.path_from_head == Self::cycle_path_kind(&self.stack, step, head_index) {
                Self::update_parent(
                    &mut self.stack,
                    step,
                    0,
                    &entry.heads,
                    entry.encountered_overflow,
                    UpdateParent::ProvisionalCacheHit,
                );
                return Some(entry.result);
            }
        }
        None
    }

    /// rustc_type_ir/src/search_graph/mod.rs:1135: replaying a global entry must
    /// neither encounter a stack cycle nor use an applicable provisional entry.
    fn candidate_is_applicable(&self, step: PathKind, nested: &NestedGoals) -> bool {
        if nested.0.is_empty() {
            return true;
        }
        for entry in &self.stack {
            if nested.0.contains_key(&entry.input) {
                return false;
            }
        }
        for (&input, &paths) in &nested.0 {
            if let Some(entries) = self.provisional_cache.get(&input) {
                for entry in entries {
                    if entry.encountered_overflow {
                        continue;
                    }
                    let path = Self::cycle_path_kind(&self.stack, step, entry.heads.highest().unwrap());
                    if paths.extend(path).contains(entry.path_from_head) {
                        return false;
                    }
                }
            }
        }
        true
    }

    fn lookup_global(&mut self, input: u32, step: PathKind, depth: usize) -> Option<u32> {
        let entry = self.global_cache.entries.get(&input)?;
        let mut selected = None;
        if let Some(success) = &entry.success {
            if depth >= success.required_depth && self.candidate_is_applicable(step, &success.nested_goals) {
                selected = Some((success, false));
            }
        }
        if selected.is_none() {
            if let Some(overflow) = entry.with_overflow.get(&depth) {
                if self.candidate_is_applicable(step, &overflow.nested_goals) {
                    selected = Some((overflow, true));
                }
            }
        }
        let (cached, overflow) = selected?;
        Self::update_parent(
            &mut self.stack,
            step,
            cached.required_depth,
            &CycleHeads::default(),
            overflow,
            UpdateParent::Ordinary(&cached.nested_goals),
        );
        Some(cached.result)
    }

    fn clear_dependent_provisional_results(&mut self) {
        let rerun_index = self.stack.len();
        self.provisional_cache.retain(|_, entries| {
            entries.retain(|entry| {
                let (&head, data) = entry.heads.0.last_key_value().unwrap();
                head != rerun_index || data.usages.is_empty()
            });
            !entries.is_empty()
        });
    }

    /// rustc_type_ir/src/search_graph/mod.rs:962: rebase all dependencies onto
    /// the popped head's own heads, checking that every cycle keeps its kind.
    /// Ambiguity and fixpoint overflow taint dependent responses instead of
    /// discarding them, which prevents exponential recomputation.
    fn rebase(&mut self, delegate: &mut dyn SearchGraphDelegate, popped: &StackEntry, reason: RebaseReason) {
        let popped_index = self.stack.len();
        let stack = &self.stack;
        self.provisional_cache.retain(|&input, entries| {
            entries.retain_mut(|entry| {
                if entry.heads.highest().unwrap() != popped_index {
                    assert!(entry.heads.highest().unwrap() < popped_index);
                    return true;
                }
                let (_, popped_head) = entry.heads.0.pop_last().unwrap();
                if popped_head.usages.is_empty() {
                    for &index in popped.heads.0.keys() {
                        entry
                            .heads
                            .insert(index, PathsToNested::EMPTY, HeadUsages::default());
                    }
                } else {
                    let ep = popped_head.paths;
                    for (&index, head) in &popped.heads.0 {
                        let ph = head.paths;
                        let hp = Self::cycle_path_kind(stack, popped.step, index);
                        let he = hp.extend(entry.path_from_head);
                        for ph_path in PATHS {
                            if !ph.contains(ph_path) {
                                continue;
                            }
                            let hph = hp.extend(ph_path);
                            for ep_path in PATHS {
                                if !ep.contains(ep_path) {
                                    continue;
                                }
                                let heph = ep_path.extend(he).extend(ph_path);
                                if hph != heph {
                                    return false;
                                }
                            }
                        }
                        entry.heads.insert(index, ep.extend_paths(ph), head.usages);
                    }
                    match reason {
                        RebaseReason::NoCycleUsages => return false,
                        RebaseReason::Ambiguity(info) => {
                            entry.result = delegate.propagate_ambiguity(input, info)
                        }
                        RebaseReason::Overflow => entry.result = delegate.fixpoint_overflow_result(input),
                        RebaseReason::ReachedFixpoint(None) => {}
                        RebaseReason::ReachedFixpoint(Some(path)) => {
                            if !popped_head.usages.is_single(path) {
                                return false;
                            }
                        }
                    }
                }
                let Some(head) = entry.heads.highest() else {
                    return false;
                };
                entry.path_from_head =
                    entry
                        .path_from_head
                        .extend(Self::cycle_path_kind(stack, popped.step, head));
                true
            });
            !entries.is_empty()
        });
    }

    /// rustc_type_ir/src/search_graph/mod.rs:1314: rerun every cycle head, carry
    /// depth/nested-goal/dependency metadata across iterations, and reset usages.
    fn evaluate_fixpoint(&mut self, delegate: &mut dyn SearchGraphDelegate, input: u32) -> EvaluationResult {
        let mut encountered_overflow = false;
        let mut iteration = 0;
        loop {
            let result = delegate.compute(self, input);
            let mut entry = self.stack.pop().unwrap();
            assert_eq!(entry.input, input);
            assert!(entry.candidate_usages.is_none(), "unfinished candidate");
            encountered_overflow |= entry.encountered_overflow;
            let Some(usages) = entry.usages else {
                return EvaluationResult::finalize(entry, encountered_overflow, result);
            };
            let fixpoint = match entry.provisional_result {
                Some(previous) if previous == result => Some(None),
                Some(_) => None,
                None => match delegate.is_initial_provisional_result(result) {
                    Some(path) if usages.is_single(path) => Some(Some(path)),
                    _ => None,
                },
            };
            let reason = if let Some(fixpoint) = fixpoint {
                Some(RebaseReason::ReachedFixpoint(fixpoint))
            } else if usages.is_empty() {
                Some(RebaseReason::NoCycleUsages)
            } else {
                delegate.is_ambiguous_result(result).map(RebaseReason::Ambiguity)
            };
            if let Some(reason) = reason {
                self.rebase(delegate, &entry, reason);
                return EvaluationResult::finalize(entry, encountered_overflow, result);
            }
            iteration += 1;
            if iteration >= self.config.fixpoint_step_limit {
                let result = delegate.fixpoint_overflow_result(input);
                self.rebase(delegate, &entry, RebaseReason::Overflow);
                return EvaluationResult::finalize(entry, encountered_overflow, result);
            }
            self.clear_dependent_provisional_results();
            entry.provisional_result = Some(result);
            entry.encountered_overflow = false;
            entry.usages = Some(HeadUsages::default());
            self.stack.push(entry);
        }
    }
}

#[cfg(test)]
mod tests;
