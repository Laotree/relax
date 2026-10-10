// ported from N:rustc_middle/src/dep_graph/graph.rs @8d1a764
//! Demand-driven, revisioned queries. Providers are ordinary functions; typed values
//! and key interners live in `QueryTable`, while this engine sees only `QueryId`.
//! The caller's force function dispatches a kind and its interned key back to a query.
//! rustc_middle/src/dep_graph/dep_node.rs:160 uses a per-kind force vtable.
//!
//! One engine owns one set of tables. Input registration and edits need `&mut` access
//! to the engine, so no query can overlap an edit. The owning context must update its
//! input values under that same exclusive borrow. Providers must propagate query errors
//! and must read all result-affecting state through queries or registered inputs.

mod dep_graph;
mod job;
mod table;

pub use dep_graph::{DepKind, DepNode, DepNodeColor, DepNodeIndex, Fingerprint};
pub use table::QueryTable;
pub use job::set_wait_release;

use crate::fxhash::HashMap;
use dep_graph::{DepGraph, TaskDeps, TaskGuard, TaskReads};
use job::{ActiveJobGuard, QueryJob, QueryLatch, WaitGuard};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct QueryId {
    pub kind: u16,
    pub key: u32,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Cycle {
    /// The first query is repeated at the end to show the closing edge.
    pub stack: Vec<QueryId>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum QueryError {
    Cycle(Cycle),
    Poisoned(QueryId),
    MissingInput(QueryId),
    MissingQuery(QueryId),
    IdentityConflict(QueryId),
    KindConflict(u16),
    WrongEngine,
    ForceDidNotComplete(QueryId),
}

static NEXT_ID: AtomicU64 = AtomicU64::new(1);

pub(super) fn next_id() -> u64 {
    NEXT_ID.fetch_add(1, Ordering::Relaxed)
}

#[derive(Default)]
struct State {
    graph: DepGraph,
    jobs: Vec<QueryJob>,
    // Zero denotes an input kind; other owners are typed table identities.
    kinds: HashMap<u16, u64>,
}

pub struct QueryEngine {
    id: u64,
    revision: u64,
    state: Mutex<State>,
    task_reads: Mutex<Vec<TaskReads>>,
    empty_anon: std::sync::OnceLock<DepNodeIndex>,
    /// Input nodes as read (index, fingerprint): every query reads inputs, and taking `state`
    /// for each read serialised the parallel `relax check`. Inputs change only through
    /// `set_input` (`&mut self`), which clears this.
    inputs: crate::conc::ShardMap<QueryId, (DepNodeIndex, Fingerprint)>,
}

impl Default for QueryEngine {
    fn default() -> Self {
        Self::new()
    }
}

impl QueryEngine {
    pub fn new() -> Self {
        Self { id: next_id(), revision: 1, state: Mutex::new(State::default()), task_reads: Mutex::new(Vec::new()), empty_anon: Default::default(), inputs: Default::default() }
    }

    pub fn revision(&self) -> u64 {
        self.revision
    }

    fn claim_kind(&self, kind: u16, owner: u64) -> Result<(), QueryError> {
        let mut state = self.state.lock().unwrap_or_else(|e| e.into_inner());
        if let Some(&existing) = state.kinds.get(&kind) {
            if existing != owner {
                return Err(QueryError::KindConflict(kind));
            }
        } else {
            state.kinds.insert(kind, owner);
        }
        Ok(())
    }

    fn intern(&self, query: QueryId, key: Fingerprint, eval_always: bool) -> Result<DepNodeIndex, QueryError> {
        let mut state = self.state.lock().unwrap_or_else(|e| e.into_inner());
        let index = state.graph.intern(query, key, eval_always)?;
        while state.jobs.len() < state.graph.nodes.len() {
            state.jobs.push(QueryJob::default());
        }
        Ok(index)
    }

    /// The owner assigns an input key index and supplies its stable identity separately.
    pub fn register_input(&mut self, kind: u16, key: u32, stable_key: Fingerprint) -> Result<(), QueryError> {
        self.claim_kind(kind, 0)?;
        self.intern(QueryId { kind, key }, stable_key, true)?;
        Ok(())
    }

    /// Each changed input starts a revision. Equal fingerprints leave the revision alone.
    /// Inputs are eval_always roots (rustc_middle/src/dep_graph/graph.rs:334,921).
    pub fn set_input(&mut self, kind: u16, key: u32, fingerprint: Fingerprint) -> Result<(), QueryError> {
        let query = QueryId { kind, key };
        self.inputs.clear();
        let state = self.state.get_mut().unwrap_or_else(|e| e.into_inner());
        let &index = state.graph.indices.get(&query).ok_or(QueryError::MissingInput(query))?;
        let node = &mut state.graph.nodes[index.0 as usize];
        if !node.eval_always {
            return Err(QueryError::KindConflict(kind));
        }
        if node.fingerprint == Some(fingerprint) {
            return Ok(());
        }
        self.revision = self.revision.checked_add(1).expect("query revision limit");
        node.fingerprint = Some(fingerprint);
        node.verified_at = self.revision;
        node.changed_at = self.revision;
        state.graph.compact();
        Ok(())
    }

    pub fn input(&self, kind: u16, key: u32) -> Result<Fingerprint, QueryError> {
        let query = QueryId { kind, key };
        let (index, fingerprint) = match self.inputs.get(&query) {
            Some(x) => x,
            None => {
                let state = self.state.lock().unwrap_or_else(|e| e.into_inner());
                let &index = state.graph.indices.get(&query).ok_or(QueryError::MissingInput(query))?;
                let node = &state.graph.nodes[index.0 as usize];
                if !node.eval_always {
                    return Err(QueryError::KindConflict(kind));
                }
                let x = (index, node.fingerprint.ok_or(QueryError::MissingInput(query))?);
                self.inputs.insert(query, x);
                x
            }
        };
        self.read_index(index);
        Ok(fingerprint)
    }

    /// rustc_middle/src/ty/context/tls.rs:49-58: an independent context owns
    /// its task stack. Nested compiler invocations restore the enclosing query.
    pub fn enter_context<R>(&self, op: impl FnOnce() -> R) -> R {
        if dep_graph::in_context(self.id) { return op(); }
        let frame = TaskDeps::new(self.id, None, false);
        let _guard = TaskGuard::enter(&frame, &self.task_reads);
        op()
    }

    /// Every value read, including a memo hit, passes here (graph.rs:450 in rustc).
    pub fn read_index(&self, index: DepNodeIndex) {
        dep_graph::read_index(self.id, index, &self.task_reads);
    }

    /// graph.rs:347-365,405-481: retain the task's ordered reads and record
    /// its node in the caller. Cached consumers must call read_index again.
    pub fn with_anon_task<R>(&self, op: &mut dyn FnMut() -> R) -> (R, DepNodeIndex) {
        crate::solver_work::count(crate::solver_work::ANON_TASKS);
        let frame = TaskDeps::new(self.id, dep_graph::current_job(self.id), true);
        let task = TaskGuard::enter(&frame, &self.task_reads);
        let result = op();
        let mut index = None;
        task.with_reads(&mut |reads| {
            // rustc_middle dep_graph/graph.rs: zero/single-read tasks reuse a node.
            // intern_anon already gives the empty set revision-independent identity.
            let intern = || {
                crate::solver_work::count(crate::solver_work::ANON_LOCKS);
                let mut state = self.state.lock().unwrap_or_else(|e| e.into_inner());
                let index = state.graph.intern_anon(self.revision, reads);
                while state.jobs.len() < state.graph.nodes.len() { state.jobs.push(QueryJob::default()); }
                index
            };
            index = Some(match reads {
                [only] => DepNodeIndex(*only),
                [] => *self.empty_anon.get_or_init(intern),
                _ => intern(),
            });
        });
        drop(task);
        let index = index.unwrap();
        self.read_index(index);
        (result, index)
    }

    fn with_task(
        &self,
        index: DepNodeIndex,
        compute: &mut dyn FnMut() -> Result<Fingerprint, QueryError>,
        force: &dyn Fn(QueryId) -> Result<(), QueryError>,
    ) -> Result<(), QueryError> {
        loop {
            let parent = dep_graph::current_job(self.id);
            let latch = {
                let mut state = self.state.lock().unwrap_or_else(|e| e.into_inner());
                let node = &state.graph.nodes[index.0 as usize];
                if node.error_at == self.revision {
                    if let Some(error) = &node.error {
                        return Err(error.clone());
                    }
                }
                if node.verified_at == self.revision {
                    return Ok(());
                }
                if let Some(parent) = parent {
                    job::check_cycle(&state, parent, index)?;
                    state.jobs[parent.0 as usize].waiting_on = Some(index);
                }
                let job = &mut state.jobs[index.0 as usize];
                if job.active {
                    Some(Arc::clone(job.latch.get_or_insert_with(|| Arc::new(QueryLatch::new()))))
                } else {
                    job.active = true;
                    None
                }
            };
            let _waiting = WaitGuard { engine: self, parent };
            if let Some(latch) = latch {
                match latch.wait() {
                    job::Completion::Value(result) => return result,
                    job::Completion::Retry => { crate::preempt::point(); continue; },
                }
            }
            let mut job = ActiveJobGuard { engine: self, index, finished: false };
            let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                // Validation must not leak forced dependencies into the caller's read set.
                let frame = TaskDeps::new(self.id, Some(index), false);
                let task = TaskGuard::enter(&frame, &self.task_reads);
                (|| {
                    if self.try_mark_green(index, force)? {
                        return Ok(());
                    }
                    task.record();
                    let fingerprint = compute()?;
                    task.with_reads(&mut |reads| {
                        self.state.lock().unwrap_or_else(|e| e.into_inner()).graph.complete(index, self.revision, fingerprint, reads);
                    });
                    Ok(())
                })()
            }));
            match result {
                Ok(result) => { job.complete(result.clone()); return result; }
                Err(payload) => {
                    // The task/read frame has already dropped, before waiters may retry.
                    if crate::preempt::is_cancelled(&*payload) {
                        drop(_waiting);
                        job.cancel();
                    }
                    std::panic::resume_unwind(payload);
                }
            }
        }
    }

    /// Walk previous reads in order, stopping at the first changed dependency.
    /// rustc_middle/src/dep_graph/graph.rs:897,921,938 (try_mark_previous_green).
    /// Compare change revisions against this node's verification revision, not just
    /// this revision's color: lazy nodes may have missed intermediate revisions.
    fn try_mark_green(&self, index: DepNodeIndex, force: &dyn Fn(QueryId) -> Result<(), QueryError>) -> Result<bool, QueryError> {
        let (verified_at, edges) = {
            let state = self.state.lock().unwrap_or_else(|e| e.into_inner());
            let node = &state.graph.nodes[index.0 as usize];
            if node.fingerprint.is_none() {
                return Ok(false);
            }
            (node.verified_at, node.edges.clone())
        };
        for edge in edges {
            let (dep, query, eval_always, current, changed_at) = {
                let state = self.state.lock().unwrap_or_else(|e| e.into_inner());
                let dep = DepNodeIndex(state.graph.edges[edge]);
                let node = &state.graph.nodes[dep.0 as usize];
                (dep, node.query, node.eval_always, node.verified_at == self.revision, node.changed_at)
            };
            if eval_always || current {
                if changed_at > verified_at {
                    return Ok(false);
                }
                continue;
            }
            let Some(query) = query else {
                if !self.try_mark_green(dep, force)? { return Ok(false); }
                continue;
            };
            force(query)?;
            let state = self.state.lock().unwrap_or_else(|e| e.into_inner());
            let node = &state.graph.nodes[dep.0 as usize];
            if node.verified_at != self.revision {
                return Err(QueryError::ForceDidNotComplete(query));
            }
            if node.changed_at > verified_at {
                return Ok(false);
            }
        }
        self.state.lock().unwrap_or_else(|e| e.into_inner()).graph.nodes[index.0 as usize].verified_at = self.revision;
        Ok(true)
    }

    pub fn dep_node(&self, query: QueryId) -> Option<DepNode> {
        let state = self.state.lock().unwrap_or_else(|e| e.into_inner());
        let index = *state.graph.indices.get(&query)?;
        Some(state.graph.nodes[index.0 as usize].identity)
    }

    pub fn dependencies(&self, query: QueryId) -> Vec<QueryId> {
        let state = self.state.lock().unwrap_or_else(|e| e.into_inner());
        let mut result = Vec::new();
        if let Some(index) = state.graph.indices.get(&query) {
            for &edge in &state.graph.edges[state.graph.nodes[index.0 as usize].edges.clone()] {
                if let Some(query) = state.graph.nodes[edge as usize].query { result.push(query); }
            }
        }
        result
    }

    pub fn color(&self, query: QueryId) -> DepNodeColor {
        let state = self.state.lock().unwrap_or_else(|e| e.into_inner());
        let Some(index) = state.graph.indices.get(&query) else { return DepNodeColor::Unknown };
        let node = &state.graph.nodes[index.0 as usize];
        if node.error_at == self.revision && node.error.is_some() {
            DepNodeColor::Red
        } else if node.fingerprint.is_none() || (!node.eval_always && node.verified_at != self.revision) {
            DepNodeColor::Unknown
        } else if node.changed_at == self.revision {
            DepNodeColor::Red
        } else {
            DepNodeColor::Green
        }
    }
}

#[cfg(test)]
mod tests;
