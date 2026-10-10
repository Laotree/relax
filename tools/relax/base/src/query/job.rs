use super::{Cycle, DepNodeIndex, QueryEngine, QueryError, State};
use std::sync::{Arc, Condvar, Mutex};

/// A live job occupies its node's flat slot; a latch is allocated only on contention.
/// rustc_middle/src/query/job.rs:17,35 uses the same lazy latch ownership.
#[derive(Default)]
pub(super) struct QueryJob {
    pub active: bool,
    pub waiting_on: Option<DepNodeIndex>,
    pub latch: Option<Arc<QueryLatch>>,
}

#[derive(Clone)]
pub(super) enum Completion {
    Value(Result<(), QueryError>),
    Retry,
}

pub(super) struct QueryLatch {
    result: Mutex<Option<Completion>>,
    ready: Condvar,
}

impl QueryLatch {
    pub fn new() -> Self {
        Self { result: Mutex::new(None), ready: Condvar::new() }
    }

    pub fn wait(&self) -> Completion {
        let mut result = self.result.lock().unwrap_or_else(|e| e.into_inner());
        while result.is_none() {
            drop(result);
            crate::preempt::point();
            result = self.result.lock().unwrap_or_else(|e| e.into_inner());
            if result.is_none() {
                result = self.ready.wait_timeout(result, std::time::Duration::from_millis(5)).unwrap_or_else(|e| e.into_inner()).0;
            }
        }
        result.as_ref().unwrap().clone()
    }

    pub fn complete(&self, result: Completion) {
        *self.result.lock().unwrap_or_else(|e| e.into_inner()) = Some(result);
        self.ready.notify_all();
    }
}

/// Both synchronous children and condvar waits are edges, as in
/// rustc_query_impl/src/job.rs:119,131,159. Insertion and cycle checking share a lock.
/// Since each running job can await only one other job, the walk is a chain.
pub(super) fn check_cycle(state: &State, parent: DepNodeIndex, target: DepNodeIndex) -> Result<(), QueryError> {
    let mut next = Some(target);
    while let Some(index) = next {
        if index == parent {
            let mut stack = vec![state.graph.nodes[parent.0 as usize].query.unwrap()];
            let mut index = target;
            while index != parent {
                stack.push(state.graph.nodes[index.0 as usize].query.unwrap());
                index = state.jobs[index.0 as usize].waiting_on.unwrap();
            }
            stack.push(state.graph.nodes[parent.0 as usize].query.unwrap());
            return Err(QueryError::Cycle(Cycle { stack }));
        }
        let job = &state.jobs[index.0 as usize];
        next = if job.active { job.waiting_on } else { None };
    }
    Ok(())
}

pub(super) struct WaitGuard<'a> {
    pub engine: &'a QueryEngine,
    pub parent: Option<DepNodeIndex>,
}

impl Drop for WaitGuard<'_> {
    fn drop(&mut self) {
        if let Some(parent) = self.parent {
            self.engine.state.lock().unwrap_or_else(|e| e.into_inner()).jobs[parent.0 as usize].waiting_on = None;
        }
    }
}

/// Unwinding poisons the node and wakes every waiter before the panic escapes.
/// rustc_query_impl/src/execution.rs:154,190,220 (ActiveJobGuard).
pub(super) struct ActiveJobGuard<'a> {
    pub engine: &'a QueryEngine,
    pub index: DepNodeIndex,
    pub finished: bool,
}

impl ActiveJobGuard<'_> {
    // Lead design round 42 extends rustc_query_impl/src/execution.rs:108-159,
    // 179-257 @8d1a764: cancellation removes the active job without publishing
    // poison or a value. Waiters retry; ordinary panic still poisons in Drop.
    pub fn cancel(&mut self) {
        let latch = {
            let mut state = self.engine.state.lock().unwrap_or_else(|e| e.into_inner());
            let job = &mut state.jobs[self.index.0 as usize];
            job.active = false;
            job.waiting_on = None;
            job.latch.take()
        };
        self.finished = true;
        if let Some(latch) = latch { latch.complete(Completion::Retry); }
    }

    pub fn complete(&mut self, result: Result<(), QueryError>) {
        let latch = {
            let mut state = self.engine.state.lock().unwrap_or_else(|e| e.into_inner());
            let node = &mut state.graph.nodes[self.index.0 as usize];
            node.error = result.as_ref().err().cloned();
            node.error_at = self.engine.revision;
            let job = &mut state.jobs[self.index.0 as usize];
            job.active = false;
            job.waiting_on = None;
            job.latch.take()
        };
        self.finished = true;
        if let Some(latch) = latch {
            latch.complete(Completion::Value(result));
        }
    }
}

impl Drop for ActiveJobGuard<'_> {
    fn drop(&mut self) {
        if !self.finished {
            let query = self.engine.state.lock().unwrap_or_else(|e| e.into_inner()).graph.nodes[self.index.0 as usize].query.unwrap();
            self.complete(Err(QueryError::Poisoned(query)));
        }
    }
}
