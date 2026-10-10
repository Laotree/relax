use super::{Cycle, DepNodeIndex, QueryEngine, QueryError, State};
use std::sync::{Arc, Condvar, Mutex};

/// Only live jobs occupy storage; a latch is allocated only on contention.
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

/// What a thread about to wait for another thread's query gives up for the wait (true: given up)
/// and takes back after: set once by the JIT for its unit lock.
static WAIT_RELEASE: std::sync::OnceLock<(fn() -> bool, fn())> = std::sync::OnceLock::new();

pub fn set_wait_release(give_up: fn() -> bool, take_back: fn()) {
    let _ = WAIT_RELEASE.set((give_up, take_back));
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
        if let Some(done) = result.as_ref() {
            return done.clone();
        }
        // the running query may need a lock this thread holds (the JIT's unit lock, for CTFE):
        // give it up for the wait, or both threads wait for each other
        let release = WAIT_RELEASE.get();
        let released = release.is_some_and(|(give_up, _)| give_up());
        while result.is_none() {
            drop(result);
            crate::preempt::point();
            result = self.result.lock().unwrap_or_else(|e| e.into_inner());
            if result.is_none() {
                result = self.ready.wait_timeout(result, std::time::Duration::from_millis(5)).unwrap_or_else(|e| e.into_inner()).0;
            }
        }
        let done = result.as_ref().unwrap().clone();
        drop(result);
        if released {
            (release.unwrap().1)();
        }
        done
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
            let mut stack = vec![state.graph.query(parent).unwrap()];
            let mut index = target;
            while index != parent {
                stack.push(state.graph.query(index).unwrap());
                index = state.jobs[&index].waiting_on.unwrap();
            }
            stack.push(state.graph.query(parent).unwrap());
            return Err(QueryError::Cycle(Cycle { stack }));
        }
        next = state.jobs.get(&index).and_then(|job| job.waiting_on);
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
            // a drop during unwinding must not panic (the job map is sparse now)
            if let Some(job) = self.engine.state.lock().unwrap_or_else(|e| e.into_inner()).jobs.get_mut(&parent) { job.waiting_on = None; }
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
            state.jobs.remove(&self.index).unwrap().latch
        };
        self.finished = true;
        if let Some(latch) = latch { latch.complete(Completion::Retry); }
    }

    pub fn complete(&mut self, result: Result<(), QueryError>) {
        let latch = {
            let mut state = self.engine.state.lock().unwrap_or_else(|e| e.into_inner());
            match &result {
                Err(error) => { state.graph.errors.insert(self.index, (self.engine.revision, error.clone())); }
                Ok(()) => { state.graph.errors.remove(&self.index); }
            }
            state.jobs.remove(&self.index).unwrap().latch
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
            let query = self.engine.state.lock().unwrap_or_else(|e| e.into_inner()).graph.query(self.index).unwrap();
            self.complete(Err(QueryError::Poisoned(query)));
        }
    }
}
