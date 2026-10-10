// ported from N:rustc_middle/src/dep_graph/graph.rs @8d1a764
use super::{QueryError, QueryId};
use crate::fxhash::{HashMap, HashSet};
use crate::sip::Sip128;
use std::cell::{Cell, RefCell};
use std::ops::Range;
use std::sync::Mutex;

/// Stable encodings must use fixed widths, explicit endianness and length prefixes.
/// rustc_middle/src/dep_graph/dep_node.rs:91 separates key and result fingerprints.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct Fingerprint(pub u128);

impl Fingerprint {
    pub fn from_bytes(bytes: &[u8]) -> Self {
        let mut hash = Sip128::new();
        hash.write(bytes);
        Self(hash.finish128())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct DepKind(pub u16);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct DepNode {
    pub kind: DepKind,
    pub key_fingerprint: Fingerprint,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct DepNodeIndex(pub u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DepNodeColor {
    Unknown,
    Red,
    Green,
}

pub(super) struct Node {
    pub query: Option<QueryId>,
    pub identity: DepNode,
    pub eval_always: bool,
    pub fingerprint: Option<Fingerprint>,
    pub verified_at: u64,
    pub changed_at: u64,
    pub edges: Range<usize>,
    pub error: Option<QueryError>,
    pub error_at: u64,
}

/// Flat edge ranges follow rustc_middle/src/dep_graph/serialized.rs:99.
/// Nodes retain their last verified revision: a lazy node can skip many edits.
#[derive(Default)]
pub(super) struct DepGraph {
    pub nodes: Vec<Node>,
    pub edges: Vec<u32>,
    pub indices: HashMap<QueryId, DepNodeIndex>,
    identities: HashMap<DepNode, DepNodeIndex>,
    live_edges: usize,
    anon_node_to_index: HashMap<(u64, Vec<u32>), DepNodeIndex>,
}

impl DepGraph {
    pub fn intern(&mut self, query: QueryId, key: Fingerprint, eval_always: bool) -> Result<DepNodeIndex, QueryError> {
        let identity = DepNode { kind: DepKind(query.kind), key_fingerprint: key };
        if let Some(&index) = self.indices.get(&query) {
            let node = &self.nodes[index.0 as usize];
            if node.identity != identity || node.eval_always != eval_always {
                return Err(QueryError::IdentityConflict(query));
            }
            return Ok(index);
        }
        if self.identities.contains_key(&identity) {
            return Err(QueryError::IdentityConflict(query));
        }
        let index = DepNodeIndex(u32::try_from(self.nodes.len()).expect("query node limit"));
        self.nodes.push(Node {
            query: Some(query),
            identity,
            eval_always,
            fingerprint: None,
            verified_at: 0,
            changed_at: 0,
            edges: 0..0,
            error: None,
            error_at: 0,
        });
        self.indices.insert(query, index);
        self.identities.insert(identity, index);
        Ok(index)
    }

    /// graph.rs:432-481: one read reuses that node; other ordered read sets
    /// are interned per session (a revision is Q1's incremental session).
    pub fn intern_anon(&mut self, revision: u64, reads: &[u32]) -> DepNodeIndex {
        if reads.len() == 1 { return DepNodeIndex(reads[0]); }
        let key = (if reads.is_empty() { 0 } else { revision }, reads.to_vec());
        if let Some(&index) = self.anon_node_to_index.get(&key) { return index; }
        let index = DepNodeIndex(u32::try_from(self.nodes.len()).expect("query node limit"));
        let mut hash = Sip128::new();
        hash.write(&key.0.to_le_bytes());
        for read in reads { hash.write(&read.to_le_bytes()); }
        self.nodes.push(Node {
            query: None,
            identity: DepNode { kind: DepKind(0), key_fingerprint: Fingerprint(hash.finish128()) },
            eval_always: false, fingerprint: None, verified_at: 0, changed_at: 0,
            edges: 0..0, error: None, error_at: 0,
        });
        self.complete(index, revision, Fingerprint(0), reads);
        self.anon_node_to_index.insert(key, index);
        index
    }

    pub fn complete(&mut self, index: DepNodeIndex, revision: u64, fingerprint: Fingerprint, reads: &[u32]) {
        let node = &mut self.nodes[index.0 as usize];
        if node.fingerprint != Some(fingerprint) {
            node.changed_at = revision;
        }
        node.fingerprint = Some(fingerprint);
        node.verified_at = revision;
        self.live_edges -= node.edges.len();
        let start = self.edges.len();
        self.edges.extend_from_slice(reads);
        node.edges = start..self.edges.len();
        self.live_edges += reads.len();
    }

    // Called only between revisions; obsolete ranges cannot grow without bound.
    pub fn compact(&mut self) {
        if self.edges.len() <= self.live_edges.saturating_mul(2) + 1024 {
            return;
        }
        let mut edges = Vec::with_capacity(self.live_edges);
        for node in &mut self.nodes {
            let start = edges.len();
            edges.extend_from_slice(&self.edges[node.edges.clone()]);
            node.edges = start..edges.len();
        }
        self.edges = edges;
    }
}

/// First-read order and deduplication follow rustc_middle/src/dep_graph/graph.rs:450.
/// Small tasks keep their reads inline, including root requests during TLS teardown.
#[derive(Default)]
pub(super) struct TaskDeps {
    engine: u64,
    job: Option<DepNodeIndex>,
    recording: bool,
    inline: [u32; 16],
    len: usize,
    spill: TaskReads,
}

/// Large read buffers belong to the engine between requests, never to TLS.
#[derive(Default)]
pub(super) struct TaskReads {
    reads: Vec<u32>,
    read_set: HashSet<u32>,
}

impl TaskDeps {
    pub fn new(engine: u64, job: Option<DepNodeIndex>, recording: bool) -> RefCell<Self> {
        RefCell::new(Self { engine, job, recording, ..Self::default() })
    }

    fn reads(&self) -> &[u32] {
        if self.len <= self.inline.len() { &self.inline[..self.len] } else { &self.spill.reads }
    }

    fn read(&mut self, index: u32, spare: &Mutex<Vec<TaskReads>>) {
        if !self.recording { return; }
        if self.len < self.inline.len() {
            if self.inline[..self.len].contains(&index) { return; }
            self.inline[self.len] = index;
        } else {
            if self.len == self.inline.len() && self.spill.read_set.is_empty() {
                self.spill = spare.lock().unwrap_or_else(|e| e.into_inner()).pop().unwrap_or_default();
                self.spill.reads.extend_from_slice(&self.inline);
                for &read in &self.inline { self.spill.read_set.insert(read); }
            }
            if !self.spill.read_set.insert(index) { return; }
            self.spill.reads.push(index);
        }
        self.len += 1;
    }
}

// rustc_middle/src/ty/context/tls.rs:12,27,49,63: TLS borrows the scoped
// implicit context. This const Cell has no destructor, so a late TLS destructor
// can start a root request just like any other caller.
thread_local! {
    static CONTEXT: Cell<*const ()> = const { Cell::new(std::ptr::null()) };
}

fn with_context<R>(op: impl FnOnce(Option<&RefCell<TaskDeps>>) -> R) -> R {
    let ptr = CONTEXT.get();
    if ptr.is_null() { return op(None); }
    // SAFETY: TaskGuard borrows the stack frame, cannot outlive it, and restores
    // this thread's previous pointer before that frame is destroyed, even on unwind.
    op(Some(unsafe { &*ptr.cast::<RefCell<TaskDeps>>() }))
}

pub(super) fn in_context(engine: u64) -> bool {
    with_context(|frame| frame.is_some_and(|frame| frame.borrow().engine == engine))
}

pub(super) fn current_job(engine: u64) -> Option<DepNodeIndex> {
    with_context(|frame| {
        let task = frame?.borrow();
        assert_eq!(task.engine, engine, "queries cannot read another engine");
        task.job
    })
}

pub(super) fn read_index(engine: u64, index: DepNodeIndex, spare: &Mutex<Vec<TaskReads>>) {
    with_context(|frame| {
        if let Some(frame) = frame {
            let mut task = frame.borrow_mut();
            assert_eq!(task.engine, engine, "queries cannot read another engine");
            task.read(index.0, spare);
        }
    });
}

pub(super) struct TaskGuard<'a> {
    frame: &'a RefCell<TaskDeps>,
    previous: *const (),
    spare: &'a Mutex<Vec<TaskReads>>,
}

impl<'a> TaskGuard<'a> {
    pub fn enter(frame: &'a RefCell<TaskDeps>, spare: &'a Mutex<Vec<TaskReads>>) -> Self {
        let previous = CONTEXT.replace((frame as *const RefCell<TaskDeps>).cast());
        Self { frame, previous, spare }
    }

    pub fn record(&self) {
        self.frame.borrow_mut().recording = true;
    }

    pub fn with_reads(&self, op: &mut dyn FnMut(&[u32])) {
        op(self.frame.borrow().reads());
    }
}

impl Drop for TaskGuard<'_> {
    fn drop(&mut self) {
        CONTEXT.set(self.previous);
        let mut task = self.frame.borrow_mut();
        if !task.spill.reads.is_empty() {
            let mut spill = std::mem::take(&mut task.spill);
            spill.reads.clear();
            spill.read_set.clear();
            self.spare.lock().unwrap_or_else(|e| e.into_inner()).push(spill);
        }
    }
}
