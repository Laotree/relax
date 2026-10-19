//! rustc_mir_build/src/builder/scope.rs: region scopes, scheduled drops, breakable scopes.
//! Frozen seam (I1): the data layout and entry-point signatures below are what pattern lowering (lane C)
//! and expression lowering call; bodies land in S3.
use super::builder::Builder;
use super::cfg::BlockAnd;
use super::thir::ExprId;
use super::{BuildResult, UnsupportedReason};
use crate::mir::{BasicBlock, Local, Place, SourceInfo, SourceScope, Span};
use crate::region_scope::ScopeId;

/// scope.rs:`DropKind`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DropKind {
    Value,
    Storage,
    ForLint,
}
#[derive(Clone, Debug)]
pub struct DropData {
    pub source_info: SourceInfo,
    pub local: Local,
    pub kind: DropKind,
}
/// One node of a drop tree: the drop and the node it falls through to (None: the root).
#[derive(Clone, Debug)]
pub struct DropNode {
    pub data: DropData,
    pub next: Option<usize>,
}
/// scope.rs:`DropTree`: drops shared by every exit (break, continue, return, unwind) of a scope.
#[derive(Clone, Debug, Default)]
pub struct DropTree {
    pub drops: Vec<DropNode>,
    /// Blocks that branch into the tree, with the node they enter at.
    pub entry_points: Vec<(Option<usize>, BasicBlock)>,
}
#[derive(Debug)]
pub struct Scope {
    pub source_scope: SourceScope,
    pub region_scope: ScopeId,
    /// Drops scheduled in this scope, in schedule order (executed in reverse).
    pub drops: Vec<DropData>,
    pub moved_locals: Vec<Local>,
}
#[derive(Debug)]
pub struct BreakableScope {
    pub region_scope: ScopeId,
    pub break_destination: Place,
    pub break_drops: DropTree,
    pub continue_drops: Option<DropTree>,
}
#[derive(Debug)]
pub struct IfThenScope {
    pub region_scope: ScopeId,
    pub else_drops: DropTree,
}
#[derive(Debug, Default)]
pub struct Scopes {
    pub scopes: Vec<Scope>,
    pub breakable_scopes: Vec<BreakableScope>,
    pub if_then_scope: Option<IfThenScope>,
    pub unwind_drops: DropTree,
    pub coroutine_drops: DropTree,
}
/// scope.rs:`BreakableTarget`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BreakableTarget {
    Continue(ScopeId),
    Break(ScopeId),
    Return,
}

impl Builder<'_> {
    fn not_yet<T>(&self, what: &'static str) -> BuildResult<T> {
        Err(self.error(Span::default(), UnsupportedReason::NotYetBuilt(what)))
    }
    /// scope.rs:`in_scope`: run `f` inside the region scope, popping (and dropping) afterwards.
    pub fn in_scope<R>(
        &mut self,
        _region_scope: (ScopeId, SourceInfo),
        f: impl FnOnce(&mut Self) -> BuildResult<BlockAnd<R>>,
    ) -> BuildResult<BlockAnd<R>> {
        let _ = f;
        self.not_yet("in_scope")
    }
    /// scope.rs:`in_opt_scope`: as `in_scope` for an expression whose scope may be absent.
    pub fn in_opt_scope<R>(
        &mut self,
        _opt_scope: Option<(ScopeId, SourceInfo)>,
        f: impl FnOnce(&mut Self) -> BuildResult<BlockAnd<R>>,
    ) -> BuildResult<BlockAnd<R>> {
        let _ = f;
        self.not_yet("in_opt_scope")
    }
    pub fn push_scope(&mut self, _region_scope: (ScopeId, SourceInfo)) -> BuildResult<()> {
        self.not_yet("push_scope")
    }
    pub fn pop_scope(&mut self, _region_scope: (ScopeId, SourceInfo), _block: BasicBlock) -> BuildResult<BlockAnd<()>> {
        self.not_yet("pop_scope")
    }
    /// scope.rs:`in_breakable_scope`: `f` returns the block after the loop body, if reachable.
    pub fn in_breakable_scope(
        &mut self,
        _loop_block: Option<BasicBlock>,
        _break_destination: Place,
        _span: Span,
        f: impl FnOnce(&mut Self) -> BuildResult<Option<BlockAnd<()>>>,
    ) -> BuildResult<BlockAnd<()>> {
        let _ = f;
        self.not_yet("in_breakable_scope")
    }
    /// scope.rs:`in_if_then_scope`: returns (then block, else block); `break_for_else` leaves through the else
    /// edge, dropping what the then-branch had scheduled.
    pub fn in_if_then_scope(
        &mut self,
        _region_scope: ScopeId,
        _span: Span,
        f: impl FnOnce(&mut Self) -> BuildResult<BlockAnd<()>>,
    ) -> BuildResult<(BasicBlock, BasicBlock)> {
        let _ = f;
        self.not_yet("in_if_then_scope")
    }
    pub fn break_for_else(&mut self, _block: BasicBlock, _source_info: SourceInfo) -> BuildResult<()> {
        self.not_yet("break_for_else")
    }
    /// scope.rs:`break_scope`: break/continue/return out of the innermost matching scope.
    pub fn break_scope(
        &mut self,
        _block: BasicBlock,
        _value: Option<ExprId>,
        _target: BreakableTarget,
        _source_info: SourceInfo,
    ) -> BuildResult<BlockAnd<()>> {
        self.not_yet("break_scope")
    }
    /// scope.rs:`schedule_drop`.
    pub fn schedule_drop(&mut self, _span: Span, _region_scope: ScopeId, _local: Local, _drop_kind: DropKind) -> BuildResult<()> {
        self.not_yet("schedule_drop")
    }
    /// scope.rs:`schedule_drop_storage_and_value`.
    pub fn schedule_drop_storage_and_value(&mut self, _span: Span, _region_scope: ScopeId, _local: Local) -> BuildResult<()> {
        self.not_yet("schedule_drop_storage_and_value")
    }
}
