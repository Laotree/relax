//! rustc_mir_build/src/builder/matches/*: pattern matching lowering. Owned by lane C (S4); this file holds
//! the entry points the rest of the builder calls (frozen at I1). Lane C replaces the bodies and may add
//! files under `matches/`.
use super::builder::Builder;
use super::cfg::BlockAnd;
use super::scope::BreakableTarget;
use super::thir::{ArmId, ExprId, LocalVarId, Pat};
use super::{BuildResult, UnsupportedReason};
use crate::mir::{BasicBlock, Place, SourceInfo, Span};
use crate::region_scope::ScopeId;

impl Builder<'_> {
    fn matches_not_yet<T>(&self, span: Span, what: &'static str) -> BuildResult<T> {
        Err(self.error(span, UnsupportedReason::NotYetBuilt(what)))
    }
    /// matches/mod.rs:`match_expr`: lower `match scrutinee { arms }` into `destination`.
    pub fn match_expr(
        &mut self,
        _destination: Place,
        _block: BasicBlock,
        scrutinee: ExprId,
        _arms: &[ArmId],
        span: Span,
        _scrutinee_span: Span,
    ) -> BuildResult<BlockAnd<()>> {
        let _ = scrutinee;
        self.matches_not_yet(span, "match_expr")
    }
    /// matches/mod.rs:`expr_into_pattern`: `let pat = init;` where `init` is an expression.
    pub fn expr_into_pattern(&mut self, _block: BasicBlock, _irrefutable_pat: &Pat, initializer: ExprId) -> BuildResult<BlockAnd<()>> {
        let span = self.thir.thir[initializer].span;
        self.matches_not_yet(span, "expr_into_pattern")
    }
    /// matches/mod.rs:`place_into_pattern`: bind `pat` against an already evaluated place.
    pub fn place_into_pattern(&mut self, _block: BasicBlock, irrefutable_pat: &Pat, _initializer: Place, _set_match_place: bool) -> BuildResult<BlockAnd<()>> {
        self.matches_not_yet(irrefutable_pat.span, "place_into_pattern")
    }
    /// matches/mod.rs:`then_else_break`: evaluate `expr` (a condition possibly containing `let`) and branch;
    /// returns (then block, else block) after scheduling the else exit with `break_for_else`.
    pub fn then_else_break(
        &mut self,
        _block: BasicBlock,
        expr: ExprId,
        _temp_scope_override: Option<ScopeId>,
        _break_scope: ScopeId,
        _variable_source_info: SourceInfo,
    ) -> BuildResult<BlockAnd<()>> {
        let span = self.thir.thir[expr].span;
        self.matches_not_yet(span, "then_else_break")
    }
    /// matches/mod.rs:`declare_bindings`: declare the locals of every binding of `pattern`.
    pub fn declare_bindings(
        &mut self,
        _visibility_scope: Option<crate::mir::SourceScope>,
        _scope_span: Span,
        pattern: &Pat,
        _guard: Option<ExprId>,
        _opt_match_place: Option<(Option<&Place>, Span)>,
    ) -> BuildResult<Option<crate::mir::SourceScope>> {
        self.matches_not_yet(pattern.span, "declare_bindings")
    }
    /// matches/mod.rs:`storage_live_binding`.
    pub fn storage_live_binding(
        &mut self,
        _block: BasicBlock,
        var: LocalVarId,
        span: Span,
        _for_guard: super::builder::ForGuard,
        _schedule_drop: bool,
    ) -> BuildResult<crate::mir::Place> {
        let _ = var;
        self.matches_not_yet(span, "storage_live_binding")
    }
    /// matches/mod.rs:`schedule_drop_for_binding`.
    pub fn schedule_drop_for_binding(&mut self, var: LocalVarId, span: Span, _for_guard: super::builder::ForGuard) -> BuildResult<()> {
        let _ = var;
        self.matches_not_yet(span, "schedule_drop_for_binding")
    }
    /// The target `break`/`continue` of a labelled scope resolves to (used by `then_else_break`).
    pub fn breakable_target_of(&self, scope: ScopeId) -> BreakableTarget {
        BreakableTarget::Break(scope)
    }
}
