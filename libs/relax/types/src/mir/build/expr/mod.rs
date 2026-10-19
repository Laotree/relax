//! rustc_mir_build/src/builder/expr/*: expression lowering entry points. Frozen seam (I1): the signatures
//! are what `matches/` (lane C) and the statement/block lowering call; bodies land in S3.
use super::builder::{Builder, TempLifetime};
use super::cfg::BlockAnd;
use super::place::PlaceBuilder;
use super::thir::ExprId;
use super::{BuildResult, UnsupportedReason};
use crate::mir::{BasicBlock, ConstOperand, Local, LocalInfo, Mutability, Operand, Place, Rvalue};
use crate::region_scope::ScopeId;

impl Builder<'_> {
    fn expr_not_yet<T>(&self, expr: ExprId, what: &'static str) -> BuildResult<T> {
        let span = self.thir.thir[expr].span;
        Err(self.error(span, UnsupportedReason::NotYetBuilt(what)))
    }
    /// as_place.rs:`as_place`.
    pub fn as_place(&mut self, _block: BasicBlock, expr: ExprId) -> BuildResult<BlockAnd<Place>> {
        self.expr_not_yet(expr, "as_place")
    }
    /// as_place.rs:`as_place_builder`: the place may still be rooted at an upvar.
    pub fn as_place_builder(&mut self, _block: BasicBlock, expr: ExprId) -> BuildResult<BlockAnd<PlaceBuilder>> {
        self.expr_not_yet(expr, "as_place_builder")
    }
    /// as_place.rs:`as_read_only_place`.
    pub fn as_read_only_place(&mut self, _block: BasicBlock, expr: ExprId) -> BuildResult<BlockAnd<Place>> {
        self.expr_not_yet(expr, "as_read_only_place")
    }
    /// as_place.rs:`as_read_only_place_builder`.
    pub fn as_read_only_place_builder(&mut self, _block: BasicBlock, expr: ExprId) -> BuildResult<BlockAnd<PlaceBuilder>> {
        self.expr_not_yet(expr, "as_read_only_place_builder")
    }
    /// as_operand.rs:`as_operand`.
    pub fn as_operand(
        &mut self,
        _block: BasicBlock,
        _scope: TempLifetime,
        expr: ExprId,
        _local_info: LocalInfo,
        _needs_temporary: bool,
    ) -> BuildResult<BlockAnd<Operand>> {
        self.expr_not_yet(expr, "as_operand")
    }
    /// as_rvalue.rs:`as_rvalue`.
    pub fn as_rvalue(&mut self, _block: BasicBlock, _scope: TempLifetime, expr: ExprId) -> BuildResult<BlockAnd<Rvalue>> {
        self.expr_not_yet(expr, "as_rvalue")
    }
    /// as_temp.rs:`as_temp`.
    pub fn as_temp(&mut self, _block: BasicBlock, _temp_lifetime: TempLifetime, expr: ExprId, _mutability: Mutability) -> BuildResult<BlockAnd<Local>> {
        self.expr_not_yet(expr, "as_temp")
    }
    /// as_constant.rs:`as_constant`.
    pub fn as_constant(&mut self, expr: ExprId) -> BuildResult<ConstOperand> {
        self.expr_not_yet(expr, "as_constant")
    }
    /// into.rs:`expr_into_dest`.
    pub fn expr_into_dest(&mut self, _destination: Place, _block: BasicBlock, expr: ExprId) -> BuildResult<BlockAnd<()>> {
        self.expr_not_yet(expr, "expr_into_dest")
    }
    /// stmt.rs:`stmt_expr`.
    pub fn stmt_expr(&mut self, _block: BasicBlock, expr: ExprId, _statement_scope: Option<ScopeId>) -> BuildResult<BlockAnd<()>> {
        self.expr_not_yet(expr, "stmt_expr")
    }
}
