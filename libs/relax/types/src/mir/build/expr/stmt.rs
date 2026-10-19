//! rustc_mir_build/src/builder/expr/stmt.rs. Owner: lane B.
use crate::mir::build::builder::{Builder};
use crate::mir::build::cfg::BlockAnd;
use crate::mir::build::thir::ExprId;
use crate::mir::build::{BuildResult};
use crate::mir::{BasicBlock};
use crate::region_scope::ScopeId;

impl Builder<'_> {
    /// stmt.rs:`stmt_expr`.
    pub fn stmt_expr(&mut self, _block: BasicBlock, expr: ExprId, _statement_scope: Option<ScopeId>) -> BuildResult<BlockAnd<()>> {
        self.expr_not_yet(expr, "stmt_expr")
    }
}
