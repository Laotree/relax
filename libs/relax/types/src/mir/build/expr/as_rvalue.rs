//! rustc_mir_build/src/builder/expr/as_rvalue.rs. Owner: lane E.
use crate::mir::build::builder::{Builder, TempLifetime};
use crate::mir::build::cfg::BlockAnd;
use crate::mir::build::thir::ExprId;
use crate::mir::build::{BuildResult};
use crate::mir::{BasicBlock, Rvalue};

impl Builder<'_> {
    /// as_rvalue.rs:`as_rvalue`.
    pub fn as_rvalue(&mut self, _block: BasicBlock, _scope: TempLifetime, expr: ExprId) -> BuildResult<BlockAnd<Rvalue>> {
        self.expr_not_yet(expr, "as_rvalue")
    }
}
