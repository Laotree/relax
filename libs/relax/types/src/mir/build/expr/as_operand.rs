//! rustc_mir_build/src/builder/expr/as_operand.rs. Owner: lane E.
use crate::mir::build::builder::{Builder, TempLifetime};
use crate::mir::build::cfg::BlockAnd;
use crate::mir::build::thir::ExprId;
use crate::mir::build::{BuildResult};
use crate::mir::{BasicBlock, LocalInfo, Operand};

impl Builder<'_> {
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
}
