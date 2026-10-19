//! rustc_mir_build/src/builder/expr/into.rs. Owner: lane E.
use crate::mir::build::builder::{Builder};
use crate::mir::build::cfg::BlockAnd;
use crate::mir::build::thir::ExprId;
use crate::mir::build::{BuildResult};
use crate::mir::{BasicBlock, Place};

impl Builder<'_> {
    /// into.rs:`expr_into_dest`.
    pub fn expr_into_dest(&mut self, _destination: Place, _block: BasicBlock, expr: ExprId) -> BuildResult<BlockAnd<()>> {
        self.expr_not_yet(expr, "expr_into_dest")
    }
}
