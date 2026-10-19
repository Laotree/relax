//! rustc_mir_build/src/builder/expr/as_temp.rs. Owner: lane B.
use crate::mir::build::builder::{Builder, TempLifetime};
use crate::mir::build::cfg::BlockAnd;
use crate::mir::build::thir::ExprId;
use crate::mir::build::{BuildResult};
use crate::mir::{BasicBlock, Local, Mutability};

impl Builder<'_> {
    /// as_temp.rs:`as_temp`.
    pub fn as_temp(&mut self, _block: BasicBlock, _temp_lifetime: TempLifetime, expr: ExprId, _mutability: Mutability) -> BuildResult<BlockAnd<Local>> {
        self.expr_not_yet(expr, "as_temp")
    }
}
