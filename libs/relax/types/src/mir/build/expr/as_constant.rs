//! rustc_mir_build/src/builder/expr/as_constant.rs. Owner: lane E.
use crate::mir::build::builder::{Builder};
use crate::mir::build::thir::ExprId;
use crate::mir::build::{BuildResult};
use crate::mir::{ConstOperand};

impl Builder<'_> {
    /// as_constant.rs:`as_constant`.
    pub fn as_constant(&mut self, expr: ExprId) -> BuildResult<ConstOperand> {
        self.expr_not_yet(expr, "as_constant")
    }
}
