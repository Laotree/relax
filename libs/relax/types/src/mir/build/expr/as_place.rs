//! rustc_mir_build/src/builder/expr/as_place.rs. Owner: lane B.
use crate::mir::build::builder::{Builder};
use crate::mir::build::cfg::BlockAnd;
use crate::mir::build::place::PlaceBuilder;
use crate::mir::build::thir::ExprId;
use crate::mir::build::{BuildResult};
use crate::mir::{BasicBlock, Place};

impl Builder<'_> {
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
}
