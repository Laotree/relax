//! rustc_mir_build/src/thir/pattern/{mod,const_to_pat}.rs: AST patterns to `thir::Pat`. Owned by lane C (S4);
//! the `Pat`/`PatKind` shapes are fixed in `thir/mod.rs` at I1.
use super::{Cx, Pat};
use crate::ast::PatId;
use crate::mir::build::{BuildResult, UnsupportedReason};

impl Cx<'_> {
    /// pattern/mod.rs:`lower_pattern`.
    pub fn lower_pattern(&mut self, pat: PatId) -> BuildResult<Pat> {
        let span = self.pat_span(pat);
        Err(self.error(span, UnsupportedReason::NotYetBuilt("lower_pattern")))
    }
}
