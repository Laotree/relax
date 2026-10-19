//! rustc_mir_build/src/thir/cx/{mod,block,expr}.rs: build the THIR of one body owner from the AST and the
//! typeck facts. Adjustments (coercions, reborrows, overloaded deref/index) become explicit nodes through
//! one `adjustments(expr)` function, so S2's unified adjustment list only replaces its body.
use super::{ExprId, Thir, ThirBody};
use crate::ast;
use crate::borrowck::body::CheckedBody;
use crate::fxhash::HashMap;
use crate::mir::Span;
use crate::mir::build::{BuildError, BuildResult, BuildRoot, UnsupportedReason};

pub struct Cx<'a> {
    pub root: &'a BuildRoot<'a>,
    pub owner: CheckedBody,
    pub thir: Thir,
    /// AST expressions already mirrored (the tree is a DAG only through shared sub-expressions).
    pub memo: HashMap<ast::ExprId, ExprId>,
}

impl<'a> Cx<'a> {
    pub fn new(root: &'a BuildRoot<'a>, owner: CheckedBody) -> Self {
        Self { root, owner, thir: Thir::default(), memo: HashMap::default() }
    }
    pub fn error(&self, span: Span, reason: UnsupportedReason) -> BuildError {
        BuildError::new(self.owner, span, reason)
    }
    /// AST patterns carry no span of their own (only identifiers and literals do); lane C derives
    /// pattern spans from those leaves, this is the fallback.
    pub fn pat_span(&self, _pat: ast::PatId) -> Span {
        Span { file: self.root.typeck.file, lo: 0, hi: 0 }
    }
    /// rustc `thir_body`.
    pub fn thir_body(self) -> BuildResult<ThirBody> {
        Err(self.error(Span::default(), UnsupportedReason::NotYetBuilt("thir_body")))
    }
    /// thir/cx/expr.rs:`mirror_expr`.
    pub fn mirror_expr(&mut self, expr: ast::ExprId) -> BuildResult<ExprId> {
        let _ = expr;
        Err(self.error(Span::default(), UnsupportedReason::NotYetBuilt("mirror_expr")))
    }
}
