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
    /// Where a pattern with no leaf of its own (`_`, `..`) is placed (lane C: derived pattern spans,
    /// `pattern/span.rs`): the callers set it to the start of the enclosing construct.
    pub pat_hint: u32,
}

impl<'a> Cx<'a> {
    pub fn new(root: &'a BuildRoot<'a>, owner: CheckedBody) -> Self {
        Self { root, owner, thir: Thir::default(), memo: HashMap::default(), pat_hint: 0 }
    }
    pub fn error(&self, span: Span, reason: UnsupportedReason) -> BuildError {
        BuildError::new(self.owner, span, reason)
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
