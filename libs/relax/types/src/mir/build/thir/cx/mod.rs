//! rustc_mir_build/src/thir/cx/{mod,block,expr}.rs (1.97.1): build the THIR of one body owner from the
//! AST and the typeck facts. A view over (Ast, typeck::Body): no second typeck, no source text.
//!
//! Where Relax's typeck records differ from rustc's TypeckResults:
//! - Adjustments live in one list per node with two sites (`typeck/adjustments.rs`): `operand` (the
//!   autoderef of a receiver / base / callee / `*` operand, applied by the consuming node) and `value`
//!   (the coercion of the node's own value, applied by `mirror_expr`). The leading builtin `Deref(None)`
//!   of a reference coercion is not stored; it is inserted here, as that file documents.
//! - Method autoref, the `&mut` receiver reborrow, overloaded operators, indexing, `for`, `?` and the
//!   builtin macros come from side tables (`methods`, `binops`, `ov_index`, `for_into`/`for_next`,
//!   `try_branch`/`try_from_residual`) and are expanded here to the calls rustc's HIR has.
//! - The desugarings (`for`, `while`, `?`, `matches!`, `assert!`, the print and panic families) use the
//!   scopes of `region_scope.rs`' synthetic nodes; their bindings (`iter`, `val`, `residual`) are
//!   synthetic locals with ids from `Body.locals.len()` up and a drop scope in `Thir::var_scopes`.
//!
//! Not built (`BuildError`): async fn / blocks / closures, `.await`, `yield`, destructuring assignment,
//! `box`, default field values, asm. They match what the BIR checker leaves unchecked.
use super::{
    Arm, ArmId, Block, BlockId, BlockSafety, ClosureExpr, ClosureExprKind, Expr, ExprId, ExprKind, LocalVarId, Param, ParamId, Pat, PatKind, Stmt, StmtId, StmtKind,
    Thir, ThirBody,
};
use crate::ast;
use crate::borrowck::body::{BodyKind as OwnerKind, CheckedBody};
use crate::consts::GenericArg;
use crate::mir::build::{BuildError, BuildResult, BuildRoot, UnsupportedReason};
use crate::mir::{BindingMode, ByRef, Mutability, Span};
use crate::program::{DefId, DefKind, Program};
use crate::region_scope::{Node, ScopeData, ScopeId};
use crate::tcx::Tcx;
use crate::typeck;
use crate::types::{RegionArgsId, RegionId, TyId, TyKind, TypeFlags};

mod block;
mod desugar;
mod expr;
#[cfg(test)]
pub(crate) mod tests;

/// A loop or labeled block a `break` / `continue` can target.
#[derive(Clone, Copy)]
pub(super) struct Breakable {
    pub label: Option<ast::Ident>,
    pub scope: ScopeId,
    /// A labeled block: only a labeled `break` reaches it.
    pub is_block: bool,
}

pub struct Cx<'a> {
    pub root: &'a BuildRoot<'a>,
    pub owner: CheckedBody,
    pub thir: Thir,
    /// Where a pattern with no leaf of its own (`_`, `..`) is placed (derived pattern spans,
    /// `pattern/span.rs`): the callers set it to the start of the enclosing construct.
    pub pat_hint: u32,
    pub(super) breakables: Vec<Breakable>,
    /// The next synthetic local id (`Body.locals.len()` up).
    next_synthetic: u32,
    /// The expression being lowered is an argument of a call: a `&mut` reborrow adjustment of it is a
    /// two-phase borrow (rustc `AllowTwoPhase::Yes` at argument coercion sites).
    pub(super) two_phase: bool,
    /// The source of the `Cast` being lowered: its pointer coercions are "from an `as` cast".
    pub(super) cast_source: Option<ast::ExprId>,
}

impl<'a> Cx<'a> {
    pub fn new(root: &'a BuildRoot<'a>, owner: CheckedBody) -> Self {
        let next_synthetic = root.typeck.locals.len() as u32;
        Self { root, owner, thir: Thir::default(), pat_hint: 0, breakables: Vec::new(), next_synthetic, two_phase: false, cast_source: None }
    }
    pub fn error(&self, span: Span, reason: UnsupportedReason) -> BuildError {
        BuildError::new(self.owner, span, reason)
    }
    pub(super) fn unresolved<T>(&self, span: Span, what: &'static str) -> BuildResult<T> {
        Err(self.error(span, UnsupportedReason::UnresolvedFact(what)))
    }
    pub(super) fn not_built<T>(&self, span: Span, what: &'static str) -> BuildResult<T> {
        Err(self.error(span, UnsupportedReason::NotYetBuilt(what)))
    }

    // ---- context
    pub(super) fn tb(&self) -> &'a typeck::Body {
        self.root.typeck
    }
    pub(super) fn prog(&self) -> &'a Program {
        self.root.cx.prog
    }
    pub(super) fn tcx(&self) -> &'a Tcx {
        self.root.cx.tcx
    }
    pub(super) fn ast(&self) -> &'a ast::Ast {
        &self.prog().files[self.tb().file as usize].ast
    }
    pub(super) fn file(&self) -> &'a crate::parser::ParsedFile {
        &self.prog().files[self.tb().file as usize]
    }
    pub(super) fn span(&self, lo: u32, hi: u32) -> Span {
        Span { file: self.tb().file, lo, hi }
    }
    pub(super) fn espan(&self, e: ast::ExprId) -> Span {
        let ex = self.ast().expr(e);
        self.span(ex.lo, ex.hi)
    }
    pub(super) fn unit_ty(&self) -> TyId {
        self.tcx().tys.unit
    }
    pub(super) fn bool_ty(&self) -> TyId {
        self.tcx().tys.bool_
    }
    pub(super) fn ref_ty(&self, mutable: bool, ty: TyId) -> TyId {
        self.tcx().tys.intern(TyKind::Ref(mutable, ty, RegionId::ERASED))
    }

    /// The type typeck recorded for an expression (before its adjustments).
    pub(super) fn ety(&self, e: ast::ExprId) -> BuildResult<TyId> {
        let tb = self.tb();
        let i = tb.expr_ix(e);
        let span = self.espan(e);
        if i >= tb.expr_ty.len() || !tb.expr_typed.get(i) {
            return self.unresolved(span, "expression type");
        }
        let ty = tb.expr_ty[i];
        let flags = self.tcx().tys.flags(ty);
        if flags.intersects(TypeFlags::HAS_ERROR) || flags.intersects(TypeFlags::HAS_NON_REGION_INFER) {
            return Err(self.error(span, UnsupportedReason::TypeckTainted));
        }
        Ok(ty)
    }
    /// The type of an expression after its value adjustments (rustc `expr_ty_adjusted`).
    pub(super) fn ety_adjusted(&self, e: ast::ExprId) -> BuildResult<TyId> {
        let ty = self.ety(e)?;
        Ok(self.tb().adjustments(e.0).and_then(|a| a.value.last()).map_or(ty, |a| a.target))
    }

    // ---- scopes
    pub(super) fn scope_of(&self, node: Node, data: ScopeData) -> Option<ScopeId> {
        self.root.scope_tree.scope(node, data)
    }
    pub(super) fn node_scope(&self, node: Node, span: Span) -> BuildResult<ScopeId> {
        match self.scope_of(node, ScopeData::Node) {
            Some(scope) => Ok(scope),
            None => self.unresolved(span, "region scope of a node"),
        }
    }
    /// rustc `temp_scope_id`, resolved through the scope tree: the scope the temporaries of `e` die in
    /// (None: static extension).
    pub(super) fn temp_scope(&self, e: ast::ExprId) -> Option<ScopeId> {
        self.scope_of(Node::Expr(e.0), ScopeData::Node)?;
        self.root.scope_tree.temporary_scope(e)
    }

    // ---- arena
    pub(super) fn push(&mut self, expr: Expr) -> ExprId {
        self.thir.alloc_expr(expr)
    }
    /// An expression of `e`'s temporary scope and span.
    pub(super) fn mk(&self, e: ast::ExprId, kind: ExprKind, ty: TyId) -> Expr {
        Expr { kind, ty, temp_scope: self.temp_scope(e), span: self.espan(e) }
    }
    pub(super) fn mk_at(&self, e: ast::ExprId, span: Span, kind: ExprKind, ty: TyId) -> Expr {
        Expr { kind, ty, temp_scope: self.temp_scope(e), span }
    }

    // ---- generic arguments
    /// The full argument list of `def` from typeck's compact list (types and consts), with erased
    /// region slots.
    pub(super) fn full_args(&self, def: DefId, compact: &[TyId], span: Span) -> BuildResult<Vec<GenericArg>> {
        let (tcx, prog) = (self.tcx(), self.prog());
        let indices = tcx.generic_indices_of(prog, def);
        if compact.len() != indices.types_consts.len() {
            return self.unresolved(span, "generic argument count");
        }
        let regions = tcx.tys.intern_region_args(&vec![RegionId::ERASED; indices.lifetimes.len()]);
        Ok(tcx.complete_args(prog, def, compact, regions))
    }
    /// A `FnDef` type with erased region slots.
    pub(super) fn fn_def_ty(&self, def: DefId, args: &[TyId]) -> TyId {
        let (tcx, prog) = (self.tcx(), self.prog());
        let lifetimes = tcx.generic_indices_of(prog, def).lifetimes.len();
        let regions: RegionArgsId = tcx.tys.intern_region_args(&vec![RegionId::ERASED; lifetimes]);
        tcx.tys.intern(TyKind::FnDef(def, tcx.tys.mk_list(args), regions))
    }
    /// The full arguments of an ADT type.
    pub(super) fn adt_args(&self, ty: TyId, span: Span) -> BuildResult<(DefId, Vec<GenericArg>)> {
        let tcx = self.tcx();
        let TyKind::Adt(def, args, regions) = *tcx.tys.kind(ty) else { return self.unresolved(span, "ADT type") };
        Ok((def, tcx.complete_args(self.prog(), def, tcx.tys.list(args), regions)))
    }

    // ---- synthetic locals
    /// A binding of a desugaring: a fresh local id whose drop is scheduled in `scope`.
    pub(super) fn synthetic_binding(&mut self, scope: ScopeId) -> LocalVarId {
        let id = self.next_synthetic;
        self.next_synthetic += 1;
        self.thir.var_scopes.insert(id, scope);
        LocalVarId(id)
    }
    pub(super) fn binding_pat(&self, var: LocalVarId, name: &str, ty: TyId, mutable: bool, span: Span) -> Pat {
        let name = self.prog().syms.get(name).unwrap_or(0);
        Pat {
            ty,
            span,
            extra: None,
            kind: PatKind::Binding {
                name,
                mode: BindingMode(ByRef::No, if mutable { Mutability::Mut } else { Mutability::Not }),
                var,
                ty,
                subpattern: None,
                is_primary: true,
                is_shorthand: false,
            },
        }
    }

    // ---- bodies
    /// rustc `thir_body`.
    pub fn thir_body(mut self) -> BuildResult<ThirBody> {
        let tb = self.tb();
        let (prog, ast) = (self.prog(), self.ast());
        let def = prog.def(self.owner.owner);
        let span = self.span(0, 0);
        if !tb.errors.is_empty() {
            return Err(self.error(span, UnsupportedReason::TypeckTainted));
        }
        let (params, expr) = match self.owner.kind {
            OwnerKind::Function => {
                let ast::ItemKind::Fn(sig, _, _) = ast.item(def.item).kind else { return self.unresolved(span, "function item") };
                let sig = ast.fn_sig(sig);
                if sig.asyncness {
                    return self.not_built(span, "async fn");
                }
                let params = self.fn_params(sig)?;
                let Some(body) = tb.body else { return self.unresolved(span, "function body") };
                let block = self.mirror_block(body)?;
                let b = ast.block(body);
                let root = Expr { kind: ExprKind::Block { block }, ty: tb.ret, temp_scope: None, span: self.span(b.lo, b.hi) };
                (params, self.push(root))
            }
            OwnerKind::Const | OwnerKind::Static | OwnerKind::AssocConst => {
                let init = match &ast.item(def.item).kind {
                    ast::ItemKind::Const(_, init) | ast::ItemKind::Static(_, _, init) => init.get(),
                    _ => None,
                };
                let init = match prog.const_body(def.file, def.item) {
                    Ok(Some(e)) => e,
                    _ => match init {
                        Some(e) => e,
                        None => return self.unresolved(span, "initializer"),
                    },
                };
                (Vec::new(), self.mirror_expr(init)?)
            }
            OwnerKind::AnonConst(e) => (Vec::new(), self.mirror_expr(e)?),
            OwnerKind::InlineConst(e) => {
                let ast::ExprKind::ConstBlock(b) = ast.expr(e).kind else { return self.unresolved(self.espan(e), "inline const block") };
                let Some(&ty) = tb.inline_const_types.get(&e.0) else { return self.unresolved(self.espan(e), "inline const type") };
                let block = self.mirror_block(b)?;
                let blk = ast.block(b);
                let root = Expr { kind: ExprKind::Block { block }, ty, temp_scope: None, span: self.span(blk.lo, blk.hi) };
                (Vec::new(), self.push(root))
            }
            OwnerKind::Closure(ce) => {
                let ast::ExprKind::Closure(row) = ast.expr(ce).kind else { return self.not_built(self.espan(ce), "coroutine body") };
                let row = *ast.row(row);
                if row.is_async {
                    return self.not_built(self.espan(ce), "async closure");
                }
                let mut params = vec![self.closure_env_param(ce)?];
                for p in ast.list(row.params) {
                    self.pat_hint = ast.expr(ce).lo;
                    let pat = self.lower_pattern(p.pat)?;
                    let ty = pat.ty;
                    params.push(self.thir.alloc_param(Param { pat: Some(Box::new(pat)), ty, ty_span: None, self_kind: None, node: Some(p.pat.0) }));
                }
                (params, self.mirror_expr(row.body)?)
            }
        };
        Ok(ThirBody { thir: self.thir, params, expr })
    }

    /// The env parameter of a closure body: the closure by reference or by value, per its kind.
    fn closure_env_param(&mut self, ce: ast::ExprId) -> BuildResult<ParamId> {
        let ty = self.ety(ce)?;
        let kind = self.tb().min_captures.get(&ce.0).map(|c| c.kind);
        let env = match kind {
            Some(crate::upvar::ClosureKind::Fn) => self.ref_ty(false, ty),
            Some(crate::upvar::ClosureKind::FnMut) => self.ref_ty(true, ty),
            Some(crate::upvar::ClosureKind::FnOnce) => ty,
            None => return self.unresolved(self.espan(ce), "closure kind"),
        };
        Ok(self.thir.alloc_param(Param { pat: None, ty: env, ty_span: None, self_kind: None, node: None }))
    }

    /// The parameters of a function: `self` (if any) and the declared patterns.
    fn fn_params(&mut self, sig: &ast::FnSig) -> BuildResult<Vec<ParamId>> {
        let (tb, ast) = (self.tb(), self.ast());
        let mut out = Vec::new();
        let mut next_param = 0usize;
        if let Some(self_param) = sig.self_param {
            let Some(index) = tb.locals.iter().position(|l| l.pat == u32::MAX) else {
                return self.unresolved(self.span(0, 0), "self parameter local");
            };
            let local = &tb.locals[index];
            let span = self.span(0, 0);
            let mut pat = self.binding_pat(LocalVarId(index as u32), "self", local.ty, local.mutable, span);
            // `self`'s name is the local's
            if let PatKind::Binding { name, .. } = &mut pat.kind {
                *name = local.name;
            }
            let self_kind = match self_param {
                ast::SelfParam::Value(false) => Some(crate::mir::ImplicitSelfKind::Imm),
                ast::SelfParam::Value(true) => Some(crate::mir::ImplicitSelfKind::Mut),
                ast::SelfParam::Ref(_, false) => Some(crate::mir::ImplicitSelfKind::RefImm),
                ast::SelfParam::Ref(_, true) => Some(crate::mir::ImplicitSelfKind::RefMut),
                ast::SelfParam::Typed(..) => None,
            };
            let ty = pat.ty;
            out.push(self.thir.alloc_param(Param { pat: Some(Box::new(pat)), ty, ty_span: None, self_kind, node: None }));
            next_param = 1;
        }
        let _ = next_param;
        for p in ast.list(sig.params) {
            self.pat_hint = ast.expr_hint_for_pat(p.pat);
            let pat = self.lower_pattern(p.pat)?;
            let ty = pat.ty;
            out.push(self.thir.alloc_param(Param { pat: Some(Box::new(pat)), ty, ty_span: None, self_kind: None, node: Some(p.pat.0) }));
        }
        Ok(out)
    }

    pub(super) fn is_upvar(&self, local: u32) -> bool {
        match self.owner.kind {
            OwnerKind::Closure(ce) => self.tb().closure_locals.get(&ce.0).is_some_and(|caps| caps.contains(&local)),
            _ => false,
        }
    }

    /// The closure id and aggregate arguments of a closure expression's type: the parent's identity
    /// arguments (types, consts, then region slots) followed by `[kind, sig, tupled upvars]`.
    pub(super) fn closure_parts(&self, ty: TyId, span: Span) -> BuildResult<(crate::mir::ClosureId, Vec<GenericArg>, ClosureExprKind, TyId)> {
        let tcx = self.tcx();
        let TyKind::Closure(file, ce, args) = *tcx.tys.kind(ty) else { return self.unresolved(span, "closure type") };
        let TyKind::FnDef(_, parent, regions) = *tcx.tys.kind(args.parent_args) else { return self.unresolved(span, "closure parent arguments") };
        let mut out = Vec::new();
        for &arg in tcx.tys.list(parent) {
            out.push(match tcx.tys.kind(arg) {
                TyKind::Const(c) => GenericArg::Const(*c),
                _ => GenericArg::Type(arg),
            });
        }
        for &r in tcx.tys.region_args(regions).iter() {
            out.push(GenericArg::Lifetime(r));
        }
        out.push(GenericArg::Type(args.closure_kind_ty));
        out.push(GenericArg::Type(args.closure_sig_as_fn_ptr_ty));
        out.push(GenericArg::Type(args.tupled_upvars_ty));
        let kind = if tcx.is_coroutine(ty) { ClosureExprKind::Coroutine } else { ClosureExprKind::Closure };
        Ok((crate::mir::ClosureId { file, expr: ce }, out, kind, args.tupled_upvars_ty))
    }
}

#[allow(dead_code)]
fn _unused(_: (ArmId, Arm, Block, BlockId, BlockSafety, ClosureExpr, Stmt, StmtId, StmtKind, DefKind)) {}
