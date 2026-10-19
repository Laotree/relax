//! The desugarings rustc's AST lowering does before THIR exists: `while`, `for`, `?` and Relax's
//! builtin macros (`matches!`, `assert!`, the print and panic families). Each uses the scopes the
//! region tree (`region_scope.rs`) enters for the same construct.
use super::{Breakable, Cx};
use crate::ast::{self, ExprKind as A};
use crate::consts::ScalarInt;
use crate::lang_items::LangItem;
use crate::mir::build::thir::{Arm, AdtExpr, AdtExprBase, Block, BlockSafety, Expr, ExprId, ExprKind, FieldPat, LocalVarId, MatchSource, Pat, PatKind, Stmt, StmtKind};
use crate::mir::build::BuildResult;
use crate::mir::{BorrowKind, FieldIdx, MutBorrowKind, Span, VariantIdx};
use crate::program::{DefId, DefKind};
use crate::region_scope::{Node, ScopeData, ScopeId, Synthetic};
use crate::types::{TyId, TyKind};

impl Cx<'_> {
    fn synthetic_scope(&self, e: ast::ExprId, which: Synthetic, data: ScopeData, span: Span) -> BuildResult<ScopeId> {
        match self.scope_of(Node::Synthetic(e.0, which), data) {
            Some(scope) => Ok(scope),
            None => self.unresolved(span, "scope of a desugaring"),
        }
    }

    fn lit_bool(&self, e: ast::ExprId, value: bool, span: Span) -> Expr {
        let lit = ScalarInt::try_from_uint(value as u128, 1).expect("one byte");
        self.mk_at(e, span, ExprKind::NonHirLiteral { lit, user_ty: None }, self.bool_ty())
    }

    /// `ty` with its projections normalized (the result type of a trait method).
    fn normalize(&self, ty: TyId) -> TyId {
        self.tcx().try_normalize_erasing_regions(self.prog(), self.root.cx.env, ty).unwrap_or(ty)
    }

    /// The return type of the trait method `def` at `args`.
    fn method_output(&self, def: DefId, args: &[TyId], span: Span) -> BuildResult<TyId> {
        let tcx = self.tcx();
        let Some(sig) = tcx.fn_sig(self.prog(), def) else { return self.unresolved(span, "method signature") };
        Ok(self.normalize(tcx.tys.subst(sig.ret, args)))
    }

    /// The index of an enum's variant that is the lang item `item`.
    fn lang_variant(&self, adt: DefId, item: LangItem, span: Span) -> BuildResult<VariantIdx> {
        let (tcx, prog) = (self.tcx(), self.prog());
        let Some(variant) = tcx.lang_items.get(item) else { return self.unresolved(span, "variant lang item") };
        let _ = adt;
        Ok(VariantIdx(prog.def(variant).sub))
    }

    fn variant_pat(&self, ty: TyId, variant: VariantIdx, subpatterns: Vec<FieldPat>, span: Span) -> BuildResult<Pat> {
        let (adt, args) = self.adt_args(ty, span)?;
        Ok(Pat { ty, span, extra: None, kind: PatKind::Variant { adt_def: adt, args, variant_index: variant, subpatterns } })
    }

    // ---------------------------------------------------------------- while

    /// `while cond { body }` is `loop { if cond { body } else { break } }`.
    pub(super) fn while_expr(&mut self, e: ast::ExprId, row: ast::WhileRow, expr_ty: TyId) -> BuildResult<Expr> {
        let span = self.espan(e);
        let loop_scope = self.node_scope(Node::Expr(e.0), span)?;
        let iteration = self.synthetic_scope(e, Synthetic::Iteration, ScopeData::Node, span)?;
        let iteration_blocks = self.synthetic_scope(e, Synthetic::Iteration, ScopeData::Destruction, span)?;
        let unit = self.unit_ty();
        self.breakables.push(Breakable { label: row.label, scope: loop_scope, is_block: false });
        let built = (|| -> BuildResult<ExprId> {
            let if_then_scope = match self.scope_of(Node::Block(row.body.0), ScopeData::IfThenRescope).or_else(|| self.scope_of(Node::Block(row.body.0), ScopeData::IfThen)) {
                Some(scope) => scope,
                None => return self.unresolved(span, "while-body scope"),
            };
            let cond = self.mirror_expr(row.cond)?;
            let then = self.block_expr(e, row.body, unit)?;
            let never = self.tcx().tys.never;
            let brk = self.push(self.mk(e, ExprKind::Break { label: loop_scope, value: None }, never));
            let else_opt = Some(self.push(self.mk(e, ExprKind::NeverToAny { source: brk }, unit)));
            let if_expr = self.mk(e, ExprKind::If { if_then_scope, cond, then, else_opt }, unit);
            let if_id = self.push(if_expr);
            let scoped = self.push(self.mk(e, ExprKind::Scope { region_scope: iteration, node: e.0, value: if_id }, unit));
            let block = self.thir.alloc_block(Block { targeted_by_break: false, region_scope: iteration_blocks, span, stmts: Box::new([]), expr: Some(scoped), safety_mode: BlockSafety::Safe });
            Ok(self.push(self.mk(e, ExprKind::Block { block }, unit)))
        })();
        self.breakables.pop();
        Ok(self.mk(e, ExprKind::Loop { body: built? }, expr_ty))
    }

    // ---------------------------------------------------------------- for

    /// `for pat in head { body }` (rustc_ast_lowering lower_expr_for):
    /// `DropTemps(match IntoIterator::into_iter(head) { mut iter => loop { match Iterator::next(&mut iter) { None => break, Some(pat) => body } } })`
    pub(super) fn for_expr(&mut self, e: ast::ExprId, row: ast::ForRow, expr_ty: TyId) -> BuildResult<Expr> {
        let (tb, tcx) = (self.tb(), self.tcx());
        let span = self.espan(e);
        let unit = self.unit_ty();
        let never = tcx.tys.never;
        let (Some(&(into_def, into_args, iter_ty)), Some(&(next_def, next_args))) = (tb.for_into.get(&row.iter.0), tb.for_next.get(&row.iter.0)) else {
            return self.unresolved(span, "for-loop iterator facts");
        };
        let for_match = self.synthetic_scope(e, Synthetic::ForMatch, ScopeData::Node, span)?;
        let for_arm = self.synthetic_scope(e, Synthetic::ForArm, ScopeData::Node, span)?;
        let for_arm_blocks = self.synthetic_scope(e, Synthetic::ForArm, ScopeData::Destruction, span)?;
        let iteration = self.synthetic_scope(e, Synthetic::Iteration, ScopeData::Node, span)?;
        let for_body = self.synthetic_scope(e, Synthetic::ForBody, ScopeData::Node, span)?;
        let for_body_stmt = self.synthetic_scope(e, Synthetic::ForBody, ScopeData::Destruction, span)?;

        // `IntoIterator::into_iter(<head>)`
        let head = self.mirror_expr(row.iter)?;
        let head_span = self.espan(row.iter);
        let into_ty = self.fn_def_ty(into_def, tcx.tys.list(into_args));
        let fun = self.push(Expr { kind: ExprKind::ZstLiteral { user_ty: None }, ty: into_ty, temp_scope: Some(for_match), span: head_span });
        let into_call = self.push(Expr {
            kind: ExprKind::Call { ty: into_ty, fun, args: Box::new([head]), from_hir_call: false, fn_span: head_span },
            ty: iter_ty,
            temp_scope: Some(for_match),
            span: head_span,
        });

        // `mut iter`
        let iter_var = self.synthetic_binding(for_arm);
        let iter_pat = self.binding_pat(iter_var, "iter", iter_ty, true, head_span);

        // `Iterator::next(&mut iter)`
        let opt_ty = self.method_output(next_def, tcx.tys.list(next_args), span)?;
        let next_ty = self.fn_def_ty(next_def, tcx.tys.list(next_args));
        let iter_ref = self.push(Expr { kind: ExprKind::VarRef { id: iter_var }, ty: iter_ty, temp_scope: Some(for_body_stmt), span: head_span });
        let ref_mut = self.ref_ty(true, iter_ty);
        let borrow = self.push(Expr { kind: ExprKind::Borrow { borrow_kind: BorrowKind::Mut { kind: MutBorrowKind::Default }, arg: iter_ref }, ty: ref_mut, temp_scope: Some(for_body_stmt), span: head_span });
        let next_fun = self.push(Expr { kind: ExprKind::ZstLiteral { user_ty: None }, ty: next_ty, temp_scope: Some(for_body_stmt), span: head_span });
        let next_call = self.push(Expr {
            kind: ExprKind::Call { ty: next_ty, fun: next_fun, args: Box::new([borrow]), from_hir_call: false, fn_span: head_span },
            ty: opt_ty,
            temp_scope: Some(for_body_stmt),
            span: head_span,
        });

        // `None => break`, `Some(<pat>) => <body>`
        self.breakables.push(Breakable { label: row.label, scope: iteration, is_block: false });
        let arms = (|| -> BuildResult<Vec<crate::mir::build::thir::ArmId>> {
            let none_idx = self.lang_variant(DefId(0), LangItem::OptionNone, span)?;
            let some_idx = self.lang_variant(DefId(0), LangItem::OptionSome, span)?;
            let none_pat = self.variant_pat(opt_ty, none_idx, Vec::new(), span)?;
            let brk = self.push(Expr { kind: ExprKind::Break { label: iteration, value: None }, ty: never, temp_scope: Some(for_body_stmt), span });
            let none_body = self.push(Expr { kind: ExprKind::NeverToAny { source: brk }, ty: unit, temp_scope: Some(for_body_stmt), span });
            let none_arm = self.thir.alloc_arm(Arm { pattern: Box::new(none_pat), guard: None, body: none_body, node: e.0, scope: for_body, span });

            self.pat_hint = self.pat_span(row.pat).lo;
            let user_pat = self.lower_pattern(row.pat)?;
            let some_pat = self.variant_pat(opt_ty, some_idx, vec![FieldPat { field: FieldIdx(0), pattern: user_pat }], span)?;
            let body = self.block_expr(e, row.body, unit)?;
            let some_arm = self.thir.alloc_arm(Arm { pattern: Box::new(some_pat), guard: None, body, node: e.0, scope: for_body, span });
            Ok(vec![none_arm, some_arm])
        })();
        self.breakables.pop();
        let arms = arms?;
        let match_next = self.push(Expr {
            kind: ExprKind::Match { scrutinee: next_call, arms: arms.into_boxed_slice(), match_source: MatchSource::ForLoopDesugar },
            ty: unit,
            temp_scope: Some(for_body_stmt),
            span,
        });
        let stmt = self.thir.alloc_stmt(Stmt { kind: StmtKind::Expr { scope: for_body_stmt, expr: match_next } });
        let block = self.thir.alloc_block(Block { targeted_by_break: false, region_scope: for_arm_blocks, span, stmts: Box::new([stmt]), expr: None, safety_mode: BlockSafety::Safe });
        let loop_body = self.push(Expr { kind: ExprKind::Block { block }, ty: unit, temp_scope: Some(iteration), span });
        let loop_expr = self.push(Expr { kind: ExprKind::Loop { body: loop_body }, ty: unit, temp_scope: Some(iteration), span });
        let loop_scoped = self.push(Expr { kind: ExprKind::Scope { region_scope: iteration, node: e.0, value: loop_expr }, ty: unit, temp_scope: Some(iteration), span });

        // `mut iter => loop { .. }`
        let iter_arm = self.thir.alloc_arm(Arm { pattern: Box::new(iter_pat), guard: None, body: loop_scoped, node: e.0, scope: for_arm, span });
        let outer = self.push(Expr {
            kind: ExprKind::Match { scrutinee: into_call, arms: Box::new([iter_arm]), match_source: MatchSource::ForLoopDesugar },
            ty: unit,
            temp_scope: self.temp_scope(e),
            span,
        });
        let outer_scoped = self.push(Expr { kind: ExprKind::Scope { region_scope: for_match, node: e.0, value: outer }, ty: unit, temp_scope: self.temp_scope(e), span });
        // `DropTemps(..)`
        Ok(self.mk(e, ExprKind::Use { source: outer_scoped }, expr_ty))
    }

    // ---------------------------------------------------------------- ?

    /// `expr?` (rustc_ast_lowering lower_expr_try):
    /// `match Try::branch(expr) { Continue(val) => val, Break(residual) => return FromResidual::from_residual(residual) }`
    pub(super) fn try_expr(&mut self, e: ast::ExprId, x: ast::ExprId, expr_ty: TyId) -> BuildResult<Expr> {
        let (tb, tcx, prog) = (self.tb(), self.tcx(), self.prog());
        let span = self.espan(e);
        let never = tcx.tys.never;
        let (Some(&(branch_def, branch_args, flow)), Some(&(from_def, from_args))) = (tb.try_branch.get(&e.0), tb.try_from_residual.get(&e.0)) else {
            return self.unresolved(span, "`?` facts");
        };
        let scope = self.node_scope(Node::Expr(e.0), span)?;
        let TyKind::Adt(flow_adt, flow_args, _) = *tcx.tys.kind(flow) else { return self.unresolved(span, "ControlFlow type") };
        let continue_idx = self.lang_variant(flow_adt, LangItem::ControlFlowContinue, span)?;
        let break_idx = self.lang_variant(flow_adt, LangItem::ControlFlowBreak, span)?;
        let field_ty = |variant: VariantIdx| tcx.field_ty(prog, self.root.cx.env, flow_adt, variant.0, 0, tcx.tys.list(flow_args));
        let (val_ty, residual_ty) = (field_ty(continue_idx), field_ty(break_idx));

        // `Try::branch(<expr>)`
        let arg = self.mirror_expr(x)?;
        let branch_ty = self.fn_def_ty(branch_def, tcx.tys.list(branch_args));
        let fun = self.push(self.mk(e, ExprKind::ZstLiteral { user_ty: None }, branch_ty));
        let scrutinee = self.push(self.mk(e, ExprKind::Call { ty: branch_ty, fun, args: Box::new([arg]), from_hir_call: false, fn_span: span }, flow));

        // `Continue(val) => val`
        let val_var = self.synthetic_binding(scope);
        let val_pat = self.binding_pat(val_var, "val", val_ty, false, span);
        let continue_pat = self.variant_pat(flow, continue_idx, vec![FieldPat { field: FieldIdx(0), pattern: val_pat }], span)?;
        let val = self.push(self.mk(e, ExprKind::VarRef { id: val_var }, val_ty));
        let continue_arm = self.thir.alloc_arm(Arm { pattern: Box::new(continue_pat), guard: None, body: val, node: e.0, scope, span });

        // `Break(residual) => return FromResidual::from_residual(residual)`
        let residual_var = self.synthetic_binding(scope);
        let residual_pat = self.binding_pat(residual_var, "residual", residual_ty, false, span);
        let break_pat = self.variant_pat(flow, break_idx, vec![FieldPat { field: FieldIdx(0), pattern: residual_pat }], span)?;
        let residual = self.push(self.mk(e, ExprKind::VarRef { id: residual_var }, residual_ty));
        let from_ty = self.fn_def_ty(from_def, tcx.tys.list(from_args));
        let from_ret = self.method_output(from_def, tcx.tys.list(from_args), span)?;
        let from_fun = self.push(self.mk(e, ExprKind::ZstLiteral { user_ty: None }, from_ty));
        let from_call = self.push(self.mk(e, ExprKind::Call { ty: from_ty, fun: from_fun, args: Box::new([residual]), from_hir_call: false, fn_span: span }, from_ret));
        let ret = self.push(self.mk(e, ExprKind::Return { value: Some(from_call) }, never));
        let ret_any = self.push(self.mk(e, ExprKind::NeverToAny { source: ret }, expr_ty));
        let break_arm = self.thir.alloc_arm(Arm { pattern: Box::new(break_pat), guard: None, body: ret_any, node: e.0, scope, span });

        Ok(self.mk(e, ExprKind::Match { scrutinee, arms: Box::new([continue_arm, break_arm]), match_source: MatchSource::TryDesugar }, expr_ty))
    }

    // ---------------------------------------------------------------- builtin macros

    pub(super) fn mac_expr(&mut self, e: ast::ExprId, m: ast::MacCall, expr_ty: TyId) -> BuildResult<Expr> {
        let (ast, file) = (self.ast(), self.file());
        let span = self.espan(e);
        let name = ast.segs(m.path.segs).last().map(|s| file.text(s.name)).unwrap_or("");
        if name == "cfg" {
            // MIR building does not prune on the value (borrowck sees both branches)
            return Ok(self.lit_bool(e, false, span));
        }
        if m.args == ast::NO_MAC_ARGS {
            return self.unresolved(span, "macro without parsed arguments");
        }
        let margs = *ast.mac_arg(m.args);
        let xs: Vec<ast::ExprId> = ast.list(margs.exprs).to_vec();
        match name {
            "matches" => self.matches_macro(e, &xs, margs.pat, margs.guard, expr_ty),
            "assert" | "debug_assert" => {
                let Some(&cond) = xs.first() else { return self.unresolved(span, "assert without a condition") };
                let branch = self.synthetic_scope(e, Synthetic::MacroBranch, ScopeData::Node, span)?;
                let branch_blocks = self.synthetic_scope(e, Synthetic::MacroBranch, ScopeData::Destruction, span)?;
                let stmt_scope = self.synthetic_scope(e, Synthetic::MacroStatement, ScopeData::Node, span)?;
                let cond = self.mirror_expr(cond)?;
                let not = self.push(self.mk(e, ExprKind::Unary { op: crate::mir::UnOp::Not, arg: cond }, self.bool_ty()));
                let unit = self.unit_ty();
                let then = self.fmt_block(e, &xs[1..], stmt_scope, branch_blocks, true, unit)?;
                Ok(self.mk(e, ExprKind::If { if_then_scope: branch, cond: not, then, else_opt: None }, expr_ty))
            }
            "assert_eq" | "assert_ne" | "debug_assert_eq" | "debug_assert_ne" => {
                let stmt_scope = self.synthetic_scope(e, Synthetic::MacroStatement, ScopeData::Node, span)?;
                let blocks = self.synthetic_scope(e, Synthetic::MacroStatement, ScopeData::Destruction, span)?;
                let block = self.fmt_block(e, &xs, stmt_scope, blocks, false, expr_ty)?;
                Ok(self.mk(e, ExprKind::Use { source: block }, expr_ty).with_kind_of(&self.thir, block))
            }
            "print" | "println" | "eprint" | "eprintln" | "panic" | "unreachable" | "todo" | "unimplemented" => {
                let diverges = matches!(name, "panic" | "unreachable" | "todo" | "unimplemented");
                let stmt_scope = self.synthetic_scope(e, Synthetic::MacroStatement, ScopeData::Node, span)?;
                let blocks = self.synthetic_scope(e, Synthetic::MacroStatement, ScopeData::Destruction, span)?;
                let block = self.fmt_block(e, &xs, stmt_scope, blocks, diverges, expr_ty)?;
                Ok(self.thir.exprs[block.0 as usize].clone())
            }
            _ => self.unresolved(span, "unsupported builtin macro"),
        }
    }

    /// `{ &arg; &arg; ..; <unreachable>? }`: the format arguments are borrowed (`format_args!` takes
    /// `&arg`), by statement; a string literal is not a place. A panicking macro ends in `Unreachable`.
    fn fmt_block(&mut self, e: ast::ExprId, args: &[ast::ExprId], stmt_scope: ScopeId, blocks: ScopeId, diverges: bool, ty: TyId) -> BuildResult<ExprId> {
        let (tb, ast) = (self.tb(), self.ast());
        let span = self.espan(e);
        let mut stmts = Vec::new();
        let mut borrow_stmt = |this: &mut Self, arg: ExprId, arg_ty: TyId, arg_span: Span| {
            let ref_ty = this.ref_ty(false, arg_ty);
            let borrow = this.push(Expr { kind: ExprKind::Borrow { borrow_kind: BorrowKind::Shared, arg }, ty: ref_ty, temp_scope: Some(stmt_scope), span: arg_span });
            let _ = arg_span;
            stmts.push(this.thir.alloc_stmt(Stmt { kind: StmtKind::Expr { scope: stmt_scope, expr: borrow } }));
        };
        for &x in args {
            if matches!(ast.expr(super::strip_paren(ast, x)).kind, A::Lit(_)) {
                continue;
            }
            let arg_ty = self.ety_adjusted(x)?;
            let arg = self.mirror_expr(x)?;
            borrow_stmt(self, arg, arg_ty, self.espan(x));
        }
        // inline `{name}` arguments
        let named: Vec<(crate::program::Sym, crate::typeck::Res)> = tb.fmt_named.iter().filter(|((node, _), _)| *node == e.0).map(|((_, sym), res)| (*sym, *res)).collect();
        for (_, res) in named {
            if let crate::typeck::Res::Local(index) = res {
                let var = LocalVarId(index);
                let ty = tb.locals[index as usize].ty;
                let kind = if self.is_upvar(index) { ExprKind::UpvarRef { var } } else { ExprKind::VarRef { id: var } };
                let arg = self.push(Expr { kind, ty, temp_scope: Some(stmt_scope), span });
                borrow_stmt(self, arg, ty, span);
            }
        }
        let tail = if diverges {
            let never = self.tcx().tys.never;
            Some(self.push(Expr { kind: ExprKind::Unreachable, ty: never, temp_scope: Some(stmt_scope), span }))
        } else {
            None
        };
        let block = self.thir.alloc_block(Block { targeted_by_break: false, region_scope: blocks, span, stmts: stmts.into_boxed_slice(), expr: tail, safety_mode: BlockSafety::Safe });
        Ok(self.push(self.mk(e, ExprKind::Block { block }, ty)))
    }

    /// `matches!(x, pat if guard)` is `match x { pat if guard => true, _ => false }`.
    fn matches_macro(&mut self, e: ast::ExprId, xs: &[ast::ExprId], pat: Option<ast::PatId>, guard: Option<ast::ExprId>, expr_ty: TyId) -> BuildResult<Expr> {
        let span = self.espan(e);
        let (Some(&x), Some(pat)) = (xs.first(), pat) else { return self.unresolved(span, "matches! arguments") };
        let arm_scope = self.synthetic_scope(e, Synthetic::MacroArm, ScopeData::Node, span)?;
        let scrutinee_ty = self.ety_adjusted(x)?;
        let scrutinee = self.mirror_expr(x)?;
        self.pat_hint = span.lo;
        let pattern = Box::new(self.lower_pattern(pat)?);
        let guard = match guard {
            Some(g) => Some(self.mirror_expr(g)?),
            None => None,
        };
        let yes = self.push(self.lit_bool(e, true, span));
        let first = self.thir.alloc_arm(Arm { pattern, guard, body: yes, node: e.0, scope: arm_scope, span });
        let no = self.push(self.lit_bool(e, false, span));
        let wild = Pat { ty: scrutinee_ty, span, extra: None, kind: PatKind::Wild };
        let second = self.thir.alloc_arm(Arm { pattern: Box::new(wild), guard: None, body: no, node: e.0, scope: arm_scope, span });
        Ok(self.mk(e, ExprKind::Match { scrutinee, arms: Box::new([first, second]), match_source: MatchSource::Normal }, expr_ty))
    }
}

trait WithKindOf {
    fn with_kind_of(self, thir: &crate::mir::build::thir::Thir, other: ExprId) -> Self;
}
impl WithKindOf for Expr {
    /// The block itself stands for the macro (no extra `Use`): its kind with this expression's type.
    fn with_kind_of(mut self, thir: &crate::mir::build::thir::Thir, other: ExprId) -> Self {
        self.kind = thir.exprs[other.0 as usize].kind.clone();
        self
    }
}

#[allow(dead_code)]
fn _unused(_: (AdtExpr, AdtExprBase, DefKind)) {}
