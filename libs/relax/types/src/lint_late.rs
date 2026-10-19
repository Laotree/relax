//! Late (type-aware) builtin lints of `makepad check` that are not liveness, reachability or
//! dead-code analyses: ports of rustc_lint's LateLintPass passes (`unused_must_use`,
//! `path_statements`, `trivial_casts`, ...). Check-only.

use crate::ast::*;
use crate::ast_visit::{self, Visitor};
use crate::lang_items::LangItem;
use crate::lint::{self, Level, Lint};
use crate::pattern_analysis::{self, Cx as PCx};
use crate::program::{DefId, DefKind, Program};
use crate::tcx::Tcx;
use crate::typeck::{Body, Res};
use crate::types::{AliasTyKind, TyId, TyKind};

pub const UNUSED_MUST_USE: Lint = lint::lint("unused_must_use", Level::Warn, &["unused"]);
pub const UNUSED_RESULTS: Lint = lint::lint("unused_results", Level::Allow, &[]);
pub const PATH_STATEMENTS: Lint = lint::lint("path_statements", Level::Warn, &["unused"]);
pub const DROPPING_REFERENCES: Lint = lint::lint("dropping_references", Level::Warn, &[]);
pub const FORGETTING_REFERENCES: Lint = lint::lint("forgetting_references", Level::Warn, &[]);
pub const DROPPING_COPY_TYPES: Lint = lint::lint("dropping_copy_types", Level::Warn, &[]);
pub const FORGETTING_COPY_TYPES: Lint = lint::lint("forgetting_copy_types", Level::Warn, &[]);
pub const UNDROPPED_MANUALLY_DROPS: Lint = lint::lint("undropped_manually_drops", Level::Deny, &[]);
pub const INVALID_ATOMIC_ORDERING: Lint = lint::lint("invalid_atomic_ordering", Level::Deny, &[]);
pub const LET_UNDERSCORE_DROP: Lint = lint::lint("let_underscore_drop", Level::Allow, &[]);
pub const LET_UNDERSCORE_LOCK: Lint = lint::lint("let_underscore_lock", Level::Deny, &[]);
pub const FOR_LOOPS_OVER_FALLIBLES: Lint = lint::lint("for_loops_over_fallibles", Level::Warn, &[]);
pub const MAP_UNIT_FN: Lint = lint::lint("map_unit_fn", Level::Warn, &["unused"]);
pub const UNUSED_ALLOCATION: Lint = lint::lint("unused_allocation", Level::Warn, &["unused"]);
pub const DEREF_NULLPTR: Lint = lint::lint("deref_nullptr", Level::Deny, &[]);
pub const TRIVIAL_CASTS: Lint = lint::lint("trivial_casts", Level::Allow, &[]);
pub const TRIVIAL_NUMERIC_CASTS: Lint = lint::lint("trivial_numeric_casts", Level::Allow, &[]);

/// Body-level passes over one typed body owner.
pub fn check_body(prog: &Program, tcx: &Tcx, body: &Body) {
    if !lint::enabled() { return; }
    let d = prog.def(body.def);
    let pf = &prog.files[body.file as usize];
    let ast = &pf.ast;
    let mut w = Late { prog, tcx, body, ast, stack: Vec::new(), pcx: pattern_analysis::body_cx(prog, tcx, body), arm_body: None, raw_operand: None };
    match ast.item(d.item).kind {
        ItemKind::Fn(s, _, _) => {
            let Ok(Some(block)) = prog.fn_body(body.file, d.item) else { return };
            let params: Vec<PatId> = ast.list(ast.fn_sig(s).params).iter().map(|p| p.pat).collect();
            w.block(block);
            known_panics(prog, tcx, body, Some(block), None, &params);
        }
        ItemKind::Const(..) | ItemKind::Static(..) => {
            let Ok(Some(e)) = prog.const_body(body.file, d.item) else { return };
            w.expr(e);
            known_panics(prog, tcx, body, None, Some(e), &[]);
        }
        _ => {}
    }
}

struct Late<'a> {
    prog: &'a Program,
    tcx: &'a Tcx,
    body: &'a Body,
    ast: &'a Ast,
    /// the attributes of the enclosing statements, arms, ..., outermost first
    stack: Vec<Attr>,
    pcx: PCx<'a>,
    /// the body of the match arm being visited (`is_single_call_in_arm`)
    arm_body: Option<ExprId>,
    /// the operand of the enclosing `&raw` borrow, when it is one (`&raw *NULL` is fine)
    raw_operand: Option<ExprId>,
}

// ---------------------------------------------------------------- must_use machinery

/// rustc_lint unused/must_use.rs `MustUsePath`: a path through a type to a `must_use` source.
enum MustUsePath {
    /// the def, its `#[must_use = ".."]` reason, and the position of the expression
    Def(u32, DefId),
    Boxed(Box<MustUsePath>),
    Pinned(Box<MustUsePath>),
    Opaque(Box<MustUsePath>),
    TraitObject(Box<MustUsePath>),
    TupleElement(Vec<(usize, MustUsePath)>),
    Result(Box<MustUsePath>),
    ControlFlow(Box<MustUsePath>),
    Array(Box<MustUsePath>, u64),
    Closure(u32),
    Coroutine(u32),
}

enum IsTyMustUse {
    Yes(MustUsePath),
    No,
    Trivial,
}

impl IsTyMustUse {
    fn map(self, f: impl FnOnce(MustUsePath) -> MustUsePath) -> Self {
        match self {
            Self::Yes(p) => Self::Yes(f(p)),
            o => o,
        }
    }
}

impl<'a> Late<'a> {
    fn kind(&self, t: TyId) -> TyKind { *self.tcx.tys.kind(t) }

    fn emit(&self, lint: &Lint, pos: u32, msg: &str) {
        if lint::external(self.prog, self.body.file, pos) { return; }
        lint::emit_in(self.prog, self.body.def, &self.stack, lint, self.body.file, pos, msg);
    }

    /// Lints declared `report_in_external_macro`.
    fn emit_ext(&self, lint: &Lint, pos: u32, msg: &str) {
        lint::emit_in(self.prog, self.body.def, &self.stack, lint, self.body.file, pos, msg);
    }

    fn expr_ty(&self, e: ExprId) -> Option<TyId> {
        let i = self.body.expr_ix(e);
        if i < self.body.expr_ty.len() && self.body.expr_typed.get(i) { Some(self.body.expr_ty[i]) } else { None }
    }

    fn lang(&self, item: LangItem) -> Option<DefId> { self.tcx.lang_items.get(item) }

    /// The enum a lang-item variant belongs to (`Result` of `ResultOk`).
    fn lang_parent(&self, variant: LangItem) -> Option<DefId> {
        self.lang(variant).map(|v| self.prog.def(v).parent)
    }

    /// `#[must_use]` on a definition: Some(()) when present.
    fn def_must_use(&self, d: DefId) -> bool {
        let def = self.prog.def(d);
        if !matches!(def.kind, DefKind::Struct | DefKind::Enum | DefKind::Union | DefKind::Trait | DefKind::Fn | DefKind::AssocFn | DefKind::ForeignFn | DefKind::Variant) { return false; }
        let ast = &self.prog.files[def.file as usize].ast;
        lint::has_attr(self.prog, def.file, ast.list(ast.item(def.item).attrs), "must_use")
    }

    fn is_def_must_use(&self, d: DefId, pos: u32) -> Option<MustUsePath> {
        self.def_must_use(d).then_some(MustUsePath::Def(pos, d))
    }

    fn is_ty_must_use(&self, ty: TyId, expr: ExprId, pos: u32) -> IsTyMustUse {
        let kind = self.kind(ty);
        if matches!(kind, TyKind::Tuple(l) if self.tcx.tys.list(l).is_empty()) { return IsTyMustUse::Trivial; }
        if self.pcx.is_uninhabited(ty) { return IsTyMustUse::Trivial; }
        let uninh = |t: TyId| self.pcx.is_uninhabited(t);
        match kind {
            TyKind::Adt(d, args, _) if Some(d) == self.lang(LangItem::OwnedBox) => {
                let inner = self.tcx.tys.list(args)[0];
                self.is_ty_must_use(inner, expr, pos).map(|p| MustUsePath::Boxed(Box::new(p)))
            }
            TyKind::Adt(d, args, _) if Some(d) == self.lang(LangItem::Pin) => {
                let inner = self.tcx.tys.list(args)[0];
                self.is_ty_must_use(inner, expr, pos).map(|p| MustUsePath::Pinned(Box::new(p)))
            }
            TyKind::Adt(d, args, _) if Some(d) == self.lang_parent(LangItem::ResultOk) && uninh(self.tcx.tys.list(args)[1]) => {
                let ok = self.tcx.tys.list(args)[0];
                self.is_ty_must_use(ok, expr, pos).map(|p| MustUsePath::Result(Box::new(p)))
            }
            TyKind::Adt(d, args, _) if Some(d) == self.lang_parent(LangItem::ControlFlowBreak) && uninh(self.tcx.tys.list(args)[0]) => {
                let cont = self.tcx.tys.list(args)[1];
                self.is_ty_must_use(cont, expr, pos).map(|p| MustUsePath::ControlFlow(Box::new(p)))
            }
            TyKind::Adt(d, _, _) => self.is_def_must_use(d, pos).map_or(IsTyMustUse::No, IsTyMustUse::Yes),
            TyKind::Alias(_, a) if matches!(a.kind, AliasTyKind::Opaque { .. } | AliasTyKind::Projection { .. }) => {
                let def = a.kind.def_id();
                let found = self.tcx.item_bounds(self.prog, def).iter().find_map(|p| {
                    let crate::next_solver::PredicateKind::Clause(crate::next_solver::ClauseKind::Trait(c)) = &p.kind else { return None };
                    // only the self bounds of the impl-trait
                    match c.trait_ref.args.first() {
                        Some(&crate::consts::GenericArg::Type(s)) if matches!(self.kind(s), TyKind::Alias(_, sa) if sa.kind.def_id() == def) => {}
                        _ => return None,
                    }
                    self.is_def_must_use(c.trait_ref.def_id, pos)
                });
                match found {
                    Some(inner) => IsTyMustUse::Yes(MustUsePath::Opaque(Box::new(inner))),
                    None => IsTyMustUse::No,
                }
            }
            TyKind::Dyn(principal, ..) => match self.is_def_must_use(principal, pos) {
                Some(inner) => IsTyMustUse::Yes(MustUsePath::TraitObject(Box::new(inner))),
                None => IsTyMustUse::No,
            },
            TyKind::Tuple(l) => {
                let tys = self.tcx.tys.list(l);
                let elems: Vec<ExprId> = match self.ast.expr(unparen(self.ast, expr)).kind {
                    ExprKind::Tuple(xs) => self.ast.list(xs).to_vec(),
                    _ => Vec::new(),
                };
                let mut all_trivial = true;
                let mut nested = Vec::new();
                for (i, &t) in tys.iter().enumerate() {
                    let (e, p) = match elems.get(i) { Some(&e) => (e, self.ast.expr(e).lo), None => (expr, pos) };
                    let r = self.is_ty_must_use(t, e, p);
                    all_trivial &= matches!(r, IsTyMustUse::Trivial);
                    if let IsTyMustUse::Yes(p) = r { nested.push((i, p)); }
                }
                if all_trivial { IsTyMustUse::Trivial }
                else if !nested.is_empty() { IsTyMustUse::Yes(MustUsePath::TupleElement(nested)) }
                else { IsTyMustUse::No }
            }
            TyKind::Array(elem, len) => match len.try_to_target_usize(&self.tcx.tys) {
                Some(0) | None => IsTyMustUse::No,
                Some(n) => self.is_ty_must_use(elem, expr, pos).map(|p| MustUsePath::Array(Box::new(p), n)),
            },
            TyKind::Closure(file, ce, _) => {
                if self.tcx.coroutines.contains(&(file, ce)) {
                    // an async block / async fn body: an implementer of `Future`
                    match self.lang(LangItem::Future).and_then(|f| self.is_def_must_use(f, pos)) {
                        Some(inner) => IsTyMustUse::Yes(MustUsePath::Opaque(Box::new(inner))),
                        None => IsTyMustUse::Yes(MustUsePath::Coroutine(pos)),
                    }
                } else {
                    IsTyMustUse::Yes(MustUsePath::Closure(pos))
                }
            }
            _ => IsTyMustUse::No,
        }
    }

    fn def_path_str(&self, d: DefId) -> String {
        let def = self.prog.def(d);
        let name = self.prog.name(d);
        if matches!(def.kind, DefKind::AssocFn) && def.parent != crate::program::NO_DEF {
            let p = self.prog.def(def.parent);
            match p.kind {
                DefKind::Trait => return format!("{}::{}", self.prog.name(def.parent), name),
                DefKind::Impl => {
                    let pa = &self.prog.files[p.file as usize].ast;
                    if let Some(i) = pa.as_impl(&pa.item(p.item).kind) {
                        if i.trait_.is_none() {
                            if let Ty::Path(path) = pa.ty(i.self_ty) {
                                return format!("{}::{}", crate::tcx::path_str(self.prog, p.file, path), name);
                            }
                        }
                    }
                }
                _ => {}
            }
        }
        name.to_string()
    }

    #[allow(clippy::too_many_arguments)]
    fn emit_must_use(&self, path: &MustUsePath, pre: &str, post: &str, plural_len: usize) {
        let plural = if plural_len == 1 { "" } else { "s" };
        match path {
            MustUsePath::Boxed(p) => self.emit_must_use(p, &format!("{pre}boxed "), post, plural_len),
            MustUsePath::Pinned(p) => self.emit_must_use(p, &format!("{pre}pinned "), post, plural_len),
            MustUsePath::Opaque(p) => self.emit_must_use(p, &format!("{pre}implementer{plural} of "), post, plural_len),
            MustUsePath::TraitObject(p) => self.emit_must_use(p, pre, &format!(" trait object{plural}{post}"), plural_len),
            MustUsePath::TupleElement(es) => {
                for (i, p) in es { self.emit_must_use(p, pre, &format!(" in tuple element {i}"), plural_len); }
            }
            MustUsePath::Result(p) => self.emit_must_use(p, pre, &format!(" in a `Result` with an uninhabited error{post}"), plural_len),
            MustUsePath::ControlFlow(p) => self.emit_must_use(p, pre, &format!(" in a `ControlFlow` with an uninhabited break {post}"), plural_len),
            MustUsePath::Array(p, n) => self.emit_must_use(p, &format!("{pre}array{plural} of "), post, plural_len.saturating_add(*n as usize)),
            MustUsePath::Closure(pos) => {
                let plural = if plural_len == 1 { "closure" } else { "closures" };
                self.emit_ext(&UNUSED_MUST_USE, *pos, &format!("unused {pre}{plural}{post} that must be used"));
            }
            MustUsePath::Coroutine(pos) => {
                self.emit_ext(&UNUSED_MUST_USE, *pos, &format!("unused {pre}coroutine{post} that must be used"));
            }
            MustUsePath::Def(pos, d) => {
                self.emit_ext(&UNUSED_MUST_USE, *pos, &format!("unused {pre}`{}`{post} that must be used", self.def_path_str(*d)));
            }
        }
    }

    /// check_fn_must_use: a call of a `#[must_use]` fn or method.
    fn check_fn_must_use(&self, e: ExprId, pos: u32) -> bool {
        let def = match self.ast.expr(e).kind {
            ExprKind::Call(callee, _) => {
                if let ExprKind::Path(_) = self.ast.expr(unparen(self.ast, callee)).kind {
                    match self.body.res.get(&unparen(self.ast, callee).0) {
                        Some(Res::Def(d)) if matches!(self.prog.def(*d).kind, DefKind::Fn | DefKind::AssocFn | DefKind::ForeignFn) => Some(*d),
                        _ => None,
                    }
                } else { None }
            }
            ExprKind::MethodCall(..) => self.body.methods.get(&e.0).map(|m| m.def),
            _ => None,
        };
        let Some(d) = def else { return false };
        match self.is_def_must_use(d, pos) {
            Some(p) => { self.emit_must_use(&p, "return value of ", "", 1); true }
            None => false,
        }
    }

    fn check_unused_results(&self, s_lo: u32, mut expr: ExprId) {
        // blocks with a tail expression
        while let ExprKind::Block(b, _) = self.ast.expr(expr).kind {
            let stmts = self.ast.stmts(b);
            match stmts.last() {
                Some(Stmt::Expr(e, false)) => expr = *e,
                _ => break,
            }
        }
        if let ExprKind::Return(_) = self.ast.expr(expr).kind { return; }
        let pos = self.ast.expr(expr).lo;
        // `foo().await;` on the future of an `async fn` marked `#[must_use]`
        if let ExprKind::Await(f) = self.ast.expr(expr).kind {
            let callee = match self.ast.expr(unparen(self.ast, f)).kind {
                ExprKind::Call(c, _) => match self.body.res.get(&unparen(self.ast, c).0) { Some(Res::Def(d)) => Some(*d), _ => None },
                ExprKind::MethodCall(..) => self.body.methods.get(&unparen(self.ast, f).0).map(|m| m.def),
                _ => None,
            };
            if let Some(d) = callee {
                let def = self.prog.def(d);
                let fa = &self.prog.files[def.file as usize].ast;
                let is_async = matches!(def.kind, DefKind::Fn | DefKind::AssocFn)
                    && matches!(fa.item(def.item).kind, ItemKind::Fn(sig, _, _) if fa.fn_sig(sig).asyncness);
                if is_async {
                    if let Some(p) = self.is_def_must_use(d, pos) {
                        self.emit_must_use(&p, "output of future returned by ", "", 1);
                        return;
                    }
                }
            }
        }
        let Some(ty) = self.expr_ty(expr) else { return };
        let must_use_result = self.is_ty_must_use(ty, expr, pos);
        let type_lint_emitted_or_trivial = match must_use_result {
            IsTyMustUse::Yes(path) => { self.emit_must_use(&path, "", "", 1); true }
            IsTyMustUse::Trivial => true,
            IsTyMustUse::No => false,
        };
        let fn_warned = self.check_fn_must_use(expr, pos);
        if !fn_warned && type_lint_emitted_or_trivial { return; }
        let inner = unparen(self.ast, expr);
        let op = match self.ast.expr(inner).kind {
            ExprKind::Binary(op, ..) => Some(match op {
                BinOp::Eq | BinOp::Lt | BinOp::Le | BinOp::Ne | BinOp::Ge | BinOp::Gt => "comparison",
                BinOp::Add | BinOp::Sub | BinOp::Div | BinOp::Mul | BinOp::Rem => "arithmetic operation",
                BinOp::And | BinOp::Or => "logical operation",
                BinOp::BitXor | BinOp::BitAnd | BinOp::BitOr | BinOp::Shl | BinOp::Shr => "bitwise operation",
            }),
            ExprKind::AddrOf(..) => Some("borrow"),
            ExprKind::Unary(..) => Some("unary operation"),
            _ => None,
        };
        let op_warned = match op {
            Some(op) => {
                self.emit_ext(&UNUSED_MUST_USE, pos, &format!("unused {op} that must be used"));
                true
            }
            None => false,
        };
        if !(type_lint_emitted_or_trivial || fn_warned || op_warned) {
            let t = crate::typeck::ty_to_string(false, self.prog, self.tcx, ty);
            self.emit(&UNUSED_RESULTS, s_lo, &format!("unused result of type `{t}`"));
        }
    }

    fn check_path_statement(&self, e: ExprId) {
        let inner = unparen(self.ast, e);
        if !matches!(self.ast.expr(inner).kind, ExprKind::Path(_)) { return; }
        let Some(ty) = self.expr_ty(inner).or_else(|| self.expr_ty(e)) else { return };
        let lo = self.ast.expr(e).lo;
        if self.tcx.needs_drop(self.prog, self.pcx.typing_env(), ty) {
            self.emit(&PATH_STATEMENTS, lo, "path statement drops value");
        } else {
            self.emit(&PATH_STATEMENTS, lo, "path statement with no effect");
        }
    }
}

// ---------------------------------------------------------------- expression passes

impl<'a> Late<'a> {
    /// `#[rustc_diagnostic_item = "name"]` of a definition.
    fn diag_item(&self, d: DefId) -> Option<String> {
        let def = self.prog.def(d);
        if !matches!(def.kind, DefKind::Struct | DefKind::Enum | DefKind::Union | DefKind::Trait | DefKind::Fn | DefKind::AssocFn | DefKind::TypeAlias) { return None; }
        let ast = &self.prog.files[def.file as usize].ast;
        let p = self.prog.src(def.file);
        for a in ast.list(ast.item(def.item).attrs) {
            if lint::attr_path(self.prog, def.file, a) != b"rustc_diagnostic_item" { continue; }
            let (lo, hi) = (a.toks.lo as usize, a.toks.hi as usize);
            let mut i = lo;
            while i < hi && crate::cfg::tok_str(p, i) != b"=" { i += 1; }
            if i + 1 < hi {
                let t = crate::cfg::tok_str(p, i + 1);
                return Some(String::from_utf8_lossy(t).trim_matches('"').to_string());
            }
        }
        None
    }

    /// The definition a path expression resolves to.
    fn path_def(&self, e: ExprId) -> Option<DefId> {
        let e = unparen(self.ast, e);
        if !matches!(self.ast.expr(e).kind, ExprKind::Path(_)) { return None; }
        match self.body.res.get(&e.0) { Some(Res::Def(d)) => Some(*d), _ => None }
    }

    /// `Expr::can_have_side_effects`.
    fn can_have_side_effects(&self, e: ExprId) -> bool {
        let ast = self.ast;
        match ast.expr(e).kind {
            ExprKind::Paren(x) => self.can_have_side_effects(x),
            ExprKind::Path(_) | ExprKind::Lit(_) | ExprKind::Underscore => false,
            ExprKind::Unary(_, b) | ExprKind::Field(b, _) | ExprKind::TupleField(b, _) | ExprKind::Index(b, _) | ExprKind::AddrOf(_, _, b) | ExprKind::Cast(b, _) => self.can_have_side_effects(b),
            ExprKind::Binary(_, l, r) => self.can_have_side_effects(l) || self.can_have_side_effects(r),
            ExprKind::Struct(row) => {
                let s = *ast.row(row);
                ast.list(s.fields).iter().any(|f| self.can_have_side_effects(f.expr)) || s.base.get().is_some_and(|b| self.can_have_side_effects(b))
            }
            ExprKind::Array(xs) | ExprKind::Tuple(xs) => ast.list(xs).iter().any(|&x| self.can_have_side_effects(x)),
            ExprKind::Repeat(x, _) => self.can_have_side_effects(x),
            ExprKind::Call(f, args) => {
                // a tuple struct / variant constructor call
                match self.path_def(f) {
                    Some(d) if matches!(self.prog.def(d).kind, DefKind::Struct | DefKind::Variant) => ast.list(args).iter().any(|&x| self.can_have_side_effects(x)),
                    _ => true,
                }
            }
            _ => true,
        }
    }

    fn check_expr(&mut self, e: ExprId) {
        let ex = *self.ast.expr(e);
        match ex.kind {
            ExprKind::Call(f, args) => {
                self.check_drop_forget(e, f, args);
                self.check_memory_fence(f, args);
            }
            ExprKind::MethodCall(..) => {
                self.check_map_unit_fn(e);
                self.check_unused_allocation(e);
                self.check_atomic_load_store(e);
                self.check_atomic_compare_exchange(e);
            }
            ExprKind::Cast(x, _) => self.check_trivial_cast(e, x),
            ExprKind::AddrOf(true, _, x) => self.raw_operand = Some(unparen(self.ast, x)),
            ExprKind::Unary(UnOp::Deref, x) => self.check_deref_nullptr(e, x),
            ExprKind::For(row) => self.check_for_loop_fallible(*self.ast.row(row)),
            ExprKind::Assign(l, r) => self.check_assign_desugar(l, r, ex.lo),
            _ => {}
        }
    }

    // ---- drop_forget_useless.rs
    fn check_drop_forget(&self, e: ExprId, f: ExprId, args: List<ExprId>) {
        let args = self.ast.list(args);
        if args.len() != 1 { return; }
        let Some(d) = self.path_def(f) else { return };
        let Some(name) = self.diag_item(d) else { return };
        let arg = args[0];
        let Some(arg_ty) = self.expr_ty(arg) else { return };
        let is_copy = self.tcx.is_copy_modulo_regions(self.prog, self.pcx.typing_env(), arg_ty);
        let is_ref = matches!(self.kind(arg_ty), TyKind::Ref(..));
        let single_call_in_arm = self.can_have_side_effects(arg) && self.arm_body == Some(e);
        let lo = self.ast.expr(e).lo;
        match name.as_str() {
            "mem_drop" if is_ref && !single_call_in_arm => self.emit(&DROPPING_REFERENCES, lo, "calls to `std::mem::drop` with a reference instead of an owned value does nothing"),
            "mem_forget" if is_ref => self.emit(&FORGETTING_REFERENCES, lo, "calls to `std::mem::forget` with a reference instead of an owned value does nothing"),
            "mem_drop" if is_copy && !single_call_in_arm => self.emit(&DROPPING_COPY_TYPES, lo, "calls to `std::mem::drop` with a value that implements `Copy` does nothing"),
            "mem_forget" if is_copy => self.emit(&FORGETTING_COPY_TYPES, lo, "calls to `std::mem::forget` with a value that implements `Copy` does nothing"),
            "mem_drop" => {
                if let TyKind::Adt(a, _, _) = self.kind(arg_ty) {
                    if self.diag_item(a).as_deref() == Some("ManuallyDrop") {
                        self.emit(&UNDROPPED_MANUALLY_DROPS, lo, "calls to `std::mem::drop` with `std::mem::ManuallyDrop` instead of the inner value does nothing");
                    }
                }
            }
            _ => {}
        }
    }

    // ---- types.rs InvalidAtomicOrdering
    /// An inherent method of the standard `Atomic` types: its name and arguments.
    fn inherent_atomic_method_call(&self, e: ExprId, names: &[&str]) -> Option<(String, Vec<ExprId>)> {
        let ExprKind::MethodCall(_, row) = self.ast.expr(e).kind else { return None };
        let m = *self.ast.row(row);
        let name = self.prog.files[self.body.file as usize].text(m.name).to_string();
        if !names.contains(&name.as_str()) { return None; }
        let md = self.body.methods.get(&e.0)?.def;
        let parent = self.prog.def(md).parent;
        if parent == crate::program::NO_DEF || self.prog.def(parent).kind != DefKind::Impl { return None; }
        // an inherent impl
        if self.tcx.impl_trait.contains_key(&parent) { return None; }
        let st = *self.tcx.impl_self.get(&parent)?;
        let TyKind::Adt(adt, ..) = self.kind(st) else { return None };
        if self.diag_item(adt).as_deref() != Some("Atomic") { return None; }
        Some((name, self.ast.list(m.args).to_vec()))
    }

    fn match_ordering(&self, arg: ExprId) -> Option<&'static str> {
        let d = self.path_def(arg)?;
        let name = self.prog.name(d);
        let parent = self.prog.def(d).parent;
        let is_ordering = |p: DefId| p != crate::program::NO_DEF && self.diag_item(p).as_deref() == Some("Ordering");
        if !(is_ordering(parent)) { return None; }
        ["Relaxed", "Release", "Acquire", "AcqRel", "SeqCst"].into_iter().find(|o| *o == name)
    }

    fn check_atomic_load_store(&self, e: ExprId) {
        let Some((method, args)) = self.inherent_atomic_method_call(e, &["load", "store"]) else { return };
        let (idx, invalid) = if method == "load" { (0, "Release") } else { (1, "Acquire") };
        let Some(&arg) = args.get(idx) else { return };
        let Some(ordering) = self.match_ordering(arg) else { return };
        if ordering == invalid || ordering == "AcqRel" {
            let lo = self.ast.expr(arg).lo;
            if method == "load" {
                self.emit(&INVALID_ATOMIC_ORDERING, lo, "atomic loads cannot have `Release` or `AcqRel` ordering");
            } else {
                self.emit(&INVALID_ATOMIC_ORDERING, lo, "atomic stores cannot have `Acquire` or `AcqRel` ordering");
            }
        }
    }

    fn check_memory_fence(&self, f: ExprId, args: List<ExprId>) {
        let Some(d) = self.path_def(f) else { return };
        if !matches!(self.diag_item(d).as_deref(), Some("fence" | "compiler_fence")) { return; }
        let Some(&arg) = self.ast.list(args).first() else { return };
        if self.match_ordering(arg) == Some("Relaxed") {
            self.emit(&INVALID_ATOMIC_ORDERING, self.ast.expr(arg).lo, "memory fences cannot have `Relaxed` ordering");
        }
    }

    fn check_atomic_compare_exchange(&self, e: ExprId) {
        let Some((method, args)) = self.inherent_atomic_method_call(e, &["update", "try_update", "fetch_update", "compare_exchange", "compare_exchange_weak"]) else { return };
        let idx = match method.as_str() { "update" | "try_update" | "fetch_update" => 1, _ => 3 };
        let Some(&arg) = args.get(idx) else { return };
        let Some(fail) = self.match_ordering(arg) else { return };
        if matches!(fail, "Release" | "AcqRel") {
            self.emit(&INVALID_ATOMIC_ORDERING, self.ast.expr(arg).lo, &format!("`{method}`'s failure ordering may not be `Release` or `AcqRel`, since a failed `{method}` does not result in a write"));
        }
    }

    // ---- let_underscore.rs
    /// `check_local`: the `_` patterns of a `let` (or of `_ = value;`) whose value is dropped
    /// at once. `local_lo`: the statement's position, `init`: its initializer.
    fn check_non_binding(&self, pat: Option<PatId>, init: Option<ExprId>, local_lo: u32) {
        let mut wilds: Vec<(Option<PatId>, bool)> = Vec::new();
        match pat {
            Some(p) => self.collect_wilds(p, true, &mut wilds),
            None => wilds.push((None, true)),
        }
        for (p, top) in wilds {
            let ty = match p {
                Some(p) => {
                    let i = self.body.pat_ix(p);
                    if i >= self.body.pat_ty.len() || !self.body.pat_typed.get(i) { continue; }
                    self.body.pat_ty[i]
                }
                None => match init.and_then(|x| self.expr_ty(x)) { Some(t) => t, None => continue },
            };
            if !self.tcx.needs_drop(self.prog, self.pcx.typing_env(), ty) { continue; }
            // `mutex.lock()` returns a `Result<MutexGuard, _>` as well
            let potential = match self.kind(ty) {
                TyKind::Adt(d, args, _) if Some(d) == self.lang_parent(LangItem::ResultOk) => self.tcx.tys.list(args)[0],
                _ => ty,
            };
            let is_sync_lock = match self.kind(potential) {
                TyKind::Adt(d, _, _) => matches!(self.diag_item(d).as_deref(), Some("MutexGuard" | "RwLockReadGuard" | "RwLockWriteGuard")),
                _ => false,
            };
            let can_use_init = top && init.is_some();
            if is_sync_lock {
                self.emit(&LET_UNDERSCORE_LOCK, local_lo, "non-binding let on a synchronization lock");
            } else if can_use_init {
                self.emit(&LET_UNDERSCORE_DROP, local_lo, "non-binding let on a type that has a destructor");
            }
        }
    }

    fn collect_wilds(&self, p: PatId, top: bool, out: &mut Vec<(Option<PatId>, bool)>) {
        let ast = self.ast;
        match *ast.pat(p) {
            Pat::Wild => out.push((Some(p), top)),
            Pat::Ident { sub: Some(s), .. } => self.collect_wilds(s, false, out),
            Pat::TupleStruct(_, ps) | Pat::Tuple(ps) | Pat::Slice(ps) | Pat::Or(ps) => {
                for &q in ast.list(ps) { self.collect_wilds(q, false, out); }
            }
            Pat::Struct(_, fs, _) => { for f in ast.list(fs) { self.collect_wilds(f.pat, false, out); } }
            Pat::Ref(_, x) | Pat::Paren(x) | Pat::Box(x) => self.collect_wilds(x, false, out),
            _ => {}
        }
    }

    /// A destructuring assignment `(_, a) = value;` / `_ = value;` is a `let` with the `_`
    /// patterns of the left side (LocalSource::AssignDesugar).
    fn check_assign_desugar(&self, l: ExprId, r: ExprId, lo: u32) {
        let mut wilds = Vec::new();
        self.assign_wilds(l, &mut wilds);
        for u in wilds {
            let top = unparen(self.ast, l) == u;
            let Some(ty) = (if top { self.expr_ty(r) } else { self.expr_ty(u) }) else { continue };
            if !self.tcx.needs_drop(self.prog, self.pcx.typing_env(), ty) { continue; }
            let potential = match self.kind(ty) {
                TyKind::Adt(d, args, _) if Some(d) == self.lang_parent(LangItem::ResultOk) => self.tcx.tys.list(args)[0],
                _ => ty,
            };
            let is_sync_lock = match self.kind(potential) {
                TyKind::Adt(d, _, _) => matches!(self.diag_item(d).as_deref(), Some("MutexGuard" | "RwLockReadGuard" | "RwLockWriteGuard")),
                _ => false,
            };
            if is_sync_lock {
                self.emit(&LET_UNDERSCORE_LOCK, self.ast.expr(u).lo, "non-binding let on a synchronization lock");
            } else if top {
                self.emit(&LET_UNDERSCORE_DROP, lo, "non-binding let on a type that has a destructor");
            }
        }
    }

    fn assign_wilds(&self, e: ExprId, out: &mut Vec<ExprId>) {
        let ast = self.ast;
        match ast.expr(e).kind {
            ExprKind::Underscore => out.push(e),
            ExprKind::Paren(x) => self.assign_wilds(x, out),
            ExprKind::Tuple(xs) | ExprKind::Array(xs) => { for &x in ast.list(xs) { self.assign_wilds(x, out); } }
            ExprKind::Call(f, xs) if self.path_def(f).is_some_and(|d| matches!(self.prog.def(d).kind, DefKind::Struct | DefKind::Variant)) => {
                for &x in ast.list(xs) { self.assign_wilds(x, out); }
            }
            ExprKind::Struct(row) => { for f in ast.list(ast.row(row).fields) { self.assign_wilds(f.expr, out); } }
            _ => {}
        }
    }

    // ---- unused.rs UnusedAllocation
    fn check_unused_allocation(&self, e: ExprId) {
        let ExprKind::MethodCall(recv, _) = self.ast.expr(e).kind else { return };
        let recv = unparen(self.ast, recv);
        let ExprKind::Call(f, args) = self.ast.expr(recv).kind else { return };
        if self.ast.list(args).len() != 1 { return; }
        let Some(d) = self.path_def(f) else { return };
        if self.diag_item(d).as_deref() != Some("box_new") { return; }
        let Some(m) = self.body.methods.get(&e.0) else { return };
        // the receiver's adjustments: derefs, then a borrow; a borrow of the box itself is needed
        if m.autoref == 0 || m.derefs == 0 { return; }
        let msg = if m.autoref == 1 { "unnecessary allocation, use `&` instead" } else { "unnecessary allocation, use `&mut` instead" };
        self.emit(&UNUSED_ALLOCATION, self.ast.expr(recv).lo, msg);
    }

    // ---- for_loops_over_fallibles.rs
    fn check_for_loop_fallible(&self, f: ForRow) {
        let Some(ty) = self.expr_ty(f.iter) else { return };
        let (adt, by_ref) = match self.kind(ty) {
            TyKind::Adt(d, ..) => (d, false),
            TyKind::Ref(_, t, _) => match self.kind(t) { TyKind::Adt(d, ..) => (d, true), _ => return },
            _ => return,
        };
        let (article, name) = if Some(adt) == self.lang_parent(LangItem::OptionSome) {
            (if by_ref { "a" } else { "an" }, "Option")
        } else if Some(adt) == self.lang_parent(LangItem::ResultOk) {
            ("a", "Result")
        } else { return };
        let pos = self.ast.expr(f.iter).lo;
        self.emit(&FOR_LOOPS_OVER_FALLIBLES, pos, &format!("for loop over {article} `{name}`. This is more readably written as an `if let` statement"));
    }

    // ---- map_unit_fn.rs
    fn check_map_unit_fn(&self, e: ExprId) {
        let ExprKind::MethodCall(recv, row) = self.ast.expr(e).kind else { return };
        let m = *self.ast.row(row);
        let args = self.ast.list(m.args);
        if args.len() != 1 { return; }
        let pf = &self.prog.files[self.body.file as usize];
        if pf.text(m.name) != "map" { return; }
        let pos = m.name.lo;
        if lint::external(self.prog, self.body.file, pos) { return; }
        // the receiver's method is an inherent slice method (`.iter()`)
        let Some(rm) = self.body.methods.get(&unparen(self.ast, recv).0) else { return };
        let ip = self.prog.def(rm.def).parent;
        if ip == crate::program::NO_DEF || self.prog.def(ip).kind != DefKind::Impl { return; }
        if !self.tcx.impl_self.get(&ip).is_some_and(|&st| matches!(self.kind(st), TyKind::Slice(_))) { return; }
        let Some(mm) = self.body.methods.get(&e.0) else { return };
        if self.diag_item(mm.def).as_deref() != Some("IteratorMap") { return; }
        let Some(at) = self.expr_ty(args[0]) else { return };
        let ret = match self.kind(at) {
            TyKind::Closure(_, _, ca) => match self.kind(ca.closure_sig_as_fn_ptr_ty) { TyKind::FnPtr(_, r, _, _) => r, _ => return },
            TyKind::FnDef(d, ..) => match self.tcx.fn_item_sig(self.prog, d) { Some(sig) => sig.ret, None => return },
            _ => return,
        };
        let unit = matches!(self.kind(ret), TyKind::Tuple(l) if self.tcx.tys.list(l).is_empty());
        if !(unit || matches!(self.kind(ret), TyKind::Never)) { return; }
        self.emit(&MAP_UNIT_FN, pos, "`Iterator::map` call that discard the iterator's values");
    }

    // ---- builtin.rs DerefNullPtr
    fn is_null_ptr(&self, e: ExprId) -> bool {
        let e = unparen(self.ast, e);
        let Some(t) = self.expr_ty(e) else { return false };
        let TyKind::Ptr(_, pointee) = self.kind(t) else { return false };
        let f = self.tcx.tys.flags(pointee);
        if !f.intersects(crate::types::TypeFlags::HAS_PARAM | crate::types::TypeFlags::HAS_INFER | crate::types::TypeFlags::HAS_ALIAS) {
            let lcx = crate::layout::LayoutCx::new(self.prog);
            let lay = crate::layout::Layouts::new();
            if !lay.is_unsized(&lcx, self.tcx, pointee) && lay.of(&lcx, self.tcx, pointee).size == 0 { return false; }
        }
        match self.ast.expr(e).kind {
            ExprKind::Cast(x, ty) => {
                if matches!(self.ast.ty(ty), Ty::Ptr(..)) {
                    let x = unparen(self.ast, x);
                    let zero = matches!(self.ast.expr(x).kind, ExprKind::Lit(LitKind::Int))
                        && crate::const_fold::parse_int_lit(std::str::from_utf8(self.prog.files[self.body.file as usize].bytes(self.ast.expr(x).lo, self.ast.expr(x).hi)).unwrap_or("")) == Some(0);
                    return zero || self.is_null_ptr(x);
                }
                false
            }
            ExprKind::Call(f, _) => match self.path_def(f) {
                Some(d) => matches!(self.diag_item(d).as_deref(), Some("ptr_null" | "ptr_null_mut")),
                None => false,
            },
            _ => false,
        }
    }

    fn check_deref_nullptr(&mut self, e: ExprId, x: ExprId) {
        if self.expr_ty(x).is_some_and(|t| matches!(self.kind(t), TyKind::Ptr(..))) && self.is_null_ptr(x) {
            // `&raw *NULL` is ok
            if self.raw_operand != Some(e) {
                self.emit(&DEREF_NULLPTR, self.ast.expr(e).lo, "dereferencing a null pointer");
            }
        }
    }

    // ---- rustc_hir_typeck cast.rs trivial_cast_lint
    fn check_trivial_cast(&self, e: ExprId, x: ExprId) {
        if self.body.coercion_casts.get(&x.0).is_none() { return; }
        let (Some(et), Some(ct)) = (self.expr_ty(x), self.expr_ty(e)) else { return };
        let numeric = |t: TyId| matches!(self.kind(t), TyKind::Int(_) | TyKind::Float(_) | TyKind::IntVar(_) | TyKind::FloatVar(_));
        let (is_num, lint) = if numeric(ct) && numeric(et) { (true, &TRIVIAL_NUMERIC_CASTS) } else { (false, &TRIVIAL_CASTS) };
        let (es, cs) = (crate::typeck::ty_to_string(false, self.prog, self.tcx, et), crate::typeck::ty_to_string(false, self.prog, self.tcx, ct));
        self.emit(lint, self.ast.expr(e).lo, &format!("trivial {}cast: `{}` as `{}`", if is_num { "numeric " } else { "" }, es, cs));
    }
}

fn unparen(ast: &Ast, mut e: ExprId) -> ExprId {
    while let ExprKind::Paren(x) = ast.expr(e).kind { e = x; }
    e
}

impl<'a> Visitor<'a> for Late<'a> {
    fn ast(&self) -> &'a Ast { self.ast }
    fn enter_attrs(&mut self, attrs: List<Attr>) { self.stack.extend_from_slice(self.ast.list(attrs)); }
    fn leave_attrs(&mut self, attrs: List<Attr>) {
        let n = self.ast.list(attrs).len();
        self.stack.truncate(self.stack.len() - n);
    }

    fn expr(&mut self, e: ExprId) {
        self.check_expr(e);
        ast_visit::walk_expr(self, e);
    }

    fn arm(&mut self, a: &Arm) {
        let saved = self.arm_body.replace(a.body);
        ast_visit::walk_arm(self, a);
        self.arm_body = saved;
    }

    fn stmt(&mut self, s: &Stmt, _b: BlockId) {
        match *s {
            Stmt::Expr(e, true) => {
                self.check_path_statement(e);
                self.check_unused_results(self.ast.expr(e).lo, e);
            }
            Stmt::Let(r) => {
                let l = *self.ast.row(r);
                self.enter_attrs(l.attrs);
                if let Some(x) = l.init { self.check_non_binding(Some(l.pat), Some(x), self.ast.expr(x).lo); }
                self.leave_attrs(l.attrs);
            }
            Stmt::Attrs(r) => {
                let a = *self.ast.row(r);
                if a.semi {
                    self.enter_attrs(a.attrs);
                    self.check_path_statement(a.expr);
                    self.check_unused_results(self.ast.expr(a.expr).lo, a.expr);
                    self.leave_attrs(a.attrs);
                }
            }
            _ => {}
        }
        ast_visit::walk_stmt(self, s);
    }
}

// ---------------------------------------------------------------- known_panics_lint
//
// rustc_mir_transform known_panics_lint.rs: constant propagation over the body's MIR with
// lint checks at the arithmetic operations, divisions and index operations. The port follows the
// propagation over the typed syntax tree in MIR evaluation order: operands are known when they
// are literals, constants, the operations on known operands that do not fail, and locals that
// are assigned exactly once and never borrowed (rustc `FullConstProp`); a conditional whose
// condition is known visits only the taken branch, and code after a diverging expression is not
// visited. Locals with several assignments (`OnlyInsideOwnBlock`) are not propagated.

pub const ARITHMETIC_OVERFLOW: Lint = lint::lint("arithmetic_overflow", Level::Deny, &[]);
pub const UNCONDITIONAL_PANIC: Lint = lint::lint("unconditional_panic", Level::Deny, &[]);

#[derive(Clone, Copy, PartialEq, Debug)]
enum V {
    Unknown,
    /// the bits of an integer (sign-extended to 128 bits for a signed value)
    Int(u128),
    Bool(bool),
    Float(f64),
    /// an array or tuple whose element values are in `Kp::aggs`
    Agg(u32),
}

#[derive(Clone, Copy, Default)]
struct LocalInfo {
    assigns: u32,
    borrowed: bool,
}

/// rustc `CanConstProp`: how often each local is assigned and whether its address is taken.
struct Scan<'a> {
    body: &'a Body,
    ast: &'a Ast,
    info: Vec<LocalInfo>,
    in_closure: u32,
}

impl<'a> Scan<'a> {
    fn root_local(&self, e: ExprId) -> Option<u32> {
        let mut e = e;
        loop {
            match self.ast.expr(e).kind {
                ExprKind::Paren(x) | ExprKind::Field(x, _) | ExprKind::TupleField(x, _) | ExprKind::Index(x, _) => e = x,
                ExprKind::Path(_) => return match self.body.res.get(&e.0) { Some(Res::Local(l)) => Some(*l), _ => None },
                _ => return None,
            }
        }
    }
    fn borrow(&mut self, e: ExprId) {
        if let Some(l) = self.root_local(e) { if let Some(i) = self.info.get_mut(l as usize) { i.borrowed = true; } }
    }
    fn assign(&mut self, e: ExprId) {
        if let Some(l) = self.root_local(e) { if let Some(i) = self.info.get_mut(l as usize) { i.assigns += 1; } }
    }
    fn pat_by_ref(&self, p: PatId) -> bool {
        struct R<'b> { ast: &'b Ast, body: &'b Body, found: bool }
        impl<'b> Visitor<'b> for R<'b> {
            fn ast(&self) -> &'b Ast { self.ast }
            fn pat(&mut self, p: PatId) {
                if let Pat::Ident { by_ref, .. } = *self.ast.pat(p) {
                    if by_ref || self.body.pat_bind_ref.get(&p.0).is_some() { self.found = true; }
                }
                ast_visit::walk_pat(self, p);
            }
        }
        let mut r = R { ast: self.ast, body: self.body, found: false };
        r.pat(p);
        r.found
    }
}

impl<'a> Visitor<'a> for Scan<'a> {
    fn ast(&self) -> &'a Ast { self.ast }
    fn pat(&mut self, p: PatId) {
        if let Pat::Ident { .. } = *self.ast.pat(p) {
            if let Some(&l) = self.body.pat_local.get(&p.0) {
                if let Some(i) = self.info.get_mut(l as usize) { i.assigns += 1; }
            }
        }
        ast_visit::walk_pat(self, p);
    }
    fn stmt(&mut self, s: &Stmt, b: BlockId) {
        if let Stmt::Let(r) = *s {
            let l = *self.ast.row(r);
            if let Some(x) = l.init { if self.pat_by_ref(l.pat) { self.borrow(x); } }
        }
        let _ = b;
        ast_visit::walk_stmt(self, s);
    }
    fn expr(&mut self, e: ExprId) {
        match self.ast.expr(e).kind {
            ExprKind::AddrOf(_, _, x) => self.borrow(x),
            ExprKind::Assign(l, _) | ExprKind::AssignOp(_, l, _) => self.assign(l),
            ExprKind::MethodCall(recv, _) => {
                if self.body.methods.get(&e.0).is_some_and(|m| m.autoref != 0) { self.borrow(recv); }
            }
            ExprKind::Mac(m) => {
                let m = *self.ast.row(m);
                if m.args != NO_MAC_ARGS {
                    let args = *self.ast.mac_arg(m.args);
                    for &x in self.ast.list(args.exprs) { self.borrow(x); }
                }
            }
            ExprKind::Match(x, arms) => {
                if self.ast.list(arms).iter().any(|a| self.pat_by_ref(a.pat)) { self.borrow(x); }
            }
            ExprKind::Let(p, x) => { if self.pat_by_ref(p) { self.borrow(x); } }
            ExprKind::Path(_) => {
                if self.in_closure > 0 { self.borrow(e); }
            }
            ExprKind::Closure(_) => {
                self.in_closure += 1;
                ast_visit::walk_expr(self, e);
                self.in_closure -= 1;
                return;
            }
            _ => {}
        }
        ast_visit::walk_expr(self, e);
    }
}

struct Kp<'a> {
    prog: &'a Program,
    tcx: &'a Tcx,
    body: &'a Body,
    ast: &'a Ast,
    stack: Vec<Attr>,
    info: Vec<LocalInfo>,
    env: std::collections::HashMap<u32, V>,
    aggs: Vec<Vec<V>>,
    /// the code being visited is unreachable (after a diverging expression)
    dead: bool,
}

fn mask(bytes: u32) -> u128 { if bytes >= 16 { u128::MAX } else { (1u128 << (bytes * 8)) - 1 } }

/// The sign-extended value of `bits` of an integer type of `bytes` bytes.
fn signed_of(bits: u128, bytes: u32) -> i128 {
    let shift = 128 - bytes * 8;
    if shift == 0 { bits as i128 } else { ((bits << shift) as i128) >> shift }
}

impl<'a> Kp<'a> {
    fn emit(&self, lint: &Lint, pos: u32, msg: &str) {
        if lint::external(self.prog, self.body.file, pos) { return; }
        lint::emit_in(self.prog, self.body.def, &self.stack, lint, self.body.file, pos, msg);
    }
    fn overflow(&self, pos: u32) { self.emit(&ARITHMETIC_OVERFLOW, pos, "this arithmetic operation will overflow"); }
    fn panics(&self, pos: u32) { self.emit(&UNCONDITIONAL_PANIC, pos, "this operation will panic at runtime"); }

    fn ty_of(&self, e: ExprId) -> Option<TyKind> {
        let i = self.body.expr_ix(e);
        if i < self.body.expr_ty.len() && self.body.expr_typed.get(i) { Some(*self.tcx.tys.kind(self.body.expr_ty[i])) } else { None }
    }
    /// (bytes, signed) of an integer-typed expression.
    fn int_of(&self, e: ExprId) -> Option<(u32, bool)> {
        match self.ty_of(e)? { TyKind::Int(p) => Some(crate::types::Types::int_info(p)), _ => None }
    }
    fn is_never(&self, e: ExprId) -> bool { matches!(self.ty_of(e), Some(TyKind::Never)) }

    fn enter(&mut self, attrs: List<Attr>) { self.stack.extend_from_slice(self.ast.list(attrs)); }
    fn leave(&mut self, attrs: List<Attr>) {
        let n = self.ast.list(attrs).len();
        self.stack.truncate(self.stack.len() - n);
    }

    fn block(&mut self, b: BlockId) -> V {
        let blk = *self.ast.block(b);
        self.enter(blk.attrs);
        let mut last = V::Unknown;
        let stmts = self.ast.stmts(b);
        for s in stmts {
            if self.dead { break; }
            last = V::Unknown;
            match *s {
                Stmt::Let(r) => {
                    let l = *self.ast.row(r);
                    self.enter(l.attrs);
                    if let Some(x) = l.init {
                        let v = self.eval(x);
                        if let Some(eb) = l.else_ {
                            let d = self.dead;
                            self.block(eb);
                            self.dead = d;
                        }
                        if let Pat::Ident { by_ref: false, sub: None, .. } = *self.ast.pat(l.pat) {
                            if let Some(&loc) = self.body.pat_local.get(&l.pat.0) {
                                if let Some(i) = self.info.get(loc as usize) {
                                    if i.assigns == 1 && !i.borrowed && v != V::Unknown { self.env.insert(loc, v); }
                                }
                            }
                        }
                    }
                    self.leave(l.attrs);
                }
                Stmt::Expr(e, semi) => { let v = self.eval(e); if !semi { last = v; } }
                Stmt::Attrs(r) => {
                    let a = *self.ast.row(r);
                    self.enter(a.attrs);
                    self.eval(a.expr);
                    self.leave(a.attrs);
                }
                Stmt::Item(_) | Stmt::Empty => {}
            }
        }
        self.leave(blk.attrs);
        last
    }

    /// Visits `f` as an alternative path: the dead state starts clean and its end is returned.
    fn branch(&mut self, f: impl FnOnce(&mut Self)) -> bool {
        let saved = self.dead;
        self.dead = false;
        f(self);
        let d = self.dead;
        self.dead = saved;
        d
    }

    fn eval(&mut self, e: ExprId) -> V {
        if self.dead { return V::Unknown; }
        let ex = *self.ast.expr(e);
        let v = self.eval_kind(e, ex);
        if self.is_never(e) { self.dead = true; }
        v
    }

    fn eval_kind(&mut self, e: ExprId, ex: Expr) -> V {
        let ast = self.ast;
        match ex.kind {
            ExprKind::Lit(LitKind::Bool(b)) => V::Bool(b),
            ExprKind::Lit(LitKind::Int) => {
                let Some(TyKind::Int(p)) = self.ty_of(e) else { return V::Unknown };
                let (bytes, signed) = crate::types::Types::int_info(p);
                let text = std::str::from_utf8(self.prog.files[self.body.file as usize].bytes(ex.lo, ex.hi)).unwrap_or("");
                match crate::const_fold::parse_int_lit(text) {
                    Some(v) => { let v = v & mask(bytes); V::Int(if signed { signed_of(v, bytes) as u128 } else { v }) }
                    None => V::Unknown,
                }
            }
            ExprKind::Lit(LitKind::Float) => {
                let text = std::str::from_utf8(self.prog.files[self.body.file as usize].bytes(ex.lo, ex.hi)).unwrap_or("");
                let digits: String = text.chars().filter(|c| *c != '_').collect();
                let digits = digits.trim_end_matches("f32").trim_end_matches("f64");
                digits.parse::<f64>().map_or(V::Unknown, V::Float)
            }
            ExprKind::Lit(_) | ExprKind::Underscore | ExprKind::Continue(_) => V::Unknown,
            ExprKind::Paren(x) => self.eval(x),
            ExprKind::Path(_) => self.eval_path(e),
            ExprKind::Unary(UnOp::Neg, x) if matches!(self.ast.expr(unparen(self.ast, x)).kind, ExprKind::Lit(LitKind::Int)) && self.int_of(x).is_some() => {
                // a negated literal is one constant (THIR: the literal is negated, `-128i8` is fine)
                let (bytes, signed) = self.int_of(x).unwrap();
                if !signed { return V::Unknown; }
                match self.eval_lit_wide(unparen(self.ast, x)) {
                    Some(v) => V::Int(signed_of((v as i128).wrapping_neg() as u128 & mask(bytes), bytes) as u128),
                    None => V::Unknown,
                }
            }
            ExprKind::Unary(op, x) => {
                let v = self.eval(x);
                if self.body.binops.get(&e.0).is_some() { return V::Unknown; }
                match (op, v) {
                    (UnOp::Neg, V::Int(b)) => {
                        let Some((bytes, true)) = self.int_of(x) else { return V::Unknown };
                        let s = signed_of(b, bytes);
                        let min = if bytes == 16 { i128::MIN } else { -(1i128 << (bytes * 8 - 1)) };
                        if s == min { self.overflow(ex.lo); V::Unknown } else { V::Int((-s) as u128) }
                    }
                    (UnOp::Neg, V::Float(f)) => V::Float(-f),
                    (UnOp::Not, V::Bool(b)) => V::Bool(!b),
                    (UnOp::Not, V::Int(b)) => match self.int_of(x) {
                        Some((bytes, signed)) => { let r = !b & mask(bytes); V::Int(if signed { signed_of(r, bytes) as u128 } else { r }) }
                        None => V::Unknown,
                    },
                    _ => V::Unknown,
                }
            }
            ExprKind::Binary(op, a, b) => self.eval_binary(e, ex.lo, op, a, b),
            ExprKind::Assign(l, r) => {
                self.eval(r);
                self.eval(l);
                V::Unknown
            }
            ExprKind::AssignOp(op, l, r) => {
                let rv = self.eval(r);
                let lv = self.eval(l);
                if self.body.binops.get(&e.0).is_none() {
                    self.int_binop(ex.lo, op, lv, rv, self.int_of(l), self.int_of(r));
                }
                V::Unknown
            }
            ExprKind::Cast(x, _) => {
                let v = self.eval(x);
                self.eval_cast(e, x, v)
            }
            ExprKind::Index(base, idx) => {
                let bv = self.eval(base);
                let iv = self.eval(idx);
                if self.body.ov_index.get(&e.0).is_some() { return V::Unknown; }
                let mut bt = self.body.expr_ty.get(self.body.expr_ix(base)).copied();
                while let Some(t) = bt {
                    if let TyKind::Ref(_, inner, _) = *self.tcx.tys.kind(t) { bt = Some(inner); } else { break; }
                }
                if let (Some(t), V::Int(i), Some((8, false))) = (bt, iv, self.int_of(idx)) {
                    if let TyKind::Array(_, len) = *self.tcx.tys.kind(t) {
                        if let Some(n) = len.try_to_target_usize(&self.tcx.tys) {
                            if i >= n as u128 { self.panics(ex.lo); return V::Unknown; }
                        }
                    }
                }
                match (bv, iv) {
                    (V::Agg(a), V::Int(i)) => self.aggs[a as usize].get(i as usize).copied().unwrap_or(V::Unknown),
                    _ => V::Unknown,
                }
            }
            ExprKind::If(c, then, els) => {
                let cv = self.eval(c);
                if self.dead { return V::Unknown; }
                let take_then = !matches!(cv, V::Bool(false));
                let take_else = !matches!(cv, V::Bool(true));
                let mut d1 = false;
                let mut d2 = false;
                if take_then { d1 = self.branch(|s| { s.block(then); }); } else { d1 = true; }
                match els.get() {
                    Some(x) => { if take_else { d2 = self.branch(|s| { s.eval(x); }); } else { d2 = true; } }
                    None => { d2 = !take_else; }
                }
                self.dead = d1 && d2;
                V::Unknown
            }
            ExprKind::Let(_, x) => { self.eval(x); V::Unknown }
            ExprKind::Match(x, arms) => {
                let sv = self.eval(x);
                if self.dead { return V::Unknown; }
                let arms: Vec<Arm> = ast.list(arms).to_vec();
                let mut all_dead = true;
                if matches!(sv, V::Int(_) | V::Bool(_)) {
                    // a known scrutinee: only the arm it selects is visited; when the selection cannot
                    // be decided no arm is visited (a missed lint rather than a false one)
                    for a in &arms {
                        match self.pat_matches(a.pat, sv) {
                            Some(false) => continue,
                            Some(true) => {
                                if let Some(g) = a.guard {
                                    match self.eval(g) {
                                        V::Bool(false) => continue,
                                        V::Bool(true) => {}
                                        _ => { all_dead = false; break; }
                                    }
                                }
                                self.enter(a.attrs);
                                all_dead = self.branch(|s| { s.eval(a.body); });
                                self.leave(a.attrs);
                                break;
                            }
                            None => { all_dead = false; break; }
                        }
                    }
                } else {
                    for a in &arms {
                        self.enter(a.attrs);
                        let d = self.branch(|s| {
                            if let Some(g) = a.guard { s.eval(g); }
                            s.eval(a.body);
                        });
                        self.leave(a.attrs);
                        all_dead &= d;
                    }
                    if arms.is_empty() { all_dead = true; }
                }
                self.dead = all_dead;
                V::Unknown
            }
            ExprKind::While(row) => {
                let w = *ast.row(row);
                let cv = self.eval(w.cond);
                if !matches!(cv, V::Bool(false)) && !self.dead { self.branch(|s| { s.block(w.body); }); }
                self.dead = false;
                V::Unknown
            }
            ExprKind::Loop(b, _) => { self.branch(|s| { s.block(b); }); self.dead = false; V::Unknown }
            ExprKind::For(row) => {
                let f = *ast.row(row);
                self.eval(f.iter);
                if !self.dead { self.branch(|s| { s.block(f.body); }); }
                self.dead = false;
                V::Unknown
            }
            ExprKind::Block(b, _) | ExprKind::Unsafe(b) => self.block(b),
            ExprKind::Async(..) | ExprKind::ConstBlock(_) => V::Unknown,
            ExprKind::Closure(row) => {
                let c = *ast.row(row);
                let env = std::mem::take(&mut self.env);
                let d = self.dead;
                self.dead = false;
                self.eval(c.body);
                self.dead = d;
                self.env = env;
                V::Unknown
            }
            ExprKind::Call(f, args) => {
                self.eval(f);
                for &a in ast.list(args) { self.eval(a); }
                V::Unknown
            }
            ExprKind::MethodCall(recv, row) => {
                self.eval(recv);
                for &a in ast.list(ast.row(row).args) { self.eval(a); }
                V::Unknown
            }
            ExprKind::Tuple(xs) | ExprKind::Array(xs) => {
                let vals: Vec<V> = ast.list(xs).iter().map(|&x| self.eval(x)).collect();
                self.aggs.push(vals);
                V::Agg(self.aggs.len() as u32 - 1)
            }
            ExprKind::Struct(row) => {
                let s = *ast.row(row);
                for f in ast.list(s.fields) { self.eval(f.expr); }
                if let Some(b) = s.base.get() { self.eval(b); }
                V::Unknown
            }
            ExprKind::Repeat(x, _) => { self.eval(x); V::Unknown }
            ExprKind::Range(a, b, _) => {
                if let Some(x) = a.get() { self.eval(x); }
                if let Some(x) = b.get() { self.eval(x); }
                V::Unknown
            }
            ExprKind::TupleField(x, i) => {
                match self.eval(x) {
                    V::Agg(a) => self.aggs[a as usize].get(i as usize).copied().unwrap_or(V::Unknown),
                    _ => V::Unknown,
                }
            }
            ExprKind::Field(x, _) | ExprKind::AddrOf(_, _, x) | ExprKind::Try(x)
            | ExprKind::Await(x) | ExprKind::Box(x) => { self.eval(x); V::Unknown }
            ExprKind::Break(_, x) | ExprKind::Return(x) | ExprKind::Yield(x) => {
                if let Some(x) = x.get() { self.eval(x); }
                V::Unknown
            }
            ExprKind::Mac(m) => {
                let m = *ast.row(m);
                if m.args != NO_MAC_ARGS {
                    let args = *ast.mac_arg(m.args);
                    for &x in ast.list(args.exprs) { self.eval(x); }
                }
                V::Unknown
            }
        }
    }

    /// The unsigned value of an integer literal (before the type's range is applied).
    fn eval_lit_wide(&self, e: ExprId) -> Option<u128> {
        let ex = self.ast.expr(e);
        let text = std::str::from_utf8(self.prog.files[self.body.file as usize].bytes(ex.lo, ex.hi)).unwrap_or("");
        crate::const_fold::parse_int_lit(text)
    }

    fn eval_path(&mut self, e: ExprId) -> V {
        match self.body.res.get(&e.0) {
            Some(Res::Local(l)) => self.env.get(l).copied().unwrap_or(V::Unknown),
            Some(Res::Def(d)) => {
                let d = *d;
                match self.prog.def(d).kind {
                    DefKind::Const | DefKind::AssocConst => self.eval_const(e, d),
                    DefKind::Variant => self.variant_discr(d),
                    _ => V::Unknown,
                }
            }
            _ => V::Unknown,
        }
    }

    /// A unit variant's discriminant (the operand of an `as` cast).
    fn variant_discr(&self, d: DefId) -> V {
        let parent = self.prog.def(d).parent;
        let Some(a) = self.tcx.adts.get(&parent) else { return V::Unknown };
        let Some(idx) = a.variants.iter().position(|v| v.def == d) else { return V::Unknown };
        if a.variants[idx].shape != 0 { return V::Unknown; }
        match a.discriminant_for_variant(self.tcx, self.prog, idx as u32) {
            Some(disc) => V::Int(disc.signed_value() as u128),
            None => V::Unknown,
        }
    }

    fn eval_const(&self, e: ExprId, d: DefId) -> V {
        let Some((bytes, signed)) = self.int_of(e) else { return V::Unknown };
        let args: Vec<crate::consts::GenericArg> = match self.body.res_args.get(&e.0) {
            Some(l) => {
                let l = self.tcx.tys.list(*l);
                for &x in l {
                    let f = self.tcx.tys.flags(x);
                    if f.intersects(crate::types::TypeFlags::HAS_PARAM | crate::types::TypeFlags::HAS_INFER) || self.tcx.tys.has_infer(x) { return V::Unknown; }
                }
                l.iter().map(|x| match self.tcx.tys.kind(*x) {
                    TyKind::Const(c) => crate::consts::GenericArg::Const(*c),
                    _ => crate::consts::GenericArg::Type(*x),
                }).collect()
            }
            None => Vec::new(),
        };
        let env = crate::tcx::TypingEnv::fully_monomorphized(self.prog);
        match self.tcx.const_eval_resolve(self.prog, env, d, &args) {
            Ok(v) => match v.try_to_leaf() {
                Some(s) if s.size() as u32 == bytes => { let b = s.to_bits(bytes as u8); V::Int(if signed { signed_of(b, bytes) as u128 } else { b }) }
                _ => V::Unknown,
            },
            Err(_) => V::Unknown,
        }
    }

    fn eval_binary(&mut self, e: ExprId, pos: u32, op: BinOp, a: ExprId, b: ExprId) -> V {
        match op {
            BinOp::And | BinOp::Or => {
                let lv = self.eval(a);
                let short = if op == BinOp::And { V::Bool(false) } else { V::Bool(true) };
                if lv == short { return lv; }
                let d = self.dead;
                let rv = self.eval(b);
                // the right operand is a path of its own: a diverging right operand does not make the join dead
                self.dead = d;
                match (lv, rv) {
                    (V::Bool(_), r) => r,
                    _ => V::Unknown,
                }
            }
            _ => {
                let lv = self.eval(a);
                let rv = self.eval(b);
                if self.dead || self.body.binops.get(&e.0).is_some() { return V::Unknown; }
                match self.ty_of(a) {
                    Some(TyKind::Int(_)) => self.int_binop(pos, op, lv, rv, self.int_of(a), self.int_of(b)),
                    Some(TyKind::Bool) => match (op, lv, rv) {
                        (BinOp::Eq, V::Bool(x), V::Bool(y)) => V::Bool(x == y),
                        (BinOp::Ne, V::Bool(x), V::Bool(y)) => V::Bool(x != y),
                        (BinOp::BitAnd, V::Bool(x), V::Bool(y)) => V::Bool(x & y),
                        (BinOp::BitOr, V::Bool(x), V::Bool(y)) => V::Bool(x | y),
                        (BinOp::BitXor, V::Bool(x), V::Bool(y)) => V::Bool(x ^ y),
                        _ => V::Unknown,
                    },
                    _ => V::Unknown,
                }
            }
        }
    }

    /// check_binary_op / the division assertions, then the operation's value.
    fn int_binop(&mut self, pos: u32, op: BinOp, l: V, r: V, lt: Option<(u32, bool)>, rt: Option<(u32, bool)>) -> V {
        let Some((lb, ls)) = lt else { return V::Unknown };
        let li = if let V::Int(x) = l { Some(x) } else { None };
        let ri = if let V::Int(x) = r { Some(x) } else { None };
        match op {
            BinOp::Shl | BinOp::Shr => {
                let Some((rb, _)) = rt else { return V::Unknown };
                if let Some(rx) = ri {
                    // the shift amount as an unsigned number of its own width
                    if (rx & mask(rb)) >= (lb * 8) as u128 { self.overflow(pos); return V::Unknown; }
                    if let Some(lx) = li {
                        let amt = (rx & mask(rb)) as u32;
                        let res = if op == BinOp::Shl { (lx << amt) & mask(lb) } else if ls { (signed_of(lx, lb) >> amt) as u128 & mask(lb) } else { (lx & mask(lb)) >> amt };
                        return V::Int(if ls { signed_of(res, lb) as u128 } else { res });
                    }
                }
                V::Unknown
            }
            BinOp::Add | BinOp::Sub | BinOp::Mul => {
                let (Some(lx), Some(rx)) = (li, ri) else { return V::Unknown };
                let (res, over) = if ls {
                    let (a, b) = (lx as i128, rx as i128);
                    let (v, o) = match op { BinOp::Add => a.overflowing_add(b), BinOp::Sub => a.overflowing_sub(b), _ => a.overflowing_mul(b) };
                    let fits = lb == 16 || { let min = -(1i128 << (lb * 8 - 1)); let max = (1i128 << (lb * 8 - 1)) - 1; v >= min && v <= max };
                    (v as u128, o || !fits)
                } else {
                    let (a, b) = (lx, rx);
                    let (v, o) = match op { BinOp::Add => a.overflowing_add(b), BinOp::Sub => a.overflowing_sub(b), _ => a.overflowing_mul(b) };
                    (v, o || (lb < 16 && v > mask(lb)))
                };
                if over { self.overflow(pos); return V::Unknown; }
                V::Int(res)
            }
            BinOp::Div | BinOp::Rem => {
                if ri == Some(0) { self.panics(pos); return V::Unknown; }
                if ls {
                    if let (Some(lx), Some(rx)) = (li, ri) {
                        let min = if lb == 16 { i128::MIN } else { -(1i128 << (lb * 8 - 1)) };
                        if rx as i128 == -1 && lx as i128 == min { self.panics(pos); return V::Unknown; }
                    }
                }
                let (Some(lx), Some(rx)) = (li, ri) else { return V::Unknown };
                if ls {
                    let (a, b) = (lx as i128, rx as i128);
                    V::Int(if op == BinOp::Div { a.wrapping_div(b) } else { a.wrapping_rem(b) } as u128)
                } else {
                    V::Int(if op == BinOp::Div { lx / rx } else { lx % rx })
                }
            }
            BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor => match (li, ri) {
                (Some(a), Some(b)) => {
                    let v = match op { BinOp::BitAnd => a & b, BinOp::BitOr => a | b, _ => a ^ b };
                    V::Int(if ls { signed_of(v & mask(lb), lb) as u128 } else { v & mask(lb) })
                }
                _ => V::Unknown,
            },
            BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => match (li, ri) {
                (Some(a), Some(b)) => V::Bool(if ls {
                    let (a, b) = (a as i128, b as i128);
                    match op { BinOp::Eq => a == b, BinOp::Ne => a != b, BinOp::Lt => a < b, BinOp::Le => a <= b, BinOp::Gt => a > b, _ => a >= b }
                } else {
                    match op { BinOp::Eq => a == b, BinOp::Ne => a != b, BinOp::Lt => a < b, BinOp::Le => a <= b, BinOp::Gt => a > b, _ => a >= b }
                }),
                _ => V::Unknown,
            },
            BinOp::And | BinOp::Or => V::Unknown,
        }
    }

    fn eval_cast(&mut self, e: ExprId, x: ExprId, v: V) -> V {
        let Some(dest) = self.ty_of(e) else { return V::Unknown };
        let src = self.ty_of(x);
        match (dest, v) {
            (TyKind::Int(p), V::Int(b)) => {
                let (db, ds) = crate::types::Types::int_info(p);
                // an integer or a (sign-extended) enum discriminant: the value is already extended
                match src {
                    Some(TyKind::Int(_)) | Some(TyKind::Adt(..)) => { let t = b & mask(db); V::Int(if ds { signed_of(t, db) as u128 } else { t }) }
                    _ => V::Unknown,
                }
            }
            (TyKind::Int(p), V::Bool(b)) => { let _ = p; V::Int(b as u128) }
            (TyKind::Int(p), V::Float(f)) => {
                let (db, ds) = crate::types::Types::int_info(p);
                if f.is_nan() { return V::Int(0); }
                let r = if ds {
                    let min = if db == 16 { i128::MIN } else { -(1i128 << (db * 8 - 1)) };
                    let max = if db == 16 { i128::MAX } else { (1i128 << (db * 8 - 1)) - 1 };
                    (f as i128).clamp(min, max) as u128
                } else {
                    let max = mask(db);
                    if f <= 0.0 { 0 } else { (f as u128).min(max) }
                };
                V::Int(r)
            }
            (TyKind::Float(_), V::Int(b)) => match src {
                Some(TyKind::Int(p)) => { let (sb, ss) = crate::types::Types::int_info(p); V::Float(if ss { signed_of(b, sb) as f64 } else { (b & mask(sb)) as f64 }) }
                _ => V::Unknown,
            },
            (TyKind::Float(_), V::Float(f)) => V::Float(f),
            _ => V::Unknown,
        }
    }

    /// Whether the pattern matches the known scrutinee value (None: cannot tell).
    fn pat_matches(&mut self, p: PatId, v: V) -> Option<bool> {
        match *self.ast.pat(p) {
            Pat::Wild => Some(true),
            Pat::Paren(x) => self.pat_matches(x, v),
            Pat::Ident { by_ref: false, sub: None, .. } => if self.body.pat_local.get(&p.0).is_some() { Some(true) } else { None },
            Pat::Lit(e) => {
                let lv = self.eval(e);
                match (lv, v) { (V::Int(a), V::Int(b)) => Some(a == b), (V::Bool(a), V::Bool(b)) => Some(a == b), _ => None }
            }
            Pat::Or(ps) => {
                let ps: Vec<PatId> = self.ast.list(ps).to_vec();
                let mut undecided = false;
                for q in ps {
                    match self.pat_matches(q, v) { Some(true) => return Some(true), Some(false) => {} None => undecided = true }
                }
                if undecided { None } else { Some(false) }
            }
            _ => None,
        }
    }
}

/// Runs the known-panics lint over a function or associated constant body.
fn known_panics(prog: &Program, tcx: &Tcx, body: &Body, block: Option<BlockId>, expr: Option<ExprId>, params: &[PatId]) {
    let d = prog.def(body.def);
    // only functions, methods, closures and associated constants (a `const` item or a static is
    // evaluated by the interpreter anyway)
    if !matches!(d.kind, DefKind::Fn | DefKind::AssocFn | DefKind::AssocConst) { return; }
    let ast = &prog.files[body.file as usize].ast;
    let mut sc = Scan { body, ast, info: vec![LocalInfo::default(); body.locals.len()], in_closure: 0 };
    for &p in params { sc.pat(p); }
    if let Some(b) = block { sc.block(b); }
    if let Some(e) = expr { sc.expr(e); }
    // arguments are assigned on entry
    let mut kp = Kp { prog, tcx, body, ast, stack: Vec::new(), info: sc.info, env: Default::default(), aggs: Vec::new(), dead: false };
    if let Some(b) = block { kp.block(b); }
    if let Some(e) = expr { kp.eval(e); }
}
