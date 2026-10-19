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
pub const TRIVIAL_CASTS: Lint = lint::lint("trivial_casts", Level::Allow, &[]);
pub const TRIVIAL_NUMERIC_CASTS: Lint = lint::lint("trivial_numeric_casts", Level::Allow, &[]);

/// Body-level passes over one typed body owner.
pub fn check_body(prog: &Program, tcx: &Tcx, body: &Body) {
    if !lint::enabled() { return; }
    let d = prog.def(body.def);
    let pf = &prog.files[body.file as usize];
    let ast = &pf.ast;
    let mut w = Late { prog, tcx, body, ast, stack: Vec::new(), pcx: pattern_analysis::body_cx(prog, tcx, body), arm_body: None };
    match ast.item(d.item).kind {
        ItemKind::Fn(s, _, _) => {
            let Ok(Some(block)) = prog.fn_body(body.file, d.item) else { return };
            let _ = s;
            w.block(block);
        }
        ItemKind::Const(..) | ItemKind::Static(..) => {
            let Ok(Some(e)) = prog.const_body(body.file, d.item) else { return };
            w.expr(e);
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
                self.check_atomic_load_store(e);
                self.check_atomic_compare_exchange(e);
            }
            ExprKind::Cast(x, _) => self.check_trivial_cast(e, x),
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

    // ---- rustc_hir_typeck cast.rs trivial_cast_lint
    fn check_trivial_cast(&self, e: ExprId, x: ExprId) {
        if self.body.coercion_casts.get(&e.0).is_none() { return; }
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
