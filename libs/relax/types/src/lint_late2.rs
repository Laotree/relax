//! More late (type-aware) builtin lints of `makepad check`: `dangling_pointers_from_temporaries`
//! and `dangling_pointers_from_locals` (rustc_lint dangling.rs), `const_item_mutation`
//! (rustc_mir_transform check_const_item_mutation.rs), ... All run over one walk of a typed body
//! and are check-only (reached from `lint_late::check_body` behind `lint::enabled()`).

use crate::ast::*;
use crate::ast_visit::{self, Visitor};
use crate::lint::{self, Level, Lint};
use crate::lang_items::LangItem;
use crate::program::{DefId, DefKind, Program};
use crate::tcx::Tcx;
use crate::typeck::{Body, Res};
use crate::types::{TyId, TyKind};
use std::collections::HashMap;

pub const DANGLING_POINTERS_FROM_TEMPORARIES: Lint = lint::lint("dangling_pointers_from_temporaries", Level::Warn, &[]);
pub const DANGLING_POINTERS_FROM_LOCALS: Lint = lint::lint("dangling_pointers_from_locals", Level::Warn, &[]);
pub const CONST_ITEM_MUTATION: Lint = lint::lint("const_item_mutation", Level::Warn, &[]);

/// Runs the passes over one body owner (`block`: a fn body, `expr`: a const / static initialiser).
pub fn check_body(prog: &Program, tcx: &Tcx, body: &Body, block: Option<BlockId>, expr: Option<ExprId>) {
    if !lint::enabled() { return; }
    let pf = &prog.files[body.file as usize];
    let ast = &pf.ast;
    let mut w = L2 {
        prog, tcx, body, ast, stack: Vec::new(), fns: Vec::new(), owner: HashMap::new(), init: HashMap::new(), names: HashMap::new(),
        inside_call_args: false, reset_block: false, closure: u32::MAX, active: false,
    };
    // pre-pass: which closure declares each local, the initialisers of plain bindings
    {
        let mut pre = Pre { w: &mut w, closure: u32::MAX };
        if let (Some(_), ItemKind::Fn(s, _, _)) = (block, ast.item(prog.def(body.def).item).kind) {
            for p in ast.list(ast.fn_sig(s).params) { pre.pat(p.pat); }
        }
        if let Some(b) = block { pre.block(b); }
        if let Some(e) = expr { pre.expr(e); }
    }
    let d = prog.def(body.def);
    if let Some(b) = block {
        // the fn itself
        let ret_ptr = match ast.item(d.item).kind {
            ItemKind::Fn(s, _, _) => ast.fn_sig(s).ret.filter(|&t| matches!(ast.ty(t), Ty::Ptr(..))).map(|t| (t, ast_ty_pos(ast, t))),
            _ => None,
        };
        let kind = if d.kind == DefKind::AssocFn { "method" } else { "function" };
        w.active = true;
        w.fns.push(w.fn_cx(body.ret, ret_ptr.map(|x| x.1), kind, u32::MAX));
        w.block(b);
        // the implicit return expression
        if let Some(t) = innermost_tail(ast, b) { w.lint_addr_of_local(t); }
        w.fns.pop();
    }
    if let Some(e) = expr { w.expr(e); }
}

fn ast_ty_pos(ast: &Ast, t: crate::ast::TyId) -> u32 {
    let _ = (ast, t);
    0
}

struct FnCx {
    /// the pointee type of a raw-pointer return type with a layout that is not a 1-ZST
    inner: Option<TyId>,
    ret_ty: TyId,
    kind: &'static str,
    /// the closure expression that owns the locals of this body (u32::MAX: the fn)
    owner: u32,
}

struct L2<'a> {
    prog: &'a Program,
    tcx: &'a Tcx,
    body: &'a Body,
    ast: &'a Ast,
    /// the attributes of the enclosing statements, arms, ..., outermost first
    stack: Vec<Attr>,
    fns: Vec<Option<FnCx>>,
    /// local -> the closure expression declaring it (u32::MAX: the body owner)
    owner: HashMap<u32, u32>,
    /// local -> the initialiser of an immutable plain binding
    init: HashMap<u32, ExprId>,
    /// local -> its name
    names: HashMap<u32, Ident>,
    /// DanglingPointerSearcher::inside_call_args
    inside_call_args: bool,
    /// the next `block` call is the block of a block expression (statements reset the flag)
    reset_block: bool,
    /// the closure being walked
    closure: u32,
    /// inside a fn or closure body (rustc `check_fn`; const and static initialisers are not searched)
    active: bool,
}

/// The first pass.
struct Pre<'w, 'a> {
    w: &'w mut L2<'a>,
    closure: u32,
}

impl<'w, 'a> Visitor<'a> for Pre<'w, 'a> {
    fn ast(&self) -> &'a Ast { self.w.ast }
    fn expr(&mut self, e: ExprId) {
        let saved = self.closure;
        if matches!(self.w.ast.expr(e).kind, ExprKind::Closure(_) | ExprKind::Async(..)) { self.closure = e.0; }
        ast_visit::walk_expr(self, e);
        self.closure = saved;
    }
    fn pat(&mut self, p: PatId) {
        if let Pat::Ident { name, .. } = *self.w.ast.pat(p) {
            if let Some(&l) = self.w.body.pat_local.get(&p.0) {
                self.w.owner.insert(l, self.closure);
                self.w.names.insert(l, name);
            }
        }
        ast_visit::walk_pat(self, p);
    }
    fn stmt(&mut self, s: &Stmt, b: BlockId) {
        if let Stmt::Let(r) = *s {
            let l = *self.w.ast.row(r);
            if let (Pat::Ident { by_ref: false, mutbl: false, sub: None, .. }, Some(init)) = (*self.w.ast.pat(l.pat), l.init) {
                if let Some(&loc) = self.w.body.pat_local.get(&l.pat.0) { self.w.init.insert(loc, init); }
            }
        }
        ast_visit::walk_stmt(self, s);
        let _ = b;
    }
}

fn unparen(ast: &Ast, mut e: ExprId) -> ExprId {
    while let ExprKind::Paren(x) = ast.expr(e).kind { e = x; }
    e
}

/// The tail expression of a block (`Block::expr`).
fn block_tail(ast: &Ast, b: BlockId) -> Option<ExprId> {
    match *ast.stmts(b).last()? {
        Stmt::Expr(e, false) => Some(e),
        Stmt::Attrs(r) => { let a = *ast.row(r); if a.semi { None } else { Some(a.expr) } }
        _ => None,
    }
}

/// `Block::innermost_block().expr`.
fn innermost_tail(ast: &Ast, mut b: BlockId) -> Option<ExprId> {
    loop {
        let t = block_tail(ast, b)?;
        match ast.expr(unparen(ast, t)).kind {
            ExprKind::Block(b2, _) | ExprKind::Unsafe(b2) => b = b2,
            _ => return Some(t),
        }
    }
}

/// `Expr::peel_blocks`.
fn peel_blocks(ast: &Ast, mut e: ExprId) -> ExprId {
    loop {
        e = unparen(ast, e);
        match ast.expr(e).kind {
            ExprKind::Block(b, _) | ExprKind::Unsafe(b) if ast.stmts(b).len() == 1 && block_tail(ast, b).is_some() => e = block_tail(ast, b).unwrap(),
            _ => return e,
        }
    }
}

/// `#[rustc_diagnostic_item = "name"]` of a definition.
fn diag_name(prog: &Program, d: DefId) -> Option<String> {
    let def = prog.def(d);
    if !matches!(def.kind, DefKind::Struct | DefKind::Enum | DefKind::Union | DefKind::Trait | DefKind::Fn | DefKind::AssocFn | DefKind::TypeAlias) { return None; }
    let ast = &prog.files[def.file as usize].ast;
    let p = prog.src(def.file);
    for a in ast.list(ast.item(def.item).attrs) {
        if lint::attr_path(prog, def.file, a) != b"rustc_diagnostic_item" { continue; }
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

fn has_def_attr(prog: &Program, d: DefId, name: &str) -> bool {
    let def = prog.def(d);
    if !matches!(def.kind, DefKind::Fn | DefKind::AssocFn | DefKind::Struct | DefKind::Enum | DefKind::Union | DefKind::Trait | DefKind::Const | DefKind::AssocConst) { return false; }
    let ast = &prog.files[def.file as usize].ast;
    lint::has_attr(prog, def.file, ast.list(ast.item(def.item).attrs), name)
}

impl<'a> L2<'a> {
    fn kind(&self, t: TyId) -> TyKind { *self.tcx.tys.kind(t) }

    fn emit(&self, lint: &Lint, pos: u32, msg: &str) {
        if lint::external(self.prog, self.body.file, pos) { return; }
        lint::emit_in(self.prog, self.body.def, &self.stack, lint, self.body.file, pos, msg);
    }

    fn expr_ty(&self, e: ExprId) -> Option<TyId> {
        let i = self.body.expr_ix(e);
        if i < self.body.expr_ty.len() && self.body.expr_typed.get(i) { Some(self.body.expr_ty[i]) } else { None }
    }

    fn lang(&self, item: LangItem) -> Option<DefId> { self.tcx.lang_items.get(item) }

    fn fn_cx(&self, ret: TyId, ret_ptr: Option<u32>, kind: &'static str, owner: u32) -> Option<FnCx> {
        ret_ptr?;
        let TyKind::Ptr(_, inner) = self.kind(ret) else { return None };
        // `layout_of(inner).is_ok_and(|layout| !layout.is_1zst())`
        if self.layout_1zst(inner, 0) != Some(false) { return None; }
        Some(FnCx { inner: Some(inner), ret_ty: ret, kind, owner })
    }

    /// Whether the layout of `t` is a 1-ZST (size 0, alignment 1); None: the layout cannot be
    /// computed (generic parameters inline, projections).
    fn layout_1zst(&self, t: TyId, depth: u32) -> Option<bool> {
        if depth > 12 { return None; }
        match self.kind(t) {
            TyKind::Bool | TyKind::Char | TyKind::Int(_) | TyKind::Float(_) | TyKind::Str | TyKind::Ref(..) | TyKind::Ptr(..)
            | TyKind::FnPtr(..) | TyKind::Dyn(..) | TyKind::Foreign(_) => Some(false),
            TyKind::Never | TyKind::FnDef(..) => Some(true),
            TyKind::Slice(e) => { self.layout_1zst(e, depth + 1)?; Some(false) }
            TyKind::Tuple(l) => {
                let mut zst = true;
                for &x in self.tcx.tys.list(l) { zst &= self.layout_1zst(x, depth + 1)?; }
                Some(zst)
            }
            TyKind::Array(e, len) => {
                let ez = self.layout_1zst(e, depth + 1)?;
                match len.try_to_target_usize(&self.tcx.tys) {
                    Some(0) => Some(ez || matches!(self.kind(e), TyKind::Bool | TyKind::Int(crate::program::Prim::I8 | crate::program::Prim::U8))),
                    Some(_) => Some(ez),
                    None => None,
                }
            }
            TyKind::Adt(d, args, _) => {
                let a = self.tcx.adts.get(&d)?;
                if a.is_phantom_data() { return Some(true); }
                let mut all = true;
                for v in &a.variants {
                    for f in &v.fields {
                        let ft = self.tcx.tys.subst(f.ty, self.tcx.tys.list(args));
                        all &= self.layout_1zst(ft, depth + 1)?;
                    }
                }
                if a.variants.is_empty() { return Some(true); }
                if a.is_union || a.repr_align > 1 { return Some(false); }
                if a.is_enum {
                    return Some(a.variants.len() == 1 && all && a.repr_int.is_none());
                }
                Some(all)
            }
            _ => None,
        }
    }

    // ---------------------------------------------------------------- dangling pointers

    /// `cx.expr_or_init`.
    fn expr_or_init(&self, e: ExprId) -> ExprId {
        let mut e = peel_blocks(self.ast, e);
        while let ExprKind::Path(_) = self.ast.expr(e).kind {
            let Some(Res::Local(l)) = self.body.res.get(&e.0).copied() else { break };
            let Some(&init) = self.init.get(&l) else { break };
            e = peel_blocks(self.ast, init);
        }
        e
    }

    /// `utils::peel_casts`.
    fn peel_casts(&self, e: ExprId) -> ExprId {
        let ast = self.ast;
        let mut e = e;
        loop {
            e = peel_blocks(ast, e);
            let next = match ast.expr(e).kind {
                ExprKind::Cast(x, _) => Some(x),
                ExprKind::MethodCall(x, row) if ast.list(ast.row(row).args).is_empty() => {
                    let name = self.body.methods.get(&e.0).and_then(|m| diag_name(self.prog, m.def));
                    if matches!(name.as_deref(), Some("ptr_cast" | "const_ptr_cast" | "ptr_cast_mut" | "ptr_cast_const")) { Some(x) } else { None }
                }
                ExprKind::Call(f, args) if ast.list(args).len() == 1 && matches!(ast.expr(unparen(ast, f)).kind, ExprKind::Path(_)) => {
                    let name = match self.body.res.get(&unparen(ast, f).0) { Some(Res::Def(d)) => diag_name(self.prog, *d), _ => None };
                    if matches!(name.as_deref(), Some("ptr_from_ref" | "unsafe_cell_raw_get" | "transmute")) { Some(ast.list(args)[0]) } else { None }
                }
                _ => None,
            };
            e = match next {
                Some(x) => x,
                None => {
                    let init = self.expr_or_init(e);
                    if init != e { init } else { return e }
                }
            };
        }
    }

    /// `lint_addr_of_local`: `&<local of this body>` returned from a fn returning a raw pointer.
    fn lint_addr_of_local(&self, expr: ExprId) {
        let Some(Some(cx)) = self.fns.last() else { return };
        let inner = self.peel_casts(expr);
        let ExprKind::AddrOf(false, _, x) = self.ast.expr(inner).kind else { return };
        let x = peel_blocks(self.ast, x);
        if !matches!(self.ast.expr(x).kind, ExprKind::Path(_)) { return; }
        let Some(Res::Local(l)) = self.body.res.get(&x.0).copied() else { return };
        if self.owner.get(&l).copied() != Some(cx.owner) { return; }
        let name = self.names.get(&l).map(|n| self.prog.files[self.body.file as usize].text(*n).to_string()).unwrap_or_default();
        let _ = (cx.inner, cx.ret_ty);
        let pos = self.ast.expr(expr).lo;
        self.emit(&DANGLING_POINTERS_FROM_LOCALS, pos, &format!("{} returns a dangling pointer to dropped local variable `{}`", cx.kind, name));
    }

    /// `is_temporary_rvalue`.
    fn is_temporary_rvalue(&self, e: ExprId) -> bool {
        let e = unparen(self.ast, e);
        match self.ast.expr(e).kind {
            ExprKind::Call(..) | ExprKind::MethodCall(..) | ExprKind::Binary(..) | ExprKind::Mac(_) => true,
            ExprKind::If(..) | ExprKind::Loop(..) | ExprKind::Match(..) | ExprKind::Block(..) | ExprKind::Unsafe(_)
            | ExprKind::While(_) | ExprKind::For(_) | ExprKind::Try(_) | ExprKind::Await(_) => true,
            ExprKind::Struct(_) | ExprKind::Range(..) => true,
            _ => false,
        }
    }

    /// `owns_allocation`.
    fn owns_allocation(&self, t: TyId) -> bool {
        match self.kind(t) {
            TyKind::Array(..) => true,
            TyKind::Adt(d, args, _) if Some(d) == self.lang(LangItem::OwnedBox) => {
                let Some(&inner) = self.tcx.tys.list(args).first() else { return false };
                match self.kind(inner) {
                    TyKind::Slice(_) | TyKind::Str => true,
                    TyKind::Adt(i, ..) if Some(i) == self.lang(LangItem::CStr) => true,
                    _ => self.owns_allocation(inner),
                }
            }
            TyKind::Adt(d, ..) => {
                if [LangItem::String, LangItem::MaybeUninit, LangItem::UnsafeCell].iter().any(|&l| Some(d) == self.lang(l)) { return true; }
                matches!(diag_name(self.prog, d).as_deref(), Some("cstring_type" | "Vec" | "Cell" | "SyncUnsafeCell"))
            }
            _ => false,
        }
    }

    /// `lint_expr` of dangling.rs.
    fn lint_temporary(&self, e: ExprId) {
        let ExprKind::MethodCall(recv, row) = self.ast.expr(e).kind else { return };
        if !self.is_temporary_rvalue(recv) { return; }
        let Some(ty) = self.expr_ty(recv) else { return };
        if !self.owns_allocation(ty) { return; }
        let Some(m) = self.body.methods.get(&e.0) else { return };
        if !has_def_attr(self.prog, m.def, "rustc_as_ptr") { return; }
        let name = self.ast.row(row).name;
        let tys = crate::typeck::ty_to_string(false, self.prog, self.tcx, ty);
        self.emit(&DANGLING_POINTERS_FROM_TEMPORARIES, name.lo, &format!("this creates a dangling pointer because temporary `{}` is dropped at end of statement", tys));
    }
}

// ---------------------------------------------------------------- const_item_mutation

impl<'a> L2<'a> {
    /// The root of a place expression that is mutably used, when it is a `const` item (or a
    /// const parameter) reached by field / builtin index projections only: (the const's path
    /// expression, whether a projection is overloaded `IndexMut`). None: a dereference
    /// is involved (the mutation goes through a pointer), or the root is no constant.
    fn const_place_root(&self, e: ExprId) -> Option<(ExprId, bool)> {
        let e = unparen(self.ast, e);
        match self.ast.expr(e).kind {
            ExprKind::Path(_) => match self.body.res.get(&e.0).copied() {
                Some(Res::Def(d)) if matches!(self.prog.def(d).kind, DefKind::Const | DefKind::AssocConst) => Some((e, false)),
                Some(Res::ConstParam(_)) => Some((e, false)),
                _ => None,
            },
            ExprKind::Field(b, _) | ExprKind::TupleField(b, _) => {
                // a field of a reference or a smart pointer is reached through a dereference
                let t = self.expr_ty(b)?;
                if !matches!(self.kind(t), TyKind::Adt(..) | TyKind::Tuple(_)) { return None; }
                if self.body.ov_derefs.get(&(b.0, 0)).is_some() || self.body.ov_derefs.get(&(e.0, 0)).is_some() { return None; }
                self.const_place_root(b)
            }
            ExprKind::Index(b, _) => {
                if self.body.ov_index.get(&e.0).is_some() {
                    return self.const_place_root(b).map(|(r, _)| (r, true));
                }
                let t = self.expr_ty(b)?;
                if !matches!(self.kind(t), TyKind::Array(..)) { return None; }
                self.const_place_root(b)
            }
            _ => None,
        }
    }

    fn const_has_dtor(&self, root: ExprId) -> bool {
        let Some(Res::Def(d)) = self.body.res.get(&root.0).copied() else { return false };
        let Some(t) = self.tcx.const_ty(self.prog, d) else { return false };
        match self.kind(t) {
            TyKind::Adt(a, ..) => self.tcx.adt_destructor(a).is_some(),
            _ => false,
        }
    }

    fn lint_const_mutation(&self, e: ExprId) {
        const MODIFY: &str = "attempting to modify a `const` item";
        const BORROW: &str = "taking a mutable reference to a `const` item";
        let ast = self.ast;
        let pos = ast.expr(e).lo;
        match ast.expr(e).kind {
            ExprKind::Assign(l, _) | ExprKind::AssignOp(_, l, _) => {
                let overloaded_op = matches!(ast.expr(e).kind, ExprKind::AssignOp(..)) && self.body.binops.get(&e.0).is_some();
                let Some((root, over)) = self.const_place_root(l) else { return };
                if overloaded_op {
                    self.emit(&CONST_ITEM_MUTATION, pos, BORROW);
                } else if over {
                    self.emit(&CONST_ITEM_MUTATION, pos, BORROW);
                } else if unparen(ast, l) != root && !self.const_has_dtor(root) {
                    self.emit(&CONST_ITEM_MUTATION, pos, MODIFY);
                }
            }
            ExprKind::AddrOf(false, true, x) => {
                if self.const_place_root(x).is_some() { self.emit(&CONST_ITEM_MUTATION, pos, BORROW); }
            }
            ExprKind::MethodCall(r, _) => {
                let Some(m) = self.body.methods.get(&e.0) else { return };
                if m.autoref != 2 { return; }
                if m.derefs > 0 {
                    let overloaded = [e.0, r.0, unparen(ast, r).0].iter().any(|k| self.body.ov_derefs.get(&(*k, 0)).is_some());
                    if !overloaded { return; }
                }
                if self.const_place_root(r).is_some() { self.emit(&CONST_ITEM_MUTATION, pos, BORROW); }
            }
            _ => {}
        }
    }
}

impl<'a> Visitor<'a> for L2<'a> {
    fn ast(&self) -> &'a Ast { self.ast }
    fn enter_attrs(&mut self, attrs: List<Attr>) { self.stack.extend_from_slice(self.ast.list(attrs)); }
    fn leave_attrs(&mut self, attrs: List<Attr>) {
        let n = self.ast.list(attrs).len();
        self.stack.truncate(self.stack.len() - n);
    }

    fn block(&mut self, b: BlockId) {
        let ast = self.ast;
        let reset = std::mem::replace(&mut self.reset_block, false);
        let blk = *ast.block(b);
        self.enter_attrs(blk.attrs);
        let saved = self.inside_call_args;
        let stmts = ast.stmts(b);
        for (i, s) in stmts.iter().enumerate() {
            if reset {
                let tail = i + 1 == stmts.len() && matches!(*s, Stmt::Expr(_, false));
                self.inside_call_args = if tail { saved } else { false };
            }
            self.stmt(s, b);
        }
        self.inside_call_args = saved;
        self.leave_attrs(blk.attrs);
    }

    fn expr(&mut self, e: ExprId) {
        let ast = self.ast;
        if self.active && !self.inside_call_args { self.lint_temporary(e); }
        self.lint_const_mutation(e);
        match ast.expr(e).kind {
            ExprKind::Call(f, args) => {
                self.expr(f);
                let saved = std::mem::replace(&mut self.inside_call_args, true);
                for &a in ast.list(args) { self.expr(a); }
                self.inside_call_args = saved;
            }
            ExprKind::MethodCall(r, row) => {
                self.expr(r);
                let saved = std::mem::replace(&mut self.inside_call_args, true);
                for &a in ast.list(ast.row(row).args) { self.expr(a); }
                self.inside_call_args = saved;
            }
            ExprKind::Block(b, _) | ExprKind::Unsafe(b) => {
                self.reset_block = true;
                self.block(b);
            }
            ExprKind::If(c, then, els) => {
                self.expr(c);
                self.reset_block = true;
                self.block(then);
                if let Some(x) = els.get() { self.expr(x); }
            }
            ExprKind::While(row) => {
                let w = *ast.row(row);
                self.expr(w.cond);
                self.reset_block = true;
                self.block(w.body);
            }
            ExprKind::For(row) => {
                let f = *ast.row(row);
                self.expr(f.iter);
                self.pat(f.pat);
                self.reset_block = true;
                self.block(f.body);
            }
            ExprKind::Closure(row) => {
                let c = *ast.row(row);
                let ret_ptr = c.ret.filter(|&t| matches!(ast.ty(t), Ty::Ptr(..)));
                let ret = self.body.closure_sigs.get(&e.0).and_then(|s| match self.kind(s.liberated) { TyKind::FnPtr(_, r, _, _) => Some(r), _ => None });
                let cx = match (ret_ptr, ret) { (Some(_), Some(r)) => self.fn_cx(r, Some(0), "closure", e.0), _ => None };
                let saved = (std::mem::replace(&mut self.inside_call_args, false), std::mem::replace(&mut self.closure, e.0), std::mem::replace(&mut self.active, true));
                self.fns.push(cx);
                ast_visit::walk_expr(self, e);
                if let Some(Some(_)) = self.fns.last() {
                    if let ExprKind::Block(b, l) = ast.expr(unparen(ast, c.body)).kind {
                        if l.get().is_none() { if let Some(t) = innermost_tail(ast, b) { self.lint_addr_of_local(t); } }
                    }
                }
                self.fns.pop();
                self.inside_call_args = saved.0;
                self.closure = saved.1;
                self.active = saved.2;
            }
            ExprKind::Async(..) => {
                let saved = std::mem::replace(&mut self.inside_call_args, false);
                let act = std::mem::replace(&mut self.active, true);
                self.fns.push(None);
                ast_visit::walk_expr(self, e);
                self.fns.pop();
                self.active = act;
                self.inside_call_args = saved;
            }
            ExprKind::ConstBlock(_) => {}
            ExprKind::Return(x) => {
                if let Some(x) = x.get() { self.lint_addr_of_local(x); }
                ast_visit::walk_expr(self, e);
            }
            _ => ast_visit::walk_expr(self, e),
        }
    }
}
