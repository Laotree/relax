//! Borrow-checking owners. Item roots are scheduled by every driver; typeck children
//! are checked with their root, even when the parent's CFG cannot reach their use.
//! Mirrors rustc_interface::passes::analysis and rustc_mir_build::builder.
use crate::ast::{ExprId, ExprKind, ItemKind};
use crate::program::{DefId, DefKind, Program};
use crate::tcx::Tcx;
use crate::typeck::Body;
use crate::types::{TyId, TyKind};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BodyKind {
    Function,
    Const,
    Static,
    AssocConst,
    InlineConst(ExprId),
    AnonConst(ExprId),
    Closure(ExprId),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CheckedBody {
    /// Item typeck root, including the generic environment inherited by children.
    pub owner: DefId,
    pub kind: BodyKind,
}

impl CheckedBody {
    pub fn item(prog: &Program, owner: DefId) -> Option<Self> {
        let d = prog.def(owner);
        if !matches!(d.kind, DefKind::Fn | DefKind::AssocFn | DefKind::Const | DefKind::Static | DefKind::AssocConst) {
            return None;
        }
        let ast = &prog.files[d.file as usize].ast;
        let kind = match (&d.kind, &ast.item(d.item).kind) {
            (DefKind::Fn | DefKind::AssocFn, ItemKind::Fn(s, b, _))
                if b.is_some() || ast.fn_sig(*s).lazy_body.is_some() => BodyKind::Function,
            (DefKind::Const, ItemKind::Const(_, Some(_))) => BodyKind::Const,
            (DefKind::AssocConst, ItemKind::Const(_, Some(_))) => BodyKind::AssocConst,
            (DefKind::Static, ItemKind::Static(_, _, Some(_))) => BodyKind::Static,
            _ => return None,
        };
        Some(Self { owner, kind })
    }

    pub fn identity_args(self, prog: &Program, tcx: &Tcx) -> Vec<TyId> {
        let n = tcx.fn_sig(prog, self.owner).map_or_else(
            || tcx.item_env(prog, self.owner).names.len(),
            |s| s.n_generics as usize,
        );
        (0..n).map(|i| tcx.tys.intern(TyKind::Param(i as u32))).collect()
    }
}

/// The single item-owner enumeration used by synchronous and background drivers.
pub fn owners(prog: &Program) -> impl Iterator<Item = CheckedBody> + '_ {
    (0..prog.defs.len()).filter_map(|i| CheckedBody::item(prog, DefId(i as u32)))
}

/// Anonymous const children for which typeck retained expression facts.
/// Inline consts remain constant operands in their parent until their region-bearing
/// signatures are available (DESIGN-regions A3). Keep their builder entry point, but
/// do not schedule a child with an independently reconstructed output lifetime.
pub fn const_children(prog: &Program, tcx: &Tcx, body: &Body) -> Vec<CheckedBody> {
    let ast = &prog.files[body.file as usize].ast;
    let mut out = Vec::new();
    for i in 0..body.expr_ty.len() {
        // Nested item ranges can share the arena; their facts belong to their
        // own typeck root, not this body.
        if body.expr_ty[i] == tcx.tys.error { continue; }
        let e = ExprId(if i < body.expr_n1 as usize {
            body.expr_lo + i as u32
        } else {
            body.expr_lo2 + i as u32 - body.expr_n1
        });
        let kind = match ast.expr(e).kind {
            ExprKind::Repeat(_, n) if !matches!(ast.expr(n).kind, ExprKind::ConstBlock(_))
                && !crate::tcx::is_infer_len(ast, n) => BodyKind::AnonConst(n),
            _ => continue,
        };
        let child = CheckedBody { owner: body.def, kind };
        out.push(child);
    }
    out
}
