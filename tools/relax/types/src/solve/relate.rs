//! Equality of type constructors shared by inference and impl-header relation.
//! rustc_type_ir/src/relate.rs:149-173 keeps every function header component.
use crate::types::{TyId, TyKind, Types};

pub trait TypeRelation {
    fn relate(&mut self, a: TyId, b: TyId) -> bool;
}

/// Aliases and inference variables belong to the inference owner. `None` asks
/// that owner to handle them; a constructor mismatch is a definitive `false`.
pub fn relate_structural(tys: &Types, cx: &mut dyn TypeRelation, a: TyId, b: TyId) -> Option<bool> {
    let ka = tys.kind(a).clone();
    let kb = tys.kind(b).clone();
    Some(match (&ka, &kb) {
            (TyKind::Tuple(x), TyKind::Tuple(y)) => {
                if x.len() != y.len() {
                    return Some(false);
                }
                for i in 0..x.len() {
                    if !cx.relate(x[i], y[i]) {
                        return Some(false);
                    }
                }
                true
            }
            (TyKind::Array(x, n), TyKind::Array(y, m)) => {
                // lengths: literals compare; a const param / variable length unifies with the
                // other side's length (as a ConstVal or its TyId)
                let ok = match (crate::types::len_ty(*n), crate::types::len_ty(*m)) {
                    (None, None) => n == m,
                    (Some(a), None) => {
                        let v = tys.intern(TyKind::ConstVal(*m));
                        cx.relate(a, v)
                    }
                    (None, Some(b)) => {
                        let v = tys.intern(TyKind::ConstVal(*n));
                        cx.relate(v, b)
                    }
                    (Some(a), Some(b)) => cx.relate(a, b),
                };
                ok && cx.relate(*x, *y)
            }
            (TyKind::Slice(x), TyKind::Slice(y)) => cx.relate(*x, *y),
            (TyKind::Ref(m1, x, _), TyKind::Ref(m2, y, _)) => m1 == m2 && cx.relate(*x, *y),
            (TyKind::Ptr(m1, x), TyKind::Ptr(m2, y)) => m1 == m2 && cx.relate(*x, *y),
            (TyKind::Adt(d1, x, _), TyKind::Adt(d2, y, _)) => {
                if d1 != d2 || x.len() != y.len() {
                    return Some(false);
                }
                for i in 0..x.len() {
                    if !cx.relate(x[i], y[i]) {
                        return Some(false);
                    }
                }
                true
            }
            (TyKind::FnPtr(p1, r1, c1, _), TyKind::FnPtr(p2, r2, c2, _)) => {
                // rustc_type_ir/src/ty_kind.rs:1151: all header fields are type identity.
                if p1.len() != p2.len() || c1 != c2 {
                    return Some(false);
                }
                for i in 0..p1.len() {
                    if !cx.relate(p1[i], p2[i]) {
                        return Some(false);
                    }
                }
                cx.relate(*r1, *r2)
            }
            (TyKind::FnDef(d, xs, _), TyKind::FnDef(e, ys, _)) if d == e && xs.len() == ys.len() => {
                for i in 0..xs.len() { if !cx.relate(xs[i], ys[i]) { return Some(false); } }
                true
            }
            (TyKind::Opaque(d, i, xs, _), TyKind::Opaque(e, j, ys, _)) if d == e && i == j && xs.len() == ys.len() => {
                for i in 0..xs.len() { if !cx.relate(xs[i], ys[i]) { return Some(false); } }
                true
            }
            (TyKind::Dyn(d, xs, bs, _, _, _, autos), TyKind::Dyn(e, ys, cs, _, _, _, others)) if d == e && autos == others && xs.len() == ys.len() && bs.len() == cs.len() => {
                for i in 0..xs.len() { if !cx.relate(xs[i], ys[i]) { return Some(false); } }
                for i in 0..bs.len() { if bs[i].0 != cs[i].0 || !cx.relate(bs[i].1, cs[i].1) { return Some(false); } }
                true
            }
            (TyKind::Closure(f, e, s, u, o), TyKind::Closure(g, j, t, v, p)) if f == g && e == j && o == p => cx.relate(*s, *t) && cx.relate(*u, *v),
        _ => return None,
    })
}
