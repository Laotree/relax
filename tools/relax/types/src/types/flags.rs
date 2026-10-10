//! Cached flags and escaping-binder depth (rustc_type_ir::flags).
use super::*;

/// The existing query bits retain their semantics; the new region/binder bits
/// visit every child, including closure owners and type-valued array lengths.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TypeFlags(u32);

impl TypeFlags {
    pub const HAS_TY_INFER: Self = Self(F_INFER);
    pub const HAS_NON_REGION_ERROR: Self = Self(F_ERROR);
    pub const HAS_TY_OPAQUE: Self = Self(F_OPAQUE);
    pub const HAS_TY_PROJECTION: Self = Self(F_PROJ);
    pub const HAS_TY_PARAM: Self = Self(F_PARAM);
    pub const HAS_TY_BOUND: Self = Self(1 << 8);
    pub const HAS_TY_PLACEHOLDER: Self = Self(1 << 9);
    pub const HAS_RE_BOUND: Self = Self(1 << 10);
    pub const HAS_RE_PLACEHOLDER: Self = Self(1 << 11);
    pub const HAS_RE_PARAM: Self = Self(1 << 12);
    pub const HAS_RE_INFER: Self = Self(1 << 13);
    pub const HAS_RE_ERROR: Self = Self(1 << 14);
    pub const HAS_RE_ERASED: Self = Self(1 << 15);
    pub const HAS_FREE_REGIONS: Self = Self(1 << 16);
    pub const HAS_ERROR: Self = Self(Self::HAS_NON_REGION_ERROR.0 | Self::HAS_RE_ERROR.0);
    pub const HAS_INFER: Self = Self(Self::HAS_TY_INFER.0 | Self::HAS_RE_INFER.0);
    pub const HAS_PARAM: Self = Self(Self::HAS_TY_PARAM.0 | Self::HAS_RE_PARAM.0);
    pub const HAS_PLACEHOLDER: Self = Self(Self::HAS_TY_PLACEHOLDER.0 | Self::HAS_RE_PLACEHOLDER.0);
    pub const HAS_BOUND_VARS: Self = Self(Self::HAS_TY_BOUND.0 | Self::HAS_RE_BOUND.0);
    pub const HAS_REGIONS: Self = Self(Self::HAS_FREE_REGIONS.0 | Self::HAS_RE_BOUND.0 | Self::HAS_RE_ERASED.0);

    pub fn contains(self, other: Self) -> bool { self.0 & other.0 == other.0 }
    pub fn intersects(self, other: Self) -> bool { self.0 & other.0 != 0 }
    pub fn bits(self) -> u32 { self.0 }
}

impl std::ops::BitOr for TypeFlags {
    type Output = Self;
    fn bitor(self, rhs: Self) -> Self { Self(self.0 | rhs.0) }
}

#[derive(Default)]
struct Computation {
    flags: u32,
    outer: DebruijnIndex,
}

impl Computation {
    fn add(&mut self, flags: u32, outer: DebruijnIndex, binders: u32) {
        self.flags |= flags;
        self.outer = self.outer.max(outer.saturating_sub(binders));
    }

    fn ty(&mut self, tys: &Types, ty: TyId, binders: u32) {
        let e = tys.entry(ty);
        self.add(e.flags & !0xff, e.outer_exclusive_binder, binders);
    }

    fn region(&mut self, tys: &Types, r: RegionId, binders: u32) {
        use TypeFlags as F;
        let (flags, outer) = match tys.region_kind(r) {
            RegionKind::ReBound(d, _) => (F::HAS_RE_BOUND, d.checked_add(1).expect("bound region index overflow")),
            RegionKind::RePlaceholder { .. } => (F::HAS_RE_PLACEHOLDER | F::HAS_FREE_REGIONS, 0),
            RegionKind::ReEarlyParam(_) => (F::HAS_RE_PARAM | F::HAS_FREE_REGIONS, 0),
            RegionKind::ReVar(_) => (F::HAS_RE_INFER | F::HAS_FREE_REGIONS, 0),
            RegionKind::ReError => (F::HAS_RE_ERROR | F::HAS_FREE_REGIONS, 0),
            RegionKind::ReErased => (F::HAS_RE_ERASED, 0),
            RegionKind::ReStatic | RegionKind::ReLateParam(..) => (F::HAS_FREE_REGIONS, 0),
        };
        self.add(flags.0, outer, binders);
    }

    fn regions(&mut self, tys: &Types, rs: RegionArgsId, binders: u32) {
        if rs != RegionArgsId::EMPTY {
            for r in tys.region_args(rs).iter() { self.region(tys, *r, binders); }
        }
    }
}

impl Types {
    pub fn flags(&self, t: TyId) -> TypeFlags { TypeFlags(self.fl(t)) }

    /// One past the greatest escaping de Bruijn index, or zero when all bound
    /// variables are captured internally. Even an empty FnPtr/dyn binder counts.
    pub fn outer_exclusive_binder(&self, t: TyId) -> DebruijnIndex {
        self.entry(t).outer_exclusive_binder
    }

    pub fn has_vars_bound_at_or_above(&self, t: TyId, depth: DebruijnIndex) -> bool {
        self.outer_exclusive_binder(t) > depth
    }

    pub fn has_escaping_bound_vars(&self, t: TyId) -> bool {
        self.has_vars_bound_at_or_above(t, 0)
    }

    pub fn has_placeholders(&self, t: TyId) -> bool {
        self.flags(t).intersects(TypeFlags::HAS_PLACEHOLDER)
    }

    pub(super) fn binder_flags_of(&self, k: &TyKind) -> (u32, DebruijnIndex) {
        let mut c = Computation::default();
        match k {
            TyKind::Bound(d, _) => c.add(TypeFlags::HAS_TY_BOUND.0, d.checked_add(1).expect("bound type index overflow"), 0),
            TyKind::Placeholder(_) => c.flags |= TypeFlags::HAS_TY_PLACEHOLDER.0,
            TyKind::Tuple(v) => for t in v { c.ty(self, *t, 0); },
            TyKind::Array(t, n) => {
                c.ty(self, *t, 0);
                if let Some(t) = len_ty(*n) { c.ty(self, t, 0); }
            }
            TyKind::Slice(t) | TyKind::Ptr(_, t) => c.ty(self, *t, 0),
            TyKind::Ref(_, t, r) => { c.ty(self, *t, 0); c.region(self, *r, 0); }
            TyKind::Adt(_, v, rs) | TyKind::FnDef(_, v, rs) | TyKind::Assoc(_, v, rs) | TyKind::Opaque(_, _, v, rs) => {
                for t in v { c.ty(self, *t, 0); }
                c.regions(self, *rs, 0);
            }
            TyKind::FnPtr(ps, r, _, _) => {
                for t in ps { c.ty(self, *t, 1); }
                c.ty(self, *r, 1);
            }
            TyKind::Dyn(_, v, bs, rs, r, _, _) => {
                for t in v { c.ty(self, *t, 1); }
                for (_, t, _) in bs { c.ty(self, *t, 1); }
                c.regions(self, *rs, 1);
                c.region(self, *r, 0);
            }
            TyKind::Closure(_, _, s, u, o) => for t in [s, u, o] { c.ty(self, *t, 0); },
            TyKind::Bool | TyKind::Char | TyKind::Str | TyKind::Int(_) | TyKind::Float(_) |
            TyKind::Never | TyKind::Param(_) | TyKind::Infer(_) | TyKind::ConstVal(_) | TyKind::Error => {}
        }
        (c.flags, c.outer)
    }
}
