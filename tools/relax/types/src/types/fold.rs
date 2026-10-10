//! Binder-aware type folding, shifting, and instantiation. FnPtr and each dyn
//! predicate introduce a binder even when their bound-region count is zero.
use super::*;
use std::collections::HashMap;

/// A structural folder. `depth` counts binders entered since the root value.
/// Overridden type callbacks can recurse with `super_fold_ty`.
pub trait TypeFolder {
    fn fold_ty(&mut self, tys: &Types, t: TyId, depth: DebruijnIndex) -> TyId {
        super_fold_ty(tys, t, self, depth)
    }
    /// Consts share TyId storage; callers identify them by argument position.
    /// rustc_type_ir/src/fold.rs:144 (TypeFolder::fold_const).
    fn fold_const(&mut self, tys: &Types, t: TyId, depth: DebruijnIndex) -> TyId {
        self.fold_ty(tys, t, depth)
    }
    fn fold_args(&mut self, tys: &Types, _def: DefId, args: &[TyId], _offset: u32, depth: DebruijnIndex) -> Vec<TyId> {
        let mut result = Vec::with_capacity(args.len());
        for t in args { result.push(self.fold_ty(tys, *t, depth)); }
        result
    }
    fn fold_region(&mut self, _tys: &Types, r: RegionId, _depth: DebruijnIndex) -> RegionId { r }
}

pub fn super_fold_ty<F: TypeFolder + ?Sized>(tys: &Types, t: TyId, f: &mut F, depth: DebruijnIndex) -> TyId {
    let mut list = |v: &[TyId], depth| v.iter().map(|t| f.fold_ty(tys, *t, depth)).collect::<Vec<_>>();
    let k = match tys.kind(t) {
        TyKind::Tuple(v) => TyKind::Tuple(list(v, depth)),
        TyKind::Array(t, n) => {
            let t = f.fold_ty(tys, *t, depth);
            return match len_ty(*n) {
                Some(n) => tys.mk_array(t, f.fold_const(tys, n, depth)),
                None => tys.intern(TyKind::Array(t, *n)),
            };
        }
        TyKind::Slice(t) => TyKind::Slice(f.fold_ty(tys, *t, depth)),
        TyKind::Ptr(m, t) => TyKind::Ptr(*m, f.fold_ty(tys, *t, depth)),
        TyKind::Ref(m, t, r) => TyKind::Ref(*m, f.fold_ty(tys, *t, depth), f.fold_region(tys, *r, depth)),
        TyKind::Adt(d, v, rs) => TyKind::Adt(*d, f.fold_args(tys, *d, v, 0, depth), fold_regions(tys, *rs, f, depth)),
        TyKind::FnDef(d, v, rs) => TyKind::FnDef(*d, f.fold_args(tys, *d, v, 0, depth), fold_regions(tys, *rs, f, depth)),
        TyKind::Assoc(d, v, rs) => TyKind::Assoc(*d, f.fold_args(tys, *d, v, 0, depth), fold_regions(tys, *rs, f, depth)),
        TyKind::Opaque(d, i, v, rs) => TyKind::Opaque(*d, *i, f.fold_args(tys, *d, v, 0, depth), fold_regions(tys, *rs, f, depth)),
        TyKind::FnPtr(ps, r, c, n) => TyKind::FnPtr(list(ps, depth + 1), f.fold_ty(tys, *r, depth + 1), *c, *n),
        TyKind::Dyn(d, v, bs, rs, r, n, autos) => {
            let v = f.fold_args(tys, *d, v, 1, depth + 1);
            let bs = bs.iter().map(|(d, t, n)| (*d, f.fold_ty(tys, *t, depth + 1), *n)).collect();
            TyKind::Dyn(*d, v.into(), bs, fold_regions(tys, *rs, f, depth + 1), f.fold_region(tys, *r, depth), *n, autos.clone())
        }
        TyKind::Closure(fi, e, s, u, o) => TyKind::Closure(*fi, *e,
            f.fold_ty(tys, *s, depth), f.fold_ty(tys, *u, depth), f.fold_ty(tys, *o, depth)),
        TyKind::Bool | TyKind::Char | TyKind::Str | TyKind::Int(_) | TyKind::Float(_) |
        TyKind::Never | TyKind::Param(_) | TyKind::Infer(_) | TyKind::ConstVal(_) |
        TyKind::Error | TyKind::Bound(..) | TyKind::Placeholder(_) => return t,
    };
    tys.intern(k)
}

fn fold_regions<F: TypeFolder + ?Sized>(tys: &Types, rs: RegionArgsId, f: &mut F, depth: DebruijnIndex) -> RegionArgsId {
    if rs == RegionArgsId::EMPTY { return rs; }
    tys.intern_region_args(&tys.region_args(rs).iter().map(|r| f.fold_region(tys, *r, depth)).collect::<Vec<_>>())
}

struct Shifter {
    amount: u32,
    out: bool,
}

impl Shifter {
    fn index(&self, d: DebruijnIndex, depth: DebruijnIndex) -> DebruijnIndex {
        if self.out {
            d.checked_sub(self.amount).filter(|d| *d >= depth)
                .expect("cannot shift a bound variable out through its binder")
        } else {
            d.checked_add(self.amount).expect("bound variable index overflow")
        }
    }
}

impl TypeFolder for Shifter {
    fn fold_ty(&mut self, tys: &Types, t: TyId, depth: DebruijnIndex) -> TyId {
        if !tys.has_vars_bound_at_or_above(t, depth) { return t; }
        match tys.kind(t) {
            TyKind::Bound(d, b) if *d >= depth => tys.intern(TyKind::Bound(self.index(*d, depth), *b)),
            _ => super_fold_ty(tys, t, self, depth),
        }
    }
    fn fold_region(&mut self, tys: &Types, r: RegionId, depth: DebruijnIndex) -> RegionId {
        match tys.region_kind(r) {
            RegionKind::ReBound(d, v) if d >= depth => tys.intern_region(RegionKind::ReBound(self.index(d, depth), v)),
            _ => r,
        }
    }
}

/// Replaces the variables of one removed binder. Callbacks return values in the
/// scope *outside* that binder; escaping variables in them are shifted under any
/// nested binders. Each distinct variable is passed to its callback once.
pub struct BoundVarReplacer<R, T> {
    regions: R,
    types: T,
    region_cache: HashMap<BoundVar, RegionId>,
    type_cache: HashMap<BoundTy, TyId>,
    folded: HashMap<(DebruijnIndex, TyId), TyId>,
}

impl<R, T> BoundVarReplacer<R, T>
where R: FnMut(BoundVar) -> RegionId, T: FnMut(BoundTy) -> TyId {
    pub fn new(regions: R, types: T) -> Self {
        Self { regions, types, region_cache: HashMap::new(), type_cache: HashMap::new(), folded: HashMap::new() }
    }

    /// `value` is the binder's payload (the binder itself has been skipped).
    /// For FnPtr, pass its inputs/output individually using this same replacer,
    /// or pack them in a tuple. Passing a FnPtr visits its binder as a nested one.
    /// A replacer belongs to one binder and one Types interner.
    pub fn instantiate(&mut self, tys: &Types, value: TyId) -> TyId {
        self.fold_ty(tys, value, 0)
    }
}

impl<R, T> TypeFolder for BoundVarReplacer<R, T>
where R: FnMut(BoundVar) -> RegionId, T: FnMut(BoundTy) -> TyId {
    fn fold_ty(&mut self, tys: &Types, t: TyId, depth: DebruijnIndex) -> TyId {
        if !tys.has_vars_bound_at_or_above(t, depth) { return t; }
        match tys.kind(t) {
            TyKind::Bound(d, b) if *d == depth => {
                let replacement = *self.type_cache.entry(*b).or_insert_with(|| (self.types)(*b));
                tys.shift_in(replacement, depth)
            }
            TyKind::Bound(d, b) if *d > depth => tys.intern(TyKind::Bound(d - 1, *b)),
            _ => {
                if let Some(t) = self.folded.get(&(depth, t)) { return *t; }
                let result = super_fold_ty(tys, t, self, depth);
                self.folded.insert((depth, t), result);
                result
            }
        }
    }
    fn fold_region(&mut self, tys: &Types, r: RegionId, depth: DebruijnIndex) -> RegionId {
        match tys.region_kind(r) {
            RegionKind::ReBound(d, v) if d == depth => {
                let replacement = *self.region_cache.entry(v).or_insert_with(|| (self.regions)(v));
                match tys.region_kind(replacement) {
                    RegionKind::ReBound(d, v) => tys.intern_region(RegionKind::ReBound(
                        d.checked_add(depth).expect("bound region index overflow"), v)),
                    _ => replacement,
                }
            }
            RegionKind::ReBound(d, v) if d > depth => tys.intern_region(RegionKind::ReBound(d - 1, v)),
            _ => r,
        }
    }
}

impl Types {
    pub fn fold_with(&self, t: TyId, folder: &mut impl TypeFolder) -> TyId { folder.fold_ty(self, t, 0) }

    /// Introduce binders outside `t`, shifting only its escaping type/region vars.
    pub fn shift_in(&self, t: TyId, amount: u32) -> TyId {
        if amount == 0 { t } else { self.fold_with(t, &mut Shifter { amount, out: false }) }
    }

    /// rustc's `shift_vars` operation.
    pub fn shift_vars(&self, t: TyId, amount: u32) -> TyId { self.shift_in(t, amount) }

    /// Remove empty binder levels outside `t`. Panics if a variable refers to
    /// a removed level; use instantiation when those levels bind variables.
    pub fn shift_out(&self, t: TyId, amount: u32) -> TyId {
        if amount == 0 { t } else { self.fold_with(t, &mut Shifter { amount, out: true }) }
    }

    /// Instantiate one skipped binder's payload; nested binders remain intact.
    pub fn instantiate_bound_vars(&self, value: TyId, regions: impl FnMut(BoundVar) -> RegionId,
        types: impl FnMut(BoundTy) -> TyId) -> TyId {
        BoundVarReplacer::new(regions, types).instantiate(self, value)
    }

    /// Region-only instantiation, like rustc's instantiate_bound_regions.
    /// Panics if the removed binder also binds a type variable.
    pub fn instantiate_bound_regions(&self, value: TyId, regions: impl FnMut(BoundVar) -> RegionId) -> TyId {
        self.instantiate_bound_vars(value, regions, |b| panic!("unexpected bound type in region-only instantiation: {b:?}"))
    }

    /// Instantiate one skipped binder with universally quantified type and
    /// region placeholders. The caller allocates/passes the fresh universe.
    pub fn instantiate_binder_with_placeholders(&self, value: TyId, universe: UniverseIndex) -> TyId {
        self.instantiate_bound_vars(value,
            |var| self.intern_region(RegionKind::RePlaceholder { universe, var }),
            |b| self.intern(TyKind::Placeholder(PlaceholderType { universe, bound: b.var })))
    }
}
