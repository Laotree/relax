//! Persistent declaration state. Query/body caches and inference contexts are deliberately
//! absent. An empty signature OnceLock remains empty; checkpointing never asks for a body.
use super::*;
use crate::crate_image::{Codec, Decode};
use crate::collected::ImageMap;
use crate::solve::goal::*;

crate::collected_fields!(FnSigT, region_contract, generic_indices, bound_regions, params, ret,
    self_kind, n_generics, n_parent_generics, is_const, rustc_promotable, header,
    track_caller, legacy_const);
crate::collected_fields!(FieldT, name, ty, is_pub, vis_mod);
crate::collected_fields!(VariantT, def, name, shape, fields, disc);
crate::collected_fields!(AdtT, region_contract, generic_indices, flags, region_params,
    is_enum, is_union, n_generics, variants, repr_c, repr_int, repr_align, repr_packed,
    valid_start, valid_end, no_niche, param_maybe_unsized, ext_from, ext_conv);
crate::collected_id!(AdtFlags);
crate::collected_fields!(Destructor, did);
crate::collected_fields!(GenEnv, sized_params, regions, names, self_ty, trait_def, impl_def,
    impl_params, bounds, consts, opaque_owner);
crate::collected_fields!(OpaqueDecl, variances, region_contract, bounds, bindings, traits);
// Variances are a derived memo (publish_collected clears them): never part of an image.
impl Codec for SigParts {
    fn put(&self, w: &mut Vec<u8>) {
        self.sig.put(w); self.item_clauses.put(w); self.self_sized.put(w); self.bindings.put(w);
        self.const_reqs.put(w); self.trait_bounds.put(w); self.ty_bounds.put(w); self.const_hit.put(w);
        self.errors.put(w);
    }
    fn get(r: &mut Decode<'_>) -> Option<Self> {
        Some(Self { variances: Default::default(), sig: Codec::get(r)?, item_clauses: Codec::get(r)?,
            self_sized: Codec::get(r)?, bindings: Codec::get(r)?, const_reqs: Codec::get(r)?,
            trait_bounds: Codec::get(r)?, ty_bounds: Codec::get(r)?, const_hit: Codec::get(r)?,
            errors: Codec::get(r)? })
    }
}
crate::collected_fields!(outlives::RegionContract, callable_signatures, regions, predicates,
    caller_predicates, assumed_wf, type_names, own_types, self_ty, trait_types, trait_regions);
crate::collected_fields!(callable::CallableSignature, param, trait_def, signature);
crate::collected_fields!(crate::types::variance::GenericIndices, lifetimes, types_consts, consts);
crate::collected_enum!(crate::types::variance::V; 0 => Bi, 1 => Co, 2 => Contra, 3 => Inv);
crate::collected_enum!(outlives::OutlivesPredicate; 0 => Region(a,b), 1 => Type(t,r));
crate::collected_enum!(TyKey; 0 => Prim(p), 1 => Adt(d), 2 => Slice, 3 => Array,
    4 => Str, 5 => Ref, 6 => Ptr, 7 => Tuple, 8 => FnPtr, 9 => Dyn(d), 10 => Other);
impl crate::collected::ImageKey for TyKey {
    fn image_key(&self) -> u128 {
        let (tag, payload) = match *self {
            TyKey::Prim(p) => (0u128, p as u128), TyKey::Adt(d) => (1, d.0 as u128),
            TyKey::Slice => (2, 0), TyKey::Array => (3, 0), TyKey::Str => (4, 0), TyKey::Ref => (5, 0),
            TyKey::Ptr => (6, 0), TyKey::Tuple => (7, 0), TyKey::FnPtr => (8, 0),
            TyKey::Dyn(d) => (9, d.0 as u128), TyKey::Other => (10, 0),
        };
        tag << 32 | payload
    }
}
crate::collected_enum!(Term; 0 => Ty(t), 1 => Const(t));
crate::collected_fields!(TraitRef, def, args);
crate::collected_enum!(PredicatePolarity; 0 => Positive, 1 => Negative);
crate::collected_fields!(TraitPredicate, trait_ref, polarity);
crate::collected_enum!(AliasKind; 0 => Projection, 1 => Opaque, 2 => Inherent, 3 => Free);
crate::collected_fields!(AliasTerm, kind, def, args);
crate::collected_fields!(ProjectionPredicate, alias, term);
crate::collected_enum!(Clause; 0 => Trait(p), 1 => Projection(p), 2 => RegionOutlives(a,b),
    3 => TypeOutlives(t,r), 4 => WellFormed(t), 5 => ConstEvaluatable(t), 6 => ConstArgHasType(c,t));

/// Keep the schema next to the collector. Every field here is declaration state, as opposed
/// to a derived query memo. Adding collection state requires updating these lists.
macro_rules! fields {
    ($op:ident) => { $op!(lang_items, blanket_cache, async_fns, future_defs, opaques,
        const_values, const_requests, const_blocked, clone_trait, impl_projection_ready,
        copy_trait, errors); };
}
/// Declaration tables, read in place from the image (ImageMap): a warm boot decodes only
/// the entries its code asks for.
macro_rules! tables {
    ($op:ident) => { $op!(sigs, ctor_sigs, adts, adt_destructors, destructor_impls, const_tys,
        nominal_region_contracts, const_region_contracts, impl_self, impl_trait, impl_generics,
        inherent, trait_impls, impls_by_key, impl_trait_args, impl_trait_regions,
        impl_trait_bounds, impls_by_key_method, derived, derived_by_adt, trait_closure); };
}

impl Tcx {
    /// Invalidate declaration owners in the changed suffix, preserving the independent
    /// dependency graph and its type IDs. Derived query caches were never in the image.
    pub fn retain_collected_prefix(&mut self, first: usize) {
        let keep = |d: &DefId| (d.0 as usize) < first;
        let impls: Vec<_> = self.impl_self.keys().filter(|d| !keep(d)).copied().collect();
        self.uncollect_impls(&impls, false);
        self.inherent.retain(|_, v| !v.is_empty()); self.trait_impls.retain(|_, v| !v.is_empty());
        self.impls_by_key.retain(|_, v| !v.is_empty()); self.impls_by_key_method.retain(|_, v| !v.is_empty());
        let gone: Vec<_> = self.sigs.keys().chain(self.adts.keys()).chain(self.const_tys.keys())
            .chain(self.impl_self.keys()).chain(self.trait_closure.keys()).filter(|d| !keep(d)).copied().collect();
        self.invalidate_check(&gone);
        self.impl_trait_args.retain(|d, _| keep(d)); self.impl_trait_regions.retain(|d, _| keep(d));
        self.impl_trait_bounds.retain(|d, _| keep(d));
        self.nominal_region_contracts.retain(|d, _| keep(d)); self.const_region_contracts.retain(|d, _| keep(d));
        self.ctor_sigs.retain(|d, _| keep(d)); self.opaques.retain(|(d, _), _| keep(d));
        self.derived.retain(|(d, t), _| keep(d) && keep(t)); self.derived_by_adt.retain(|d, _| keep(d));
        self.adt_destructors.retain(|d, v| keep(d) && keep(&v.did));
        self.destructor_impls.retain(|d, v| keep(d) && keep(v));
        self.async_fns = self.async_fns.snapshot().into_iter().filter(|(d, _)| keep(d))
            .fold(Default::default(), |out, (d, v)| { out.insert(d, v); out });
        self.const_values = self.const_values.snapshot().into_iter().filter(|(d, _)| keep(d))
            .fold(Default::default(), |out, (d, v)| { out.insert(d, v); out });
        self.const_requests.get_mut().unwrap_or_else(|e| e.into_inner()).retain(keep);
        self.const_blocked.retain(keep);
        for d in &mut self.lang_items.items { if d.as_ref().is_some_and(|d| !keep(d)) { *d = None; } }
        self.lang_items.by_def.retain(|d, _| keep(d));
    }

    pub fn collect_collected_suffix(&mut self, prog: &Program, first: usize) {
        let defs: Vec<_> = (first..prog.defs.len()).map(|d| DefId(d as u32)).collect();
        self.collect_added(prog, &defs, true);
        for d in defs {
            if prog.def(d).kind == DefKind::Trait {
                let mut all = Vec::new(); let mut todo = vec![d];
                while let Some(x) = todo.pop() { if !all.contains(&x) { all.push(x); todo.extend(self.trait_supers(prog, x)); } }
                self.trait_closure.insert(d, all);
            }
        }
        self.orphan_check(&EvalCx::new(prog, TypingEnv::fully_monomorphized(), &EvalState::new()), prog);
        self.flush_errs();
        self.seal_collected_diagnostics();
        self.publish_collected();
    }

    pub fn verify_collected(&self, saved_prog: &Program, prog: &Program, rebuilt: &Self) {
        let mut a_keys: Vec<_> = self.sigs.keys().copied().collect(); a_keys.sort_by_key(|d| d.0);
        let mut b_keys: Vec<_> = rebuilt.sigs.keys().copied().collect(); b_keys.sort_by_key(|d| d.0);
        assert_eq!(a_keys, b_keys, "collected signature definitions differ");
        for d in a_keys {
            // Demand the same declarations on both sides, never their bodies.
            if self.sigs[&d].get().is_some() || rebuilt.sigs[&d].get().is_some() {
                let a = self.signature_parts(saved_prog, d);
                let b = rebuilt.signature_parts(prog, d);
                let encode = |p: Option<&SigParts>| {
                    let mut w = Vec::new();
                    p.is_some().put(&mut w);
                    if let Some(p) = p {
                        // Variance is a derived memo; collection leaves it lazy.
                        p.sig.put(&mut w); p.item_clauses.put(&mut w); p.self_sized.put(&mut w);
                        p.bindings.put(&mut w); p.const_reqs.put(&mut w); p.trait_bounds.put(&mut w);
                        p.ty_bounds.put(&mut w); p.const_hit.put(&mut w); p.errors.put(&mut w);
                    }
                    w
                };
                assert_eq!(self.tys.with_semantic_ids(|| encode(a)), rebuilt.tys.with_semantic_ids(|| encode(b)),
                    "collected signature differs: {}", prog.def_path(d));
            }
        }
        macro_rules! compare { ($($f:ident),+) => { $(
            assert!(self.tys.with_semantic_ids(|| crate::crate_image::encode(&self.$f)) ==
                rebuilt.tys.with_semantic_ids(|| crate::crate_image::encode(&rebuilt.$f)),
                "collected Tcx {} differs", stringify!($f));
        )+ }; }
        compare!(ctor_sigs, adts, lang_items, adt_destructors, destructor_impls, const_tys,
            nominal_region_contracts, const_region_contracts, impl_self, impl_trait,
            impl_generics, inherent, trait_impls, impls_by_key, impl_trait_args,
            impl_trait_regions, impl_trait_bounds, blanket_cache, impls_by_key_method,
            derived, derived_by_adt, trait_closure, clone_trait, impl_projection_ready, copy_trait);
        assert_eq!(self.collected_errors, rebuilt.collected_errors, "collected declaration diagnostics differ");
    }

    /// Only declaration diagnostics decide whether collection completed cleanly. Later
    /// lazy/speculative queries can report errors for unused items; these are not a failure
    /// of the collected graph. SigParts keeps its own diagnostics for subsequent readers.
    pub(super) fn seal_collected_diagnostics(&mut self) {
        let mut errors = self.errors.clone();
        errors.extend(self.err_sink.get_mut().unwrap_or_else(|e| e.into_inner()).iter().cloned());
        self.collected_errors = Some(errors);
    }

    pub fn collected_image(&self) -> Option<Vec<u8>> {
        self.collected_image_with(&|| false)
    }

    /// `stop`: asked between the tables; yes drops the image (None) -- the recorder yields the
    /// unit lock to a waiting main thread (relax-compiler cache/collected.rs).
    pub fn collected_image_with(&self, stop: &dyn Fn() -> bool) -> Option<Vec<u8>> {
        Some(self.collected_writer_with(stop)?.finish())
    }

    pub fn collected_writer_with(&self, stop: &dyn Fn() -> bool) -> Option<crate::image::Writer<'_>> {
        let errors = self.collected_errors.as_ref()?;
        if !errors.is_empty() || self.const_in_progress.len() != 0 { return None; }
        let mut w = Vec::new();
        2u32.put(&mut w);
        macro_rules! put_one {
            (errors) => { errors.put(&mut w) };
            ($f:ident) => { self.$f.put(&mut w) };
        }
        macro_rules! put { ($($f:ident),+) => { $(put_one!($f);)+ }; }
        fields!(put);
        // publish_collected's one pass over the signatures, done here instead of at restore
        (self.sigs.is_mapped() && self.image_const_hit
            || self.sigs.decoded_values().any(|cell| cell.get().is_some_and(|p| p.const_hit))).put(&mut w);
        let mut image = crate::image::Writer::default();
        image.add_bytes(0, w);
        if stop() { return None; }
        image.add_image(1, std::sync::Arc::new(self.tys.collected_writer()?));
        let mut id = 2;
        macro_rules! table { ($($f:ident),+) => { $(if stop() { return None; } self.$f.write_image(&mut image, &mut id);)+ }; }
        tables!(table);
        Some(image)
    }

    pub fn restore_collected(bytes: &'static [u8]) -> Option<Self> {
        let image = crate::image::Reader::new(bytes)?;
        let mut r = Decode::new(image.bytes(0, 0)?);
        if u32::get(&mut r)? != 2 { return None; }
        let mut t = Self::with_types(Types::restore_collected(image.bytes(1, 1)?)?);
        macro_rules! get { ($($f:ident),+) => { $(t.$f = Codec::get(&mut r)?;)+ }; }
        fields!(get);
        let pending = bool::get(&mut r)?;
        if !r.bytes.is_empty() { return None; }
        let (mut k, mut id) = (2, 2);
        macro_rules! table { ($($f:ident),+) => { $(t.$f = ImageMap::read_image(&image, &mut k, &mut id)?;)+ }; }
        tables!(table);
        if k != image.len() { return None; }
        // Epochs and derived variance/query memos belong to this process. Publish the
        // declaration input once, just as collect does, rather than persisting boot counts;
        // the image's signatures carry no variances and the const flag was computed when recorded.
        t.collected_errors = Some(t.errors.clone());
        t.image_const_hit = pending;
        t.publish_declarations(pending);
        *t.norm_ready.get_mut() = true;
        Some(t)
    }
}
