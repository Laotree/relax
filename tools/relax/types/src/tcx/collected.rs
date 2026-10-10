//! Persistent declaration state. Query/body caches and inference contexts are deliberately
//! absent. An empty signature OnceLock remains empty; checkpointing never asks for a body.
use super::*;
use crate::crate_image::{Codec, Decode};
use crate::collected::ImageMap;

crate::collected_fields!(FnSigT, region_contract, generic_indices, bound_regions, params, ret,
    self_kind, n_generics, n_parent_generics, is_const, rustc_promotable, header,
    track_caller, target_features, safe_target_features);
crate::collected_fields!(FieldT, name, ty, is_pub, vis_mod);
crate::collected_fields!(VariantT, def, name, shape, fields, discr);
crate::collected_fields!(AdtT, region_contract, generic_indices, flags, region_params,
    is_enum, is_union, n_generics, variants, repr_c, repr_int, repr_align, repr_packed,
    valid_start, valid_end, no_niche, param_maybe_unsized, ext_from, ext_conv);
crate::collected_id!(AdtFlags);
crate::collected_fields!(Destructor, did);
crate::collected_fields!(GenEnv, sized_params, regions, names, self_ty, trait_def, impl_def,
    impl_params, bounds, consts, opaque_owner);
crate::collected_fields!(OpaqueDecl, region_contract, bounds);
// Derived variance is rebuilt after declaration publication.
impl Codec for SigParts {
    fn put(&self, w: &mut Vec<u8>) {
        self.sig.put(w); self.self_sized.put(w); self.trait_bounds.put(w);
        self.ty_bounds.put(w); self.errors.put(w);
    }
    fn get(r: &mut Decode<'_>) -> Option<Self> {
        Some(Self { variances: Default::default(), sig: Codec::get(r)?, self_sized: Codec::get(r)?,
            trait_bounds: Codec::get(r)?, ty_bounds: Codec::get(r)?, errors: Codec::get(r)? })
    }
}
crate::collected_fields!(callable::CallableSignature, param, trait_def, signature);
crate::collected_fields!(outlives::RegionContract, callable_signatures, regions, predicates,
    caller_predicates, assumed_wf, type_names, own_types, self_ty, trait_types, trait_regions);

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
crate::collected_enum!(VariantDiscr; 0 => Explicit(d), 1 => Relative(n));
/// Keep the schema next to the collector. Every field here is declaration state, as opposed
/// to a derived query memo. Adding collection state requires updating these lists.
macro_rules! fields {
    ($op:ident) => { $op!(lang_items, async_fns, future_defs,
        opaques, copy_trait, errors); };
}
/// Declaration tables decoded only when demanded from the collected image.
macro_rules! tables {
    ($op:ident) => { $op!(sigs, ctor_sigs, adts, adt_destructors, destructor_impls,
        nominal_region_contracts, const_region_contracts, impl_self, impl_trait, impl_generics,
        inherent, trait_impls, impls_by_key, impl_trait_args, impl_trait_regions,
        impl_trait_bounds, trait_closure); };
}

impl Tcx {
    /// Invalidate declaration owners in the changed suffix, preserving the independent
    /// dependency graph and its type IDs. Derived query caches were never in the image.
    pub fn retain_collected_prefix(&mut self, first: usize) {
        let keep = |d: &DefId| (d.0 as usize) < first;
        let impls: Vec<_> = self.impl_self.keys().filter(|d| !keep(d)).copied().collect();
        self.uncollect_impls(&impls);
        self.inherent.retain(|_, v| !v.is_empty()); self.trait_impls.retain(|_, v| !v.is_empty());
        let consts = self.const_tys.snapshot();
        let gone: Vec<_> = self.sigs.keys().chain(self.adts.keys()).chain(consts.keys())
            .chain(self.impl_self.keys()).chain(self.trait_closure.keys()).filter(|d| !keep(d)).copied().collect();
        self.invalidate_check(&gone);
        self.impl_trait_args.retain(|d, _| keep(d)); self.impl_trait_regions.retain(|d, _| keep(d));
        self.impl_trait_bounds.retain(|d, _| keep(d));
        self.nominal_region_contracts.retain(|d, _| keep(d)); self.contracts_waiting.retain(|d| keep(d));
        self.const_region_contracts.retain(|d, _| keep(d));
        self.ctor_sigs.retain(|d, _| keep(d)); self.opaques.retain(|d, _| keep(d));
        self.adt_destructors.retain(|d, v| keep(d) && keep(&v.did));
        self.destructor_impls.retain(|d, v| keep(d) && keep(v));
        self.async_fns = self.async_fns.snapshot().into_iter().filter(|(d, _)| keep(d))
            .fold(Default::default(), |out, (d, v)| { out.insert(d, v); out });
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
        self.orphan_check(&EvalCx::new(prog, self, TypingEnv::fully_monomorphized(prog), &EvalState::new()), prog);
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
                        p.sig.put(&mut w); p.self_sized.put(&mut w);
                        p.trait_bounds.put(&mut w);
                        p.ty_bounds.put(&mut w); p.errors.put(&mut w);
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
            nominal_region_contracts, contracts_waiting, const_region_contracts, impl_self, impl_trait,
            impl_generics, inherent, trait_impls, impls_by_key, impl_trait_args,
            impl_trait_regions, impl_trait_bounds, trait_closure, copy_trait);
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
        if !errors.is_empty() { return None; }
        let mut w = Vec::new();
        4u32.put(&mut w);
        macro_rules! put_one {
            (errors) => { errors.put(&mut w) };
            ($f:ident) => { self.$f.put(&mut w) };
        }
        macro_rules! put { ($($f:ident),+) => { $(put_one!($f);)+ }; }
        fields!(put);
        let mut image = crate::image::Writer::default();
        image.add_bytes(0, w);
        if stop() { return None; }
        image.add_image(1, std::sync::Arc::new(self.tys.collected_writer()?));
        let mut id = 2;
        macro_rules! table { ($($f:ident),+) => { $(if stop() { return None; } self.$f.write_image(&mut image, &mut id);)+ }; }
        tables!(table);
        self.const_tys.write_image(&mut image, &mut id);
        self.contracts_waiting.write_image(&mut image, &mut id);
        Some(image)
    }

    pub fn restore_collected(bytes: &'static [u8], files: usize, crates: usize) -> Option<Self> {
        let image = crate::image::Reader::new(bytes)?;
        let mut r = Decode::new(image.bytes(0, 0)?);
        if u32::get(&mut r)? != 4 { return None; }
        let mut t = Self::with_types(Types::restore_collected(image.bytes(1, 1)?)?);
        macro_rules! get { ($($f:ident),+) => { $(t.$f = Codec::get(&mut r)?;)+ }; }
        fields!(get);
        if !r.bytes.is_empty() { return None; }
        let (mut k, mut id) = (2, 2);
        macro_rules! table { ($($f:ident),+) => { $(t.$f = ImageMap::read_image(&image, &mut k, &mut id)?;)+ }; }
        tables!(table);
        t.const_tys = ConstTypes::read_image(&image, &mut k, &mut id)?;
        t.contracts_waiting = crate::collected::ImageSet::read_image(&image, &mut k, &mut id)?;
        if k != image.len() { return None; }
        // Epochs and derived variance/query memos belong to this process. Re-publish the
        // declaration input once, just as collect does, rather than persisting boot counts.
        t.queries.register_files(files);
        t.queries.register_crates(crates);
        t.collected_errors = Some(t.errors.clone());
        t.publish_collected();
        Some(t)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn round38_collected_native_declarations_restore() {
        let session = std::sync::Arc::new(crate::Session::default());
        let root = std::env::temp_dir().join(format!("n01-collected-{}", std::process::id()));
        std::fs::create_dir_all(&root).unwrap();
        let source = root.join("lib.rs");
        std::fs::write(&source, r#"#![no_std]
            #[lang = "sized"] pub trait Sized {}
            pub struct Array<'a, const N: usize> { pub value: &'a [u8; N] }
            pub trait View { fn view<'a>(&'a self) -> impl Sized; }
            pub fn borrow<'a, const N: usize>(x: &'a Array<'a, N>) -> &'a [u8; N] { x.value }
            pub fn closure() { let _f = |x: u8| x; }
        "#).unwrap();
        let mut prog = Program::new(&session);
        prog.load_crate("fixture", source.to_str().unwrap(), 2021, crate::cfg::CfgSet::host(&session, &[]), vec![]).unwrap();
        prog.resolve_imports();
        assert!(prog.errors.is_empty(), "{:?}", prog.errors);
        let mut tcx = Tcx::new();
        tcx.collect(&prog);
        let def = DefId(prog.defs.iter().position(|d| prog.syms.str(d.name) == "borrow").unwrap() as u32);
        let _ = tcx.fn_item_sig(&prog, def).unwrap();
        let program_image = prog.collected_image().unwrap();
        let types_image = tcx.collected_image().unwrap();
        let pre = [crate::preload::PreCrate { rx_packages: Default::default(), name: "fixture".into(),
            root: source.to_str().unwrap().into(), edition: 2021, cfg: crate::cfg::CfgSet::host(&session, &[]),
            deps: vec![], proc_macro: false, image_deps: vec![], image_dep_names: vec![] }];
        let restored_prog = Program::restore_collected(&session, Box::leak(program_image.into_boxed_slice()), &pre,
            |_, _, _, meta| prog.file_paths.iter().position(|path| *path == meta.path).and_then(|i| crate::parser::parse_owned(&session, prog.files[i].src.to_vec(), 2021).ok())).unwrap();
        let restored_tcx = Tcx::restore_collected(Box::leak(types_image.into_boxed_slice()), restored_prog.files.len(), restored_prog.crates.len()).unwrap();
        prog.verify_collected(&restored_prog);
        tcx.verify_collected(&prog, &restored_prog, &restored_tcx);
        assert!(!restored_prog.node_id_to_def_id.is_empty());
        assert!(!restored_prog.impl_trait_in_trait_data.is_empty());
        assert_eq!(restored_tcx.fn_item_sig(&restored_prog, def).unwrap().bound_regions,
            tcx.fn_item_sig(&prog, def).unwrap().bound_regions);
        std::fs::remove_dir_all(root).unwrap();
    }
}

/// Mapped declaration types plus types published by shared anonymous-constant lowering.
#[derive(Default)]
pub struct ConstTypes {
    image: ImageMap<DefId, TyId>,
    added: crate::conc::ShardMap<DefId, TyId>,
}
impl ConstTypes {
    pub fn get(&self, d: &DefId) -> Option<TyId> { self.added.get(d).or_else(|| self.image.get(d).copied()) }
    pub fn insert(&self, d: DefId, t: TyId) { self.added.insert(d, t); }
    pub fn snapshot(&self) -> crate::fxhash::HashMap<DefId, TyId> {
        let mut out: crate::fxhash::HashMap<_, _> = self.image.iter().map(|(d, t)| (*d, *t)).collect();
        out.extend(self.added.snapshot()); out
    }
    pub fn retain(&mut self, mut f: impl FnMut(&DefId, &mut TyId) -> bool) {
        self.image.retain(|d, t| f(d, t)); self.added.retain(|d, t| f(d, t));
    }
    fn write_image(&self, image: &mut crate::image::Writer<'_>, id: &mut u32) {
        let table: ImageMap<_, _> = self.snapshot().into_iter().collect(); table.write_image(image, id);
    }
    fn read_image(image: &crate::image::Reader, k: &mut usize, id: &mut u32) -> Option<Self> {
        Some(Self { image: ImageMap::read_image(image, k, id)?, added: Default::default() })
    }
}
impl Codec for ConstTypes {
    fn put(&self, w: &mut Vec<u8>) { self.snapshot().put(w); }
    fn get(r: &mut Decode<'_>) -> Option<Self> { Some(Self { image: Codec::get(r)?, added: Default::default() }) }
}
