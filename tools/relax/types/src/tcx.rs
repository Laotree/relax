// ported from compiler/rustc_middle/src/ty/generics.rs @8d1a764
//! Type context: item signatures, ADT fields, the inherent/trait impl index and
//! lowering of syntactic types (`ast::Ty`) to interned types.

use crate::solve::SelectionResult;
use crate::ast::{self, GenericArg, GenericArgs, GenericParamKind, ItemKind, SegKind, TyId as AstTy, VariantData};
use crate::program::{DefId, DefKind, Prim, Program, Sym, NO_DEF};
use crate::types::{Abi, FnHeader, Safety, TyId, TyKind, Types};
use crate::fxhash::HashMap;
use crate::collected::ImageMap;
use crate::lang_items::{LangItem, LangItems};

mod collected;
mod regions;
pub mod outlives;
mod env;
pub use env::{ParamEnvId, DefiningOpaquesId};
use regions::RegionEnv;
use crate::types::{RegionId, RegionKind, RegionArgsId};

/// Key for impl lookup: the outer type constructor.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum TyKey {
    Prim(Prim),
    Adt(DefId),
    Slice,
    Array,
    Str,
    Ref,
    Ptr,
    Tuple,
    FnPtr,
    /// trait objects by principal trait (`impl Debug for dyn ActionTrait`)
    Dyn(DefId),
    Other,
}

#[derive(Clone)]
pub struct FnSigT {
    pub region_contract: outlives::RegionContract,
    pub generic_indices: crate::types::variance::GenericIndices,
    pub bound_regions: u32,
    pub params: Vec<TyId>,
    pub ret: TyId,
    /// 0 none, 1 self by value, 2 &self, 3 &mut self
    pub self_kind: u8,
    /// generic params of the owner impl/trait followed by the fn's own
    pub n_generics: u32,
    pub n_parent_generics: u32,
    pub is_const: bool,
    /// Explicit promotion permission, from the resolved definition's attribute.
    pub rustc_promotable: bool,
    pub header: FnHeader,
    /// `#[track_caller]`: takes the caller's `&'static Location` as an implicit last argument
    /// (rustc's implicit caller-location parameter)
    pub track_caller: bool,
    /// `#[rustc_legacy_const_generics(i, ..)]` (stdarch intrinsics): the value arguments at
    /// these positions are the fn's const generic args (rustc_ast_lowering
    /// lower_legacy_const_generics: `f(a, 6)` is `f::<6>(a)`)
    pub legacy_const: Vec<u32>,
}

#[derive(Clone)]
pub struct FieldT {
    pub name: Sym,
    pub ty: TyId,
    pub is_pub: bool,
    /// the module a restricted visibility (`pub`, `pub(in path)`, private) limits the
    /// field to; u32::MAX: `pub`
    pub vis_mod: u32,
}

#[derive(Clone)]
pub struct VariantT {
    pub def: DefId,
    pub name: Sym,
    /// 0 unit, 1 tuple, 2 struct
    pub shape: u8,
    pub fields: Vec<FieldT>,
    pub disc: i128,
}

#[derive(Clone)]
pub struct AdtT {
    pub region_contract: outlives::RegionContract,
    pub generic_indices: crate::types::variance::GenericIndices,
    pub flags: AdtFlags,
    pub region_params: RegionArgsId,
    pub is_enum: bool,
    pub is_union: bool,
    pub n_generics: u32,
    pub variants: Vec<VariantT>,
    pub repr_c: bool,
    pub repr_int: Option<Prim>,
    /// `#[repr(align(N))]`: N (0 = none)
    pub repr_align: u32,
    /// `#[repr(packed)]` / `#[repr(packed(N))]`: N (0 = none)
    pub repr_packed: u32,
    /// `#[rustc_layout_scalar_valid_range_start(N)]` / `_end(N)`: the valid range of the
    /// struct's scalar (NonNull, NonZero: 1..)
    pub valid_start: Option<u128>,
    pub valid_end: Option<u128>,
    /// `#[rustc_layout_no_niche]` (Relax's mark for UnsafeCell / UnsafePinned, which rustc
    /// special-cases): its niches are hidden
    pub no_niche: bool,
    /// per generic type param (lifetimes excluded): bounded `?Sized`
    pub param_maybe_unsized: Vec<bool>,
    /// Live sessions (M10, hotreload.md section 13): fields from this index on were added by
    /// edits and live in the value's extension block (layout.rs ext word); u32::MAX: none.
    /// Fields before it keep the slots of the struct's first version (a removed one stays as a
    /// dead slot, renamed so no code names it).
    pub ext_from: u32,
    /// Live sessions (M10): (added field, dead base slot) for a retyped scalar field -- running
    /// values get the old value converted (`as`, lossless widening) instead of the default.
    pub ext_conv: Vec<(u32, u32)>,
}

/// rustc_middle/src/ty/adt.rs:33,340. Identity flags come only from collected attributes.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct AdtFlags(pub u16);

impl AdtFlags {
    pub const IS_ENUM: Self = Self(1 << 0);
    pub const IS_UNION: Self = Self(1 << 1);
    pub const IS_STRUCT: Self = Self(1 << 2);
    pub const IS_BOX: Self = Self(1 << 3);
    pub const IS_PHANTOM_DATA: Self = Self(1 << 4);
    pub const IS_MANUALLY_DROP: Self = Self(1 << 5);
    pub const IS_UNSAFE_CELL: Self = Self(1 << 6);
    pub const IS_UNSAFE_PINNED: Self = Self(1 << 7);
    pub const HAS_CTOR: Self = Self(1 << 8);
    pub const IS_VARIANT_LIST_NON_EXHAUSTIVE: Self = Self(1 << 9);
    pub fn contains(self, flag: Self) -> bool { self.0 & flag.0 == flag.0 }
    fn insert(&mut self, flag: Self) { self.0 |= flag.0; }
}

impl AdtT {
    pub fn is_enum(&self) -> bool { self.flags.contains(AdtFlags::IS_ENUM) }
    pub fn is_union(&self) -> bool { self.flags.contains(AdtFlags::IS_UNION) }
    pub fn is_struct(&self) -> bool { self.flags.contains(AdtFlags::IS_STRUCT) }
    pub fn is_box(&self) -> bool { self.flags.contains(AdtFlags::IS_BOX) }
    pub fn is_phantom_data(&self) -> bool { self.flags.contains(AdtFlags::IS_PHANTOM_DATA) }
    pub fn is_manually_drop(&self) -> bool { self.flags.contains(AdtFlags::IS_MANUALLY_DROP) }
    pub fn is_unsafe_cell(&self) -> bool { self.flags.contains(AdtFlags::IS_UNSAFE_CELL) }
    pub fn is_unsafe_pinned(&self) -> bool { self.flags.contains(AdtFlags::IS_UNSAFE_PINNED) }
    pub fn has_ctor(&self) -> bool { self.flags.contains(AdtFlags::HAS_CTOR) }
    pub fn is_variant_list_non_exhaustive(&self) -> bool { self.flags.contains(AdtFlags::IS_VARIANT_LIST_NON_EXHAUSTIVE) }
}

/// The associated drop function, not the impl or an instantiated method selection.
/// rustc_middle/src/ty/util.rs:376.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Destructor { pub did: DefId }

/// Generic parameter environment while lowering types.
#[derive(Clone, Default)]
pub struct GenEnv {
    pub sized_params: Vec<u32>,
    pub regions: RegionEnv,
    pub names: Vec<Sym>,
    pub self_ty: Option<TyId>,
    /// inside a trait (its items see `Self::Assoc` as projections)
    pub trait_def: Option<DefId>,
    /// inside an impl (its items see `Self::Assoc` as the impl's own types)
    pub impl_def: Option<DefId>,
    /// `impl Trait` in argument position: (ast type id, the anonymous generic param it is)
    pub impl_params: Vec<(u32, u32)>,
    /// trait bounds on generic params (param index, file, trait path): `T::Assoc` lookups
    pub bounds: Vec<(u32, u32, ast::Path)>,
    /// const generic params: (param index, file, declared type)
    pub consts: Vec<(u32, u32, ast::TyId)>,
    /// lowering this fn's return type: `impl Trait` there is its opaque type
    pub opaque_owner: Option<DefId>,
}

/// The pseudo AST type id of an async fn's `impl Future` return type.
pub const ASYNC_OPAQUE: u32 = u32::MAX - 3;

/// Expression id of an async fn's body coroutine: ASYNC_FN_BODY | the body block's id.
pub const ASYNC_FN_BODY: u32 = 0x8000_0000;

/// A return-position `impl Trait` (rustc's opaque type item): its bounds over the defining fn's
/// generics, which is all its users see (rustc item_bounds).
#[derive(Clone, Default)]
pub struct OpaqueDecl {
    /// Capture variances in declaration order, supplied by opaque collection.
    pub variances: Option<(crate::types::variance::GenericIndices, Vec<crate::types::variance::V>)>,
    pub region_contract: outlives::RegionContract,
    /// (trait, its args without Self)
    pub bounds: Vec<(DefId, Vec<TyId>)>,
    /// `Assoc = T` bindings: (assoc type, its trait's args without Self, T)
    pub bindings: Vec<(DefId, Vec<TyId>, TyId)>,
    /// the bound traits with their supertraits
    pub traits: Vec<DefId>,
}

pub struct Tcx {
    pub tys: Types,
    envs: env::Envs,
    /// Immutable entries; each declaration is lowered once by its first reader.
    sigs: ImageMap<DefId, std::sync::OnceLock<Box<SigParts>>>,
    /// tuple constructors as fn items (fields to the ADT): apart from `sigs`, which names
    /// only fns (code asks `sigs` whether a def is a fn); FnDef paths read fn_item_sig
    pub ctor_sigs: ImageMap<DefId, FnSigT>,
    pub adts: ImageMap<DefId, AdtT>,
    pub lang_items: LangItems,
    pub(crate) variances: std::sync::OnceLock<HashMap<DefId, Vec<crate::types::variance::V>>>,
    adt_destructors: ImageMap<DefId, Destructor>,
    destructor_impls: ImageMap<DefId, DefId>,
    pub const_tys: ImageMap<DefId, TyId>,
    pub nominal_region_contracts: ImageMap<DefId, outlives::RegionContract>,
    pub const_region_contracts: ImageMap<DefId, outlives::RegionContract>,
    pub impl_self: ImageMap<DefId, TyId>,
    pub impl_trait: ImageMap<DefId, DefId>,
    pub impl_generics: ImageMap<DefId, GenEnv>,
    pub inherent: ImageMap<TyKey, Vec<DefId>>,
    pub trait_impls: ImageMap<(TyKey, DefId), Vec<DefId>>,
    /// trait impls by self type constructor
    pub impls_by_key: ImageMap<TyKey, Vec<DefId>>,
    /// trait arguments of each trait impl (in the impl's generic environment, defaults filled)
    pub impl_trait_args: ImageMap<DefId, Vec<TyId>>,
    pub impl_trait_regions: ImageMap<DefId, RegionArgsId>,
    pub alias_tys: crate::conc::MemoMap<(TypingEnv, DefId), TyId>,
    /// per impl: its trait bounds with their trait args (param, trait, args): inference through
    /// where-clauses once the impl is selected (`impl<A, B> PartialEq<Vec<B>> for Vec<A> where
    /// A: PartialEq<B>` fixes an integer literal B from A's impls, rustc's obligation processing)
    pub impl_trait_bounds: ImageMap<DefId, Vec<(u32, DefId, Vec<TyId>)>>,
    /// Definite selection answers, keyed by the full typing environment.
    selection_cache: crate::conc::MemoMap<(TypingEnv, DefId, TyId, Vec<TyId>), crate::solve::SelectionResult>,
    /// normalize() of concrete projections (rustc caches projection results too): without it a
    /// nested `<Chain<Chain<..>, ..> as Iterator>::Item` re-normalized each level's `A::Item`
    /// through its impl's bounds -- 2x work per level (19 chained iterators: seconds)
    norm_cache: crate::conc::MemoMap<(TypingEnv, TyId), TyId>,
    /// the norm_cache is used only once collection is complete (impl associated types known)
    norm_ready: std::sync::atomic::AtomicBool,
    blanket_cache: Option<std::sync::Arc<[DefId]>>,
    /// trait impls by (self type key, method name): the impls of traits that have an assoc fn
    /// of that name, in impl order (method probing asks only those; built in `collect`)
    impls_by_key_method: ImageMap<(TyKey, Sym), Vec<DefId>>,
    /// `core::<path>` items typeck asks for by path ("ops:Index:")
    pub core_path_items: crate::conc::MemoMap<String, Option<DefId>>,
    /// `trait_methods_for` answers for concrete receiver types, computed outside any impl
    /// selection in progress (depth-limited or cycle-cut answers are never stored)
    /// `#[derive(Trait)]` on an ADT: (adt, trait) -- the impl is compiler-generated
    pub derived: ImageMap<(DefId, DefId), ()>,
    /// the same, per ADT (method probes ask per receiver type)
    pub derived_by_adt: ImageMap<DefId, Vec<DefId>>,
    /// closures (file, expr, owner instance) that consume a capture (FnOnce kind, rustc
    /// upvar.rs): their state ends in one drop flag (u8) per capture, cleared when the body moves
    /// the capture out, and lives in memory. Per owner instance, as the capture analysis it comes
    /// from (closure_capture_types): one closure expression of a generic fn is Fn in one instance
    /// (`|c| c.set(v)` borrows a Copy `v`) and FnOnce in another (it moves a String).
    pub closure_once: crate::conc::MemoMap<(u32, u32, TyId), ()>,
    /// Minimum-capture types, kind and Copy proof by closure, owner and collection epoch.
    pub closure_capture_types: crate::conc::MemoMap<(u32, u32, TyId, u64), crate::upvar::ClosureCaptureTypes>,
    /// Wakes stalled goals after capture or opaque hidden-type publication.
    pub(crate) trait_input_revision: std::sync::atomic::AtomicU64,
    /// Per closure: legacy top-level field ownership (Body::capture_fields).
    pub closure_cap_fields: crate::conc::MemoMap<(u32, u32), Vec<Option<Vec<u32>>>>,
    /// async blocks / async fn bodies (file, expr; an async fn body is ASYNC_FN_BODY | block):
    /// closure types that are coroutines -- they implement Future<Output = sig's return>; their
    /// upvars end in the state word (rustc's discriminant: 0 unresumed, 1 returned, 2 poisoned,
    /// 3 + k suspended at point k), then the saved locals (coro_frames)
    pub coroutines: crate::conc::MemoMap<(u32, u32), ()>,
    /// a coroutine type's saved locals after its upvars: (end offset, alignment), made when its
    /// poll function is lowered (coroutine_transform)
    pub coro_frames: crate::conc::MemoMap<TyId, (u32, u32)>,
    /// a coroutine type's state shape (M5): a hash of its suspension points' saved slots and
    /// values (offset, size), its size and alignment -- a body edit whose new poll code has the
    /// same shape and the same code up to its last await may resume suspended values (reload.rs)
    pub coro_shapes: crate::conc::MemoMap<TyId, u64>,
    /// a coroutine poll slot's coroutine type (set when it is lowered)
    pub coro_slot_ty: crate::conc::MemoMap<u32, TyId>,
    /// async fns: their declared output type (the signature returns an opaque Future of it)
    pub async_fns: crate::conc::MemoMap<DefId, TyId>,
    /// core::future::Future and its Output (found on first use)
    future_defs: std::sync::OnceLock<Option<(DefId, DefId)>>,
    /// return-position `impl Trait` declarations by (defining fn, ast type id)
    pub opaques: crate::conc::ShardMap<(DefId, u32), OpaqueDecl>,
    /// hidden types of opaque type instances (Opaque(fn, ty, args) -> the defining body's type)
    pub opaque_hidden: crate::conc::MemoMap<TyId, TyId>,
    /// each trait with its supertraits, transitively (a trait object implements all of them)
    pub trait_closure: ImageMap<DefId, Vec<DefId>>,
    /// integer const items evaluated by running their initializer (CTFE through the JIT):
    /// array lengths and repeat counts that need a const fn (`SLICE.len()`)
    pub const_values: crate::conc::MemoMap<DefId, u128>,
    /// const items whose value a length needs and that have not been evaluated yet
    pub const_requests: std::sync::Mutex<Vec<DefId>>,
    pub queries: crate::type_queries::QueryCx,
    /// bumped whenever collected signatures / types change after the first collection
    /// (re-collection of items that waited for constants): bodies checked before are stale
    pub collect_epoch: std::sync::atomic::AtomicU64,
    /// generic fns' polymorphic bodies (tytemplate.rs), per (def, collect epoch); None: no template
    pub templates: crate::conc::MemoMap<(DefId, u64), Option<std::sync::Arc<crate::typeck::Body>>>,
    /// definitions with one instance checked (the second builds the template)
    pub template_seen: crate::conc::MemoMap<(DefId, u64), ()>,
    /// generic fns' bodies checked over their own params (identity args), per (def, collect
    /// epoch), for decisions an instance cannot make alone (typeck bound_method: which of two
    /// bounds a call goes through when the instance makes their self types equal)
    pub poly_bodies: crate::conc::MemoMap<(DefId, u64), std::sync::Arc<crate::typeck::Body>>,
    /// const items whose evaluation failed (not requested again)
    pub const_failed: crate::conc::MemoMap<DefId, ()>,
    /// const items being evaluated (their initializer is compiling / running)
    pub const_in_progress: crate::conc::ShardMap<DefId, ()>,
    /// items whose signature / declared type waits for a requested const (re-collected after)
    pub const_blocked: Vec<DefId>,
    pending_signature_consts: std::sync::atomic::AtomicBool,
    /// core::clone::Clone / core::marker::Copy (closures implement them structurally)
    pub clone_trait: Option<DefId>,
    /// Initial collection precedes projection matching in impl trait arguments.
    pub impl_projection_ready: bool,
    pub copy_trait: Option<DefId>,
    /// errors of signature collection and type lowering (moved here from `err_sink` when a
    /// collection step ends)
    pub errors: Vec<String>,
    /// errors reported through `&self` (type lowering may run on any thread)
    err_sink: std::sync::Mutex<Vec<String>>,
    // Diagnostics at the declaration checkpoint, before runtime/speculative queries.
    collected_errors: Option<Vec<String>>,
    /// a signature in the restored image waits for a const (publish_collected)
    image_const_hit: bool,
}

/// Asks for constant `d` to be evaluated (consteval): into this evaluation's capture while a
/// parallel collection step runs, else into the unit's queue.
pub fn request_const(cx: &crate::tcx::EvalCx<'_>, tcx: &Tcx, d: DefId) {
    let captured = match cx.state.requests.borrow_mut().as_mut() {
        Some(v) => {
            if !v.contains(&d) {
                v.push(d);
            }
            true
        }
        None => false,
    };
    if !captured {
        let mut r = tcx.const_requests.lock().unwrap_or_else(|e| e.into_inner());
        if !r.contains(&d) {
            r.push(d);
        }
    }
}

/// `f` over `items` on the boot's worker count (RELAX_JOBS), results in item order.
fn par_map<T: Sync, R: Send>(items: &[T], f: impl Fn(&T) -> R + Sync) -> Vec<R> where T: Copy {
    let jobs = crate::preload::jobs().min(items.len().max(1));
    if jobs < 2 {
        return items.iter().map(|x| f(x)).collect();
    }
    let next = std::sync::atomic::AtomicUsize::new(0);
    const CHUNK: usize = 64;
    let mut parts: Vec<(usize, Vec<R>)> = std::thread::scope(|sc| {
        let hs: Vec<_> = (0..jobs)
            .map(|_| {
                sc.spawn(|| {
                    let mut out = Vec::new();
                    loop {
                        let k = next.fetch_add(CHUNK, std::sync::atomic::Ordering::Relaxed);
                        if k >= items.len() {
                            break;
                        }
                        let end = (k + CHUNK).min(items.len());
                        out.push((k, items[k..end].iter().map(|x| f(x)).collect::<Vec<R>>()));
                    }
                    out
                })
            })
            .collect();
        hs.into_iter().flat_map(|h| h.join().unwrap()).collect()
    });
    parts.sort_by_key(|p| p.0);
    parts.into_iter().flat_map(|p| p.1).collect()
}

/// One impl header's collection (Tcx::impl_head_captured), recorded in impl order.
struct ImplHead {
    env: GenEnv,
    self_ty: TyId,
    /// None: inherent impl; Some(None): a trait path that did not resolve
    trait_: Option<Option<(DefId, Vec<TyId>)>>,
    errors: Vec<String>,
    const_reqs: Vec<DefId>,
    /// its lowering read the impl tables: recomputed in impl order after the earlier impls
    reads_impls: bool,
    trait_regions: RegionArgsId,
}

/// One ADT's collection, computed with `&self` (Tcx::adt_parts) and recorded by Tcx::apply_adt.
pub struct AdtParts {
    adt: Option<AdtT>,
    derived: Vec<DefId>,
    const_reqs: Vec<DefId>,
    const_hit: bool,
    errors: Vec<String>,
}

/// One complete function declaration, published atomically for all signature readers.
#[derive(Default)]
pub(crate) struct SigParts {
    pub(crate) variances: std::sync::OnceLock<Vec<crate::types::variance::V>>,
    sig: Option<FnSigT>,
    item_clauses: Vec<crate::solve::goal::Clause>,
    self_sized: bool,
    bindings: Vec<(u32, DefId, Vec<TyId>, TyId)>,
    const_reqs: Vec<DefId>,
    trait_bounds: Vec<(u32, DefId, Vec<TyId>)>,
    ty_bounds: Vec<(TyId, DefId, Vec<TyId>)>,
    const_hit: bool,
    errors: Vec<String>,
}

/// Stand-in impl id for a `#[derive]`d trait impl (no impl item exists).
pub const DERIVED_IMPL: DefId = DefId(u32::MAX - 2);

pub fn ty_key(tys: &Types, t: TyId) -> TyKey {
    match tys.kind(t) {
        TyKind::Bool => TyKey::Prim(Prim::Bool),
        TyKind::Char => TyKey::Prim(Prim::Char),
        TyKind::Int(p) | TyKind::Float(p) => TyKey::Prim(*p),
        TyKind::Str => TyKey::Str,
        TyKind::Adt(d, _, _) => TyKey::Adt(*d),
        TyKind::Slice(_) => TyKey::Slice,
        TyKind::Array(..) => TyKey::Array,
        TyKind::Ref(..) => TyKey::Ref,
        TyKind::Ptr(..) => TyKey::Ptr,
        TyKind::Tuple(_) => TyKey::Tuple,
        TyKind::FnPtr(..) => TyKey::FnPtr,
        TyKind::Dyn(d, ..) => TyKey::Dyn(*d),
        _ => TyKey::Other,
    }
}

impl Tcx {
    /// Memory report lines: the type interner and the shared memo tables typeck fills.
    pub fn mem_lines(&self) -> Vec<(String, u64)> {
        fn v<T>(x: &Vec<T>) -> usize {
            x.capacity() * std::mem::size_of::<T>()
        }
        let mut out = self.tys.mem_lines();
        let mut push = |name: &str, (n, b): (usize, usize)| out.push((format!("tcx {} ({})", name, n), b as u64));
        push("param envs", self.envs.mem_stats());
        push("selection_cache", self.selection_cache.mem_stats(|k, r| v(&k.3) + match r { crate::solve::SelectionResult::Ok(s) => v(&s.args) + v(&s.nested), _ => 0 }));
        push("norm_cache", self.norm_cache.mem_stats(|_, _| 0));
        push("alias_tys", self.alias_tys.mem_stats(|_, _| 0));
        push("core_path_items", self.core_path_items.mem_stats(|k, _| k.capacity()));
        push("closure_capture_types", self.closure_capture_types.mem_stats(|_, _| 0));
        push("closure_cap_fields", self.closure_cap_fields.mem_stats(|_, x| v(x)));
        push("opaque_hidden", self.opaque_hidden.mem_stats(|_, _| 0));
        push("template_seen", self.template_seen.mem_stats(|_, _| 0));
        push("templates (bodies)", self.templates.mem_stats(|_, b| b.as_ref().map_or(0, |b| std::mem::size_of::<crate::typeck::Body>() + b.heap_bytes())));
        push("poly_bodies (bodies)", self.poly_bodies.mem_stats(|_, b| std::mem::size_of::<crate::typeck::Body>() + b.heap_bytes()));
        out
    }

    pub fn new() -> Tcx { Self::with_types(Types::new()) }

    fn with_types(tys: Types) -> Tcx {
        Tcx {
            tys,
            envs: env::Envs::new(),
            sigs: Default::default(),
            ctor_sigs: Default::default(),
            adts: Default::default(),
            const_tys: Default::default(),
            nominal_region_contracts: Default::default(),
            const_region_contracts: Default::default(),
            impl_self: Default::default(),
            impl_trait: Default::default(),
            impl_generics: Default::default(),
            inherent: Default::default(),
            trait_impls: Default::default(),
            impls_by_key: Default::default(),
            impl_trait_args: Default::default(),
            impl_trait_regions: Default::default(),
            alias_tys: Default::default(),
            impl_trait_bounds: Default::default(),
            selection_cache: Default::default(),
            norm_cache: Default::default(),
            norm_ready: std::sync::atomic::AtomicBool::new(false),
            blanket_cache: None,
            impls_by_key_method: Default::default(),
            core_path_items: Default::default(),
            lang_items: Default::default(),
            variances: Default::default(),
            adt_destructors: Default::default(),
            destructor_impls: Default::default(),
            closure_once: Default::default(),
            closure_cap_fields: Default::default(),
            closure_capture_types: Default::default(),
            trait_input_revision: Default::default(),
            coroutines: crate::conc::MemoMap::with_bits(10),
            coro_frames: Default::default(),
            coro_shapes: Default::default(),
            coro_slot_ty: Default::default(),
            async_fns: crate::conc::MemoMap::with_bits(10),
            future_defs: Default::default(),
            derived: Default::default(),
            derived_by_adt: Default::default(),
            opaques: Default::default(),
            opaque_hidden: Default::default(),
            trait_closure: Default::default(),
            const_values: crate::conc::MemoMap::with_bits(10),
            const_requests: Default::default(),
            queries: crate::type_queries::QueryCx::new(),
            collect_epoch: Default::default(),
            templates: crate::conc::MemoMap::with_bits(14),
            template_seen: crate::conc::MemoMap::with_bits(14),
            poly_bodies: crate::conc::MemoMap::with_bits(8),
            const_failed: crate::conc::MemoMap::with_bits(10),
            const_in_progress: Default::default(),
            const_blocked: Vec::new(),
            pending_signature_consts: Default::default(),
            clone_trait: None,
            impl_projection_ready: false,
            copy_trait: None,
            errors: Vec::new(),
            err_sink: Default::default(),
            collected_errors: None,
            image_const_hit: false,
        }
    }

    /// The errors collected so far (signature collection, type lowering).
    /// Moves the errors reported through `&self` into `errors` (end of a collection step).
    fn flush_errs(&mut self) {
        let v = std::mem::take(self.err_sink.get_mut().unwrap_or_else(|e| e.into_inner()));
        self.errors.extend(v);
    }

    /// rustc's orphan rules (coherence/orphan.rs, RFC 2451) for every impl outside the std
    /// crates: an inherent impl only for a type of this crate (E0116; primitives E0390); an impl
    /// of a foreign trait only when one of `Self, T1..Tn` is a local type (through the
    /// fundamental `&`, `&mut`, `Box`, `Pin`) and no uncovered type parameter comes before it
    /// (E0210), else E0117.
    fn orphan_check(&self, cx: &crate::tcx::EvalCx<'_>, prog: &Program) {
        for im in &prog.impls {
            let krate = prog.def(im.def).krate;
            let kname = prog.syms.str(prog.crates[krate as usize].name);
            if matches!(kname, "core" | "alloc" | "std" | "proc_macro") {
                continue;
            }
            let Some(&st) = self.impl_self.get(&im.def) else { continue };
            // (a projection self type is checked as what it normalizes to)
            let st = if self.tys.has_assoc(st) { self.normalize(cx, prog, st) } else { st };
            let item = prog.files[im.file as usize].ast.item(im.item);
            let pos = item.lo;
            let is_trait_impl = matches!(&item.kind, crate::ast::ItemKind::Impl { trait_: Some(_), .. });
            // const generic params are no types (`impl<const N: usize> Trait<N, Local> for i32`)
            let consts: Vec<u32> = self.impl_generics.get(&im.def).map(|e| e.consts.iter().map(|c| c.0).collect()).unwrap_or_default();
            match self.impl_trait.get(&im.def) {
                // a trait impl whose trait did not resolve: reported there
                None if is_trait_impl => {}
                None => {
                    if self.orphan_local(prog, st, krate) {
                        continue;
                    }
                    let shown = crate::typeck::ty_to_string(false, prog, self, st);
                    if matches!(self.tys.kind(st), TyKind::Adt(..) | TyKind::Dyn(..)) {
                        self.err(cx, prog, im.file, pos, format!("E0116: cannot define inherent `impl` for a type outside of the crate where the type is defined (`{}`) -- define and implement a trait or a new type instead", shown));
                    } else {
                        self.err(cx, prog, im.file, pos, format!("E0390: cannot define inherent `impl` for primitive types (`{}`) -- use a trait instead", shown));
                    }
                }
                Some(&td) => {
                    if prog.def(td).krate == krate {
                        continue;
                    }
                    let mut tys = vec![st];
                    if let Some(a) = self.impl_trait_args.get(&im.def) {
                        tys.extend(a.iter().copied());
                    }
                    let mut verdict = Err(false);
                    for t in tys {
                        if self.orphan_local(prog, t, krate) {
                            verdict = Ok(());
                            break;
                        }
                        if self.orphan_uncovered(prog, t, &consts) {
                            verdict = Err(true);
                            break;
                        }
                    }
                    match verdict {
                        Ok(()) => {}
                        Err(true) => self.err(cx, prog, im.file, pos, format!("E0210: type parameter must be covered by another type when it appears before the first local type in an impl of `{}` -- implement it for a local type or a local wrapper", prog.def_path(td))),
                        Err(false) => self.err(cx, prog, im.file, pos, format!("E0117: only traits defined in the current crate can be implemented for types defined outside of the crate (`impl {} for {}`) -- implement it for a local type or a local wrapper", prog.def_path(td), crate::typeck::ty_to_string(false, prog, self, st))),
                    }
                }
            }
        }
    }

    /// A local type for the orphan rules: an ADT or trait object of crate `krate`, or one behind
    /// a fundamental type (`&`, `&mut`, `Box`, `Pin`).
    fn orphan_local(&self, prog: &Program, t: TyId, krate: u32) -> bool {
        match self.tys.kind(t) {
            TyKind::Adt(d, args, _) => {
                if prog.def(*d).krate == krate {
                    return true;
                }
                self.fundamental(prog, *d) && args.first().map_or(false, |a| self.orphan_local(prog, *a, krate))
            }
            TyKind::Dyn(td, ..) => prog.def(*td).krate == krate,
            TyKind::Ref(_, x, _) => self.orphan_local(prog, *x, krate),
            _ => false,
        }
    }

    /// `#[fundamental]` types: std's Box and Pin, and any type declared `#[fundamental]`.
    fn fundamental(&self, prog: &Program, d: DefId) -> bool {
        let k = prog.syms.str(prog.crates[prog.def(d).krate as usize].name);
        if matches!(prog.name(d), "Box" | "Pin") && matches!(k, "core" | "alloc" | "std") {
            return true;
        }
        let def = prog.def(d);
        let f = &prog.files[def.file as usize];
        f.ast.list(f.ast.item(def.item).attrs).iter().any(|a| a.toks.hi > a.toks.lo && f.tok_text(a.toks.lo) == "fundamental")
    }

    /// A type parameter not covered by a non-fundamental type (`T`, `&T`, `Box<T>`).
    fn orphan_uncovered(&self, prog: &Program, t: TyId, consts: &[u32]) -> bool {
        match self.tys.kind(t) {
            TyKind::Param(i) => !consts.contains(i),
            TyKind::Ref(_, x, _) => self.orphan_uncovered(prog, *x, consts),
            TyKind::Adt(d, args, _) => {
                self.fundamental(prog, *d) && args.first().map_or(false, |a| self.orphan_uncovered(prog, *a, consts))
            }
            _ => false,
        }
    }

    /// rustc_hir_analysis/src/hir_ty_lowering/mod.rs:3604 retains all header fields.
    fn lower_fn_header(&self, cx: &EvalCx<'_>, prog: &Program, file: u32, unsafe_: bool,
        abi: Option<Option<ast::Ident>>, c_variadic: bool) -> FnHeader {
        let abi = match abi {
            None => Abi::Rust,
            Some(None) => Abi::C,
            Some(Some(a)) => match Abi::from_name(prog.files[file as usize].text(a).trim_matches('"')) {
                Some(abi) => abi,
                None => {
                    self.err(cx, prog, file, a.lo, format!("unsupported function ABI {}", prog.files[file as usize].text(a)));
                    Abi::Rust
                }
            },
        };
        FnHeader { safety: if unsafe_ { Safety::Unsafe } else { Safety::Safe }, abi, c_variadic }
    }

    fn err(&self, cx: &crate::tcx::EvalCx<'_>, prog: &Program, file: u32, pos: u32, msg: String) {
        let m = prog.record_error(file, pos, "typeck", msg);
        if let Some(m) = match cx.state.errors.borrow_mut().as_mut() {
            Some(v) => {
                v.push(m);
                None
            }
            None => Some(m),
        } {
            self.err_sink.lock().unwrap_or_else(|e| e.into_inner()).push(m);
        }
    }

    /// Reports an already formatted error again (one taken out of a with_errors capture).
    pub fn reraise_error(&self, cx: &crate::tcx::EvalCx<'_>, m: String) {
        if let Some(m) = match cx.state.errors.borrow_mut().as_mut() {
            Some(v) => {
                v.push(m);
                None
            }
            None => Some(m),
        } {
            self.err_sink.lock().unwrap_or_else(|e| e.into_inner()).push(m);
        }
    }

    /// Errors reported so far by this evaluation's captured step (None: not capturing).
    /// Runs `f` with this evaluation's errors captured; returns its result and the errors.
    /// with_errors in two halves, for a caller that needs `&mut self` meanwhile: starts
    /// capturing and returns what was capturing before (give it back to `end_errors`).
    pub fn begin_errors(&self, cx: &crate::tcx::EvalCx<'_>) -> Option<Vec<String>> {
        cx.state.errors.replace(Some(Vec::new()))
    }

    /// Ends a begin_errors capture: the errors reported since.
    pub fn end_errors(&self, cx: &crate::tcx::EvalCx<'_>, outer: Option<Vec<String>>) -> Vec<String> {
        cx.state.errors.replace(outer).unwrap_or_default()
    }

    pub fn with_errors<R>(&self, cx: &crate::tcx::EvalCx<'_>, f: impl FnOnce() -> R) -> (R, Vec<String>) {
        let outer = cx.state.errors.replace(Some(Vec::new()));
        let r = f();
        let errors = cx.state.errors.replace(outer).unwrap_or_default();
        (r, errors)
    }

    fn captured_len(&self, cx: &crate::tcx::EvalCx<'_>) -> Option<usize> {
        cx.state.errors.borrow().as_ref().map(|v| v.len())
    }

    /// Q3 will split the collected-program input into item queries.
    pub fn publish_collected(&mut self) {
        self.variances.take();
        // signatures still in a restored image carry no variances, and their const flag was
        // recorded with the image
        let mut pending = self.sigs.is_mapped() && self.image_const_hit;
        for cell in self.sigs.decoded_values_mut() {
            if let Some(p) = cell.get_mut() {
                p.variances.take();
                pending |= p.const_hit;
            }
        }
        self.publish_declarations(pending);
    }

    /// The declaration input changed: `pending` tells whether a signature waits for a const.
    pub(crate) fn publish_declarations(&mut self, pending: bool) {
        *self.pending_signature_consts.get_mut() = pending;
        let epoch = self.collect_epoch.fetch_add(1, std::sync::atomic::Ordering::SeqCst) + 1;
        self.queries.collected(epoch);
    }

    /// Collects impls, ADTs and constants; registers functions for signature queries.
    pub fn collect(&mut self, prog: &Program) {
        let cx_state = crate::tcx::EvalState::new();
        let cx = &EvalCx::new(prog, TypingEnv::fully_monomorphized(), &cx_state);
        self.norm_ready.store(false, std::sync::atomic::Ordering::Release);
        self.norm_cache.clear();
        self.lang_items = LangItems::default();
        let mut defs = Vec::with_capacity(prog.defs.len());
        for i in 0..prog.defs.len() { defs.push(DefId(i as u32)); }
        self.lang_items.collect(prog, &defs, &mut self.errors);
        self.collect_all(cx, prog);
        self.collect_nominal_region_contracts(cx, prog, defs.iter().copied());
        self.collect_adt_destructors(prog);
        self.seal_collected_diagnostics();
        self.publish_collected();
        self.norm_ready.store(true, std::sync::atomic::Ordering::Release);
    }

    fn collect_all(&mut self, cx: &crate::tcx::EvalCx<'_>, prog: &Program) {
        let _mem = crate::memstat::tag(crate::memstat::Tag::Sigs);
        let t0 = std::time::Instant::now();
        // impls first: their self types key the index. Each impl's header is lowered in
        // parallel (`&self`), then recorded in impl order with its errors and constant
        // requests, as the sequential loop did.
        let idx: Vec<u32> = (0..prog.impls.len() as u32).collect();
        let heads = par_map(&idx, |ii| {
            let cx_state = crate::tcx::EvalState::new();
            let cx = &EvalCx::new(prog, TypingEnv::fully_monomorphized(), &cx_state);
            cx.state.par_impls.set(true);
            let h = self.impl_head_captured(cx, prog, *ii as usize);
            cx.state.par_impls.set(false);
            h
        });
        for (ii, h) in heads.into_iter().enumerate() {
            let h = match h {
                // a header that read the impl tables is lowered again now: with exactly the
                // impls before it recorded, as the sequential collection saw them
                Some(h) if h.reads_impls => match self.impl_head_captured(cx, prog, ii) {
                    Some(h) => h,
                    None => continue,
                },
                Some(h) => h,
                None => continue,
            };
            let im = &prog.impls[ii];
            self.err_sink.get_mut().unwrap_or_else(|e| e.into_inner()).extend(h.errors);
            {
                let r = self.const_requests.get_mut().unwrap_or_else(|e| e.into_inner());
                for cd in h.const_reqs {
                    if !r.contains(&cd) {
                        r.push(cd);
                    }
                }
            }
            let st = h.self_ty;
            self.impl_self.insert(im.def, st);
            let key = ty_key(&self.tys, st);
            match h.trait_ {
                None => {
                    self.inherent.entry(key).or_default().push(im.def);
                }
                Some(None) => {}
                Some(Some((td, targs))) => {
                    self.impl_trait.insert(im.def, td);
                    self.trait_impls.entry((key, td)).or_default().push(im.def);
                    self.impls_by_key.entry(key).or_default().push(im.def);
                    self.impl_trait_args.insert(im.def, targs);
                }
            }
            self.impl_trait_regions.insert(im.def, h.trait_regions);
            self.impl_generics.insert(im.def, h.env);
        }
        // trait args naming another impl's constant (`impl Tr<{ u64::BYTE_LEN }, 0> for X`,
        // the const coming from `impl Tr<8, 0> for u64`): with every header recorded now, those
        // left unevaluated are lowered once more (rustc evaluates them lazily, in any order)
        for ii in 0..prog.impls.len() {
            let d = prog.impls[ii].def;
            let bad = self.impl_trait_args.get(&d).map_or(false, |a| a.iter().any(|t| *t == self.tys.error));
            if !bad {
                continue;
            }
            if let Some(h) = self.impl_head_captured(cx, prog, ii) {
                if let Some(Some((td, targs))) = h.trait_ {
                    if self.impl_trait.get(&d) == Some(&td) && !targs.iter().any(|t| *t == self.tys.error) {
                        self.impl_trait_args.insert(d, targs);
                        self.impl_trait_regions.insert(d, h.trait_regions);
                    }
                }
            }
        }
        self.orphan_check(cx, prog);
        let t1 = std::time::Instant::now();
        for ii in 0..prog.impls.len() {
            let d = prog.impls[ii].def;
            self.resolve_impl_bounds(cx, d, prog);
        }
        let t1b = std::time::Instant::now();
        self.blanket_cache = Some(self.compute_blanket().into());
        self.impls_by_key_method.clear();
        for ii in 0..prog.impls.len() {
            let imp = prog.impls[ii].def;
            let td = match self.impl_trait.get(&imp) {
                Some(&td) => td,
                None => continue,
            };
            let key = match self.impl_self.get(&imp) {
                Some(&st) => ty_key(&self.tys, st),
                None => continue,
            };
            let mut names: Vec<Sym> = Vec::new();
            for &it in &prog.traits[prog.def(td).sub as usize] {
                let d = prog.def(it);
                if d.kind == DefKind::AssocFn && !names.contains(&d.name) {
                    names.push(d.name);
                }
            }
            for n in names {
                self.impls_by_key_method.entry((key, n)).or_default().push(imp);
            }
        }
        for di in 0..prog.defs.len() {
            let d = DefId(di as u32);
            if prog.def(d).kind == DefKind::Trait {
                match prog.def_path(d).as_str() {
                    "core::clone::Clone" => self.clone_trait = Some(d),
                    "core::marker::Copy" => self.copy_trait = Some(d),
                    _ => {}
                }
            }
        }
        for di in 0..prog.defs.len() {
            let d = DefId(di as u32);
            if prog.def(d).kind == DefKind::Trait {
                let mut all = Vec::new();
                let mut todo = vec![d];
                while let Some(x) = todo.pop() {
                    if !all.contains(&x) {
                        all.push(x);
                        todo.extend(self.trait_supers(prog, x));
                    }
                }
                self.trait_closure.insert(d, all);
            }
        }
        let t2 = std::time::Instant::now();
        let adts: Vec<DefId> = (0..prog.defs.len() as u32).map(DefId).filter(|d| matches!(prog.def(*d).kind, DefKind::Struct | DefKind::Enum | DefKind::Union)).collect();
        let parts = par_map(&adts, |d| self.adt_parts_captured(&EvalCx::new(prog, TypingEnv::fully_monomorphized(), &crate::tcx::EvalState::new()), prog, *d));
        for (d, p) in adts.into_iter().zip(parts) {
            self.apply_adt(d, p);
        }
        let t3 = std::time::Instant::now();
        // Allocate only the publication cells. Function declarations are lowered by
        // their first reader, after impl/ADT inputs are complete.
        for di in 0..prog.defs.len() {
            let d = DefId(di as u32);
            let def = prog.def(d);
            match def.kind {
                DefKind::Fn | DefKind::AssocFn | DefKind::ForeignFn => {
                    self.sigs.insert(d, Default::default());
                }
                DefKind::Const | DefKind::Static | DefKind::AssocConst | DefKind::ForeignStatic => self.collect_const(cx, prog, d),
                _ => {}
            }
        }
        if crate::preload::trace() {
            let t4 = std::time::Instant::now();
            let ms = |a: std::time::Instant, b: std::time::Instant| (b - a).as_secs_f64() * 1e3;
            eprintln!("boot-trace: signatures: impls {:.1}, impl bounds {:.1}, traits {:.1}, adts {:.1}, fn slots + consts {:.1} ms", ms(t0, t1), ms(t1, t1b), ms(t1b, t2), ms(t2, t3), ms(t3, t4));
        }
        self.flush_errs();
    }

    /// Hot reload: signatures, types and impl tables of defs a new file version added (the
    /// per-item steps of `collect`). Returns the errors they made.
    /// `own_crate`: the defs are a crate of their own added to the program (a run-time module).
    /// No cached answer about the program's types can change then -- the orphan rule keeps a new
    /// crate's impls to its own traits or its own types -- so the selection caches stay.
    pub fn collect_added(&mut self, prog: &Program, defs: &[DefId], own_crate: bool) -> Vec<String> {
        let cx_state = crate::tcx::EvalState::new();
        let cx = &EvalCx::new(prog, TypingEnv::fully_monomorphized(), &cx_state);
        // (new impls and associated types: projection answers may change)
        self.norm_ready.store(false, std::sync::atomic::Ordering::Release);
        self.norm_cache.clear();
        let r = self.collect_added_inner(cx, prog, defs, own_crate);
        self.publish_collected();
        self.norm_ready.store(true, std::sync::atomic::Ordering::Release);
        r
    }

    fn collect_added_inner(&mut self, cx: &crate::tcx::EvalCx<'_>, prog: &Program, defs: &[DefId], own_crate: bool) -> Vec<String> {
        // errors reported before this collection (body checks since the last one) are not its
        // errors: they go to `errors` first, and only this collection's are returned
        self.flush_errs();
        let n0 = self.errors.len();
        self.lang_items.collect(prog, defs, &mut self.errors);
        // method and impl selection answers may change with new impls or associated items
        if !own_crate {
            self.selection_cache.clear();
        }
        let mut impls_added = Vec::new();
        for &d in defs {
            if prog.def(d).kind != DefKind::Impl {
                continue;
            }
            let ii = prog.def(d).sub as usize;
            let h = match self.impl_head_captured(cx, prog, ii) {
                Some(h) => h,
                None => continue,
            };
            self.err_sink.get_mut().unwrap_or_else(|e| e.into_inner()).extend(h.errors);
            {
                let r = self.const_requests.get_mut().unwrap_or_else(|e| e.into_inner());
                for cd in h.const_reqs {
                    if !r.contains(&cd) {
                        r.push(cd);
                    }
                }
            }
            let st = h.self_ty;
            self.impl_self.insert(d, st);
            let key = ty_key(&self.tys, st);
            match h.trait_ {
                None => self.inherent.entry(key).or_default().push(d),
                Some(None) => {}
                Some(Some((td, targs))) => {
                    self.impl_trait.insert(d, td);
                    self.trait_impls.entry((key, td)).or_default().push(d);
                    self.impls_by_key.entry(key).or_default().push(d);
                    self.impl_trait_args.insert(d, targs);
                }
            }
            self.impl_trait_regions.insert(d, h.trait_regions);
            self.impl_generics.insert(d, h.env);
            impls_added.push(d);
        }
        for &d in &impls_added {
            self.resolve_impl_bounds(cx, d, prog);
        }
        if !impls_added.is_empty() {
            self.blanket_cache = Some(self.compute_blanket().into());
            for &imp in &impls_added {
                let (Some(&td), Some(&st)) = (self.impl_trait.get(&imp), self.impl_self.get(&imp)) else { continue };
                let key = ty_key(&self.tys, st);
                let mut names: Vec<Sym> = Vec::new();
                for &it in &prog.traits[prog.def(td).sub as usize] {
                    let dd = prog.def(it);
                    if dd.kind == DefKind::AssocFn && !names.contains(&dd.name) {
                        names.push(dd.name);
                    }
                }
                for n in names {
                    self.impls_by_key_method.entry((key, n)).or_default().push(imp);
                }
            }
        }
        let adts: Vec<DefId> = defs.iter().copied().filter(|d| matches!(prog.def(*d).kind, DefKind::Struct | DefKind::Enum | DefKind::Union)).collect();
        for d in adts {
            let p = self.adt_parts_captured(cx, prog, d);
            self.apply_adt(d, p);
        }
        for &d in defs {
            match prog.def(d).kind {
                DefKind::Fn | DefKind::AssocFn | DefKind::ForeignFn => {
                    self.sigs.insert(d, Default::default());
                }
                DefKind::Const | DefKind::Static | DefKind::AssocConst | DefKind::ForeignStatic => self.collect_const(cx, prog, d),
                _ => {}
            }
        }
        self.flush_errs();
        // A crate of its own (a run-time module): nothing in the program names its items, so
        // only its own contracts are new. A reload recomputes every contract (a changed trait,
        // alias or associated type feeds the contracts of the items that name it).
        if own_crate {
            self.collect_nominal_region_contracts(cx, prog, defs.iter().copied());
        } else {
            self.collect_nominal_region_contracts(cx, prog, (0..prog.defs.len() as u32).map(DefId));
        }
        self.collect_adt_destructors(prog);
        self.errors[n0..].to_vec()
    }

    /// Frees the cache tables collect_added / uncollect_impls retired. Safety: no reader may run
    /// (front-end write lock and unit lock held).
    pub unsafe fn reclaim_caches(&self) {
        self.selection_cache.reclaim();
        self.norm_cache.reclaim();
    }

    /// A single-writer check session discards answers tied to old bodies and definitions.
    pub fn invalidate_check(&mut self, gone: &[DefId]) {
        self.opaque_hidden.clear(); self.templates.clear(); self.poly_bodies.clear();
        self.alias_tys.clear(); self.const_failed.clear();
        self.selection_cache.clear(); self.norm_cache.clear();
        if gone.is_empty() { self.publish_collected(); return; }
        let gone: crate::fxhash::HashSet<_> = gone.iter().copied().collect();
        self.sigs.retain(|d, _| !gone.contains(d));
        self.adts.retain(|d, _| !gone.contains(d));
        self.ctor_sigs.retain(|d, _| !gone.contains(d));
        self.const_tys.retain(|d, _| !gone.contains(d));
        self.nominal_region_contracts.retain(|d, _| !gone.contains(d));
        self.const_region_contracts.retain(|d, _| !gone.contains(d));
        self.impl_self.retain(|d, _| !gone.contains(d));
        self.impl_trait.retain(|d, _| !gone.contains(d));
        self.impl_generics.retain(|d, _| !gone.contains(d));
        self.opaques.retain(|k, _| !gone.contains(&k.0));
        self.trait_closure.retain(|d, _| !gone.contains(d));
        self.derived.retain(|(d, t), _| !gone.contains(d) && !gone.contains(t));
        self.derived_by_adt.retain(|d, _| !gone.contains(d));
        self.publish_collected();
    }

    /// Ordinary bodies do not change impl selection or signatures. An opaque return
    /// type is the exception: its inferred hidden type participates in those answers.
    pub fn invalidate_check_bodies(&mut self, changed: &[DefId]) {
        let mut opaque = false;
        self.opaques.retain(|(d, _), _| { opaque |= changed.contains(d); true });
        if opaque {
            self.invalidate_check(&[]);
        } else {
            self.templates.clear(); self.poly_bodies.clear(); self.template_seen.clear();
        }
    }

    /// The metadata that collect_added does not need for hot code installation, but which
    /// a full checker must refresh after trait/item-set edits.
    pub fn collect_check(&mut self, prog: &Program, defs: &[DefId]) {
        self.collect_added(prog, defs, false);
        for &d in defs {
            let errors = self.signature_errors(prog, d).to_vec();
            self.errors.extend(errors);
            if prog.def(d).kind == DefKind::Trait {
                let mut all = Vec::new(); let mut todo = vec![d];
                while let Some(x) = todo.pop() { if !all.contains(&x) { all.push(x); todo.extend(self.trait_supers(prog, x)); } }
                self.trait_closure.insert(d, all);
            }
        }
        self.orphan_check(&EvalCx::new(prog, TypingEnv::fully_monomorphized(), &EvalState::new()), prog);
        self.flush_errs();
        self.publish_collected();
    }

    /// Hot reload: takes impls a refused version added out of the impl tables.
    /// `own_crate`: the impls of a run-time module being taken out; cached answers that name
    /// them are about the module's own types or traits, which nothing asks about again.
    pub fn uncollect_impls(&mut self, impls: &[DefId], own_crate: bool) {
        self.norm_cache.clear();
        if !own_crate {
            self.selection_cache.clear();
        }
        if impls.is_empty() {
            return;
        }
        // a set: every impl list of the program is filtered against them (a slice scan per
        // entry was 2% of a `relax check makepad-scope`)
        let impls: crate::fxhash::HashSet<DefId> = impls.iter().copied().collect();
        let impls = &impls;
        self.adt_destructors.retain(|adt, _| !self.destructor_impls.get(adt).is_some_and(|imp| impls.contains(imp)));
        self.destructor_impls.retain(|_, imp| !impls.contains(imp));
        for v in self.inherent.values_mut() {
            v.retain(|d| !impls.contains(d));
        }
        for v in self.trait_impls.values_mut() {
            v.retain(|d| !impls.contains(d));
        }
        for v in self.impls_by_key.values_mut() {
            v.retain(|d| !impls.contains(d));
        }
        for v in self.impls_by_key_method.values_mut() {
            v.retain(|d| !impls.contains(d));
        }
        self.blanket_cache = Some(self.compute_blanket().into());
        self.publish_collected();
    }

    /// rustc_hir_analysis/src/check/mod.rs:124; rustc_middle/src/ty/util.rs:376.
    /// E0120/E0367/E0366 applicability and coherence validation belong to T8.
    pub fn adt_destructor(&self, adt: DefId) -> Option<Destructor> {
        self.adt_destructors.get(&adt).copied()
    }

    fn collect_adt_destructors(&mut self, prog: &Program) {
        self.adt_destructors.clear();
        self.destructor_impls.clear();
        let Some(drop_trait) = self.lang_items.get(LangItem::Drop) else { return };
        for &adt in self.adts.keys() {
            let Some(impls) = self.trait_impls.get(&(TyKey::Adt(adt), drop_trait)) else { continue };
            for &imp in impls {
                let Some(&self_ty) = self.impl_self.get(&imp) else { continue };
                if !matches!(self.tys.kind(self_ty), TyKind::Adt(d, _, _) if *d == adt) { continue; }
                let data = &prog.impls[prog.def(imp).sub as usize];
                let Some(&did) = data.items.first() else { continue };
                if prog.def(did).kind == DefKind::AssocFn {
                    self.adt_destructors.insert(adt, Destructor { did });
                    self.destructor_impls.insert(adt, imp);
                }
            }
        }
    }

    /// Module scope used to resolve names inside an item.
    pub fn item_module(&self, prog: &Program, d: DefId) -> u32 {
        prog.def(d).scope
    }

    /// Generic environment of an item (impl/trait generics first, then the item's own).
    pub fn item_env(&self, prog: &Program, d: DefId) -> GenEnv {
        let def = prog.def(d);
        let mut env = GenEnv::default();
        if def.parent != NO_DEF {
            let pd = prog.def(def.parent);
            if pd.kind == DefKind::Impl {
                if let Some(e) = self.impl_generics.get(&def.parent) {
                    env = e.clone();
                }
            } else if pd.kind == DefKind::Trait {
                let ast = &prog.files[pd.file as usize].ast;
                if let ItemKind::Trait { generics, .. } = &ast.item(pd.item).kind {
                    // `Self` is param 0 inside traits
                    env.names.push(prog.syms.get("Self").unwrap_or(u32::MAX));
                    env.regions.next_param += 1;
                    push_generics(prog, pd.file, generics, &mut env);
                    env.self_ty = Some(self.tys.intern(TyKind::Param(0)));
                    env.trait_def = Some(def.parent);
                }
            }
        }
        let ast = &prog.files[def.file as usize].ast;
        let it = ast.item(def.item);
        match &it.kind {
            ItemKind::Fn(sig, _, _) => {
                let sig = ast.fn_sig(*sig);
                push_generics(prog, def.file, &sig.generics, &mut env);
                // each `impl Trait` in a parameter type is an anonymous generic param, also nested
                // in generic args, tuples, slices, arrays (`&mut Image2d<u8, impl AsMut<[u8]>>`;
                // rustc: synthetic params in order of appearance)
                fn apit(ast: &ast::Ast, t: ast::TyId, out: &mut Vec<ast::TyId>) {
                    match ast.ty(t) {
                        ast::Ty::Ref(_, _, x) | ast::Ty::Paren(x) | ast::Ty::Ptr(_, x) | ast::Ty::Slice(x) | ast::Ty::Array(x, _) => apit(ast, *x, out),
                        ast::Ty::Tuple(v) => ast.list(*v).iter().for_each(|x| apit(ast, *x, out)),
                        ast::Ty::ImplTrait(bs) => {
                            out.push(t);
                            // nested in its own bounds too (`impl IntoIterator<Item = impl Into<String>>`)
                            for b in ast.list(*bs) {
                                if let ast::Bound::Trait { path, .. } = b {
                                    for seg in ast.segs(path.segs) {
                                        if let Some(a) = ast.gargs(seg.args) {
                                            if let GenericArgs::Angle(v) = a {
                                                for g in ast.list(*v) {
                                                    if let GenericArg::Type(x) | GenericArg::Binding(_, _, x) = g {
                                                        apit(ast, *x, out);
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                        ast::Ty::Path(p) => {
                            for seg in ast.segs(p.segs) {
                                if let Some(a) = ast.gargs(seg.args) {
                                    if let GenericArgs::Angle(v) = a {
                                        for g in ast.list(*v) {
                                            match g {
                                                GenericArg::Type(x) | GenericArg::Binding(_, _, x) => apit(ast, *x, out),
                                                _ => {}
                                            }
                                        }
                                    }
                                }
                            }
                        }
                        _ => {}
                    }
                }
                let mut found = Vec::new();
                for p in ast.list(sig.params) {
                    apit(ast, p.ty, &mut found);
                }
                for t in found {
                    if let ast::Ty::ImplTrait(bs) = ast.ty(t) {
                        let pi = env.names.len() as u32;
                        env.impl_params.push((t.0, pi));
                        env.names.push(u32::MAX);
                        env.sized_params.push(pi);
                        // its bounds are the anonymous param's (`impl IntoIterator<Item =
                        // u32>` fixes `1..=3` to u32 like `I: IntoIterator<Item = u32>`)
                        for b in ast.list(*bs) {
                            if let ast::Bound::Trait { path, maybe, .. } = b {
                                if *maybe { env.sized_params.retain(|p| *p != pi); continue; }
                                env.bounds.push((pi, def.file, *path));
                            }
                        }
                    }
                }
            }
            ItemKind::Struct(g, _) | ItemKind::Enum(g, _) | ItemKind::Union(g, _) => push_generics(prog, def.file, g, &mut env),
            ItemKind::TypeAlias { generics, .. } => push_generics(prog, def.file, generics, &mut env),
            _ => {}
        }
        env.regions.enabled = false;
        env
    }

    /// One impl's header (generics, self type, trait and its args), with this evaluation's errors
    /// and constant requests captured; None for an item that is no impl.
    fn impl_head_captured(&self, cx: &crate::tcx::EvalCx<'_>, prog: &Program, ii: usize) -> Option<ImplHead> {
        let im = &prog.impls[ii];
        let ast = &prog.files[im.file as usize].ast;
        let (generics, trait_, self_ty) = match &ast.item(im.item).kind {
            ItemKind::Impl { generics, trait_, self_ty, .. } => (generics, trait_, *self_ty),
            _ => return None,
        };
        let outer = cx.state.errors.replace(Some(Vec::new()));
        let outer_req = cx.state.requests.replace(Some(Vec::new()));
        let read0 = cx.state.impl_read.replace(false);
        let mut env = GenEnv::default();
        env.regions.enabled = true;
        push_generics(prog, im.file, generics, &mut env);
        env.regions.impl_elision();
        env.impl_def = Some(im.def);
        let st = self.lower_ty(cx, prog, im.file, im.module, &env, self_ty);
        env.self_ty = Some(st);
        let trait_regions = trait_.as_ref().map(|p| self.lower_region_args(prog, im.file, im.module, &env, p)).unwrap_or(RegionArgsId::EMPTY);
        let tr = trait_.as_ref().map(|tp| {
            self.resolve_type_path_def(prog, im.file, im.module, tp).and_then(|td| {
                // `impl Struct<T> for Trait<T>`: the trait position names no trait (rustc E0404)
                let k = prog.def(td).kind;
                if matches!(k, DefKind::Struct | DefKind::Enum | DefKind::Union | DefKind::TypeAlias) {
                    let what = match k {
                        DefKind::Struct => "struct",
                        DefKind::Enum => "enum",
                        DefKind::Union => "union",
                        _ => "type alias",
                    };
                    self.err(cx, prog, im.file, tp.lo, format!("E0404: expected trait, found {} `{}`", what, prog.name(td)));
                    return None;
                }
                let explicit = self.lower_type_args_with_regions(cx, prog, im.file, im.module, &env, tp, trait_regions);
                Some((td, self.fill_trait_defaults(cx, prog, td, st, explicit)))
            })
        });
        env.regions.finish_impl_elision();
        let errors = cx.state.errors.replace(outer).unwrap_or_default();
        let const_reqs = cx.state.requests.replace(outer_req).unwrap_or_default();
        let reads_impls = cx.state.impl_read.replace(read0);
        Some(ImplHead { env, self_ty: st, trait_: tr, errors, const_reqs, reads_impls, trait_regions })
    }

    fn collect_adt(&mut self, cx: &crate::tcx::EvalCx<'_>, prog: &Program, d: DefId) {
        let p = self.adt_parts_captured(cx, prog, d);
        self.apply_adt(d, p);
    }

    /// adt_parts with this evaluation's errors and const waits captured into the result.
    /// A struct's definition collected again from its current text, not recorded (a live layout
    /// edit reconciles it with the running one first, reload.rs layout_edit): the ADT and errors.
    pub fn adt_fresh(&self, cx: &crate::tcx::EvalCx<'_>, prog: &Program, d: DefId) -> (Option<AdtT>, Vec<String>) {
        let p = self.adt_parts_captured(cx, prog, d);
        (p.adt, p.errors)
    }

    fn adt_parts_captured(&self, cx: &crate::tcx::EvalCx<'_>, prog: &Program, d: DefId) -> AdtParts {
        let mut parts = AdtParts { adt: None, derived: Vec::new(), const_reqs: Vec::new(), const_hit: false, errors: Vec::new() };
        cx.state.pending_const_hit.set(false);
        let outer = cx.state.errors.replace(Some(Vec::new()));
        let outer_req = cx.state.requests.replace(Some(Vec::new()));
        self.adt_parts(cx, prog, d, &mut parts);
        parts.errors = cx.state.errors.replace(outer).unwrap_or_default();
        parts.const_reqs = cx.state.requests.replace(outer_req).unwrap_or_default();
        parts.const_hit = cx.state.pending_const_hit.replace(false);
        parts
    }

    /// Records one ADT's collection (derives, const requests and errors in their order).
    fn apply_adt(&mut self, d: DefId, p: AdtParts) {
        self.variances.take();
        self.err_sink.get_mut().unwrap_or_else(|e| e.into_inner()).extend(p.errors);
        for td in p.derived {
            if self.derived.insert((d, td), ()).is_none() {
                self.derived_by_adt.entry(d).or_default().push(td);
            }
        }
        {
            let r = self.const_requests.get_mut().unwrap_or_else(|e| e.into_inner());
            for cd in p.const_reqs {
                if !r.contains(&cd) {
                    r.push(cd);
                }
            }
        }
        if let Some(adt) = p.adt {
            // a tuple constructor is a fn item (rustc: its own FnDef type with the ADT's args):
            // its signature, fields to the ADT
            if !adt.is_union {
                let n = adt.n_generics;
                let pargs: Vec<TyId> = (0..n).map(|i| self.tys.intern(TyKind::Param(i))).collect();
                let ret = self.tys.intern(TyKind::Adt(d, pargs, adt.region_params));
                for v in adt.variants.iter().filter(|v| v.shape == 1) {
                    self.ctor_sigs.insert(v.def, FnSigT {
                        region_contract: adt.region_contract.clone(),
                        generic_indices: adt.generic_indices.clone(),
                        bound_regions: 0,
                        params: v.fields.iter().map(|f| f.ty).collect(),
                        ret,
                        self_kind: 0,
                        n_generics: n,
                        n_parent_generics: if adt.is_enum { n } else { 0 },
                        is_const: false,
                        rustc_promotable: false,
                        header: FnHeader::RUST,
                        track_caller: false,
                        legacy_const: Vec::new(),
                    });
                }
            }
            self.adts.insert(d, adt);
        }
        if p.const_hit {
            self.const_blocked.push(d);
        }
    }

    fn adt_parts(&self, cx: &crate::tcx::EvalCx<'_>, prog: &Program, d: DefId, parts: &mut AdtParts) {
        let def = prog.def(d);
        let file = def.file;
        let module = self.item_module(prog, d);
        let mut env = self.item_env(prog, d);
        env.regions.enabled = true;
        let n_generics = env.names.len() as u32;
        let self_args: Vec<TyId> = {
            let mut v = Vec::new();
            for i in 0..n_generics {
                v.push(self.tys.intern(TyKind::Param(i)));
            }
            v
        };
        env.self_ty = Some(self.tys.intern(TyKind::Adt(d, self_args, env.regions.identity_args(&self.tys))));
        let ast = &prog.files[file as usize].ast;
        let it = ast.item(def.item);
        let mut repr_c = false;
        let mut repr_int = None;
        let (repr_align, repr_packed) = read_repr(prog, file, ast.list(it.attrs), &mut repr_c, &mut repr_int);
        // `#[derive(A, B)]`: std derives are generated by the compiler (DERIVED_IMPL)
        {
            let s2 = prog.macros.s2_fmt;
            let src = prog.src(file);
            for a in ast.list(it.attrs) {
                let (lo, hi) = (a.toks.lo as usize, a.toks.hi as usize);
                if hi <= lo || crate::cfg::tok_str(src, lo) != b"derive" {
                    continue;
                }
                for i in lo + 1..hi {
                    let name = std::str::from_utf8(crate::cfg::tok_str(src, i)).unwrap_or("");
                    if name.is_empty() || !name.chars().next().unwrap().is_ascii_alphabetic() {
                        continue;
                    }
                    // expanded into real impls by the parser (parser/derive.rs) on the S2 std
                    // Proc derives also expand to ordinary impls; recording a
                    // synthetic candidate duplicates their proof (rustc_expand/
                    // src/expand.rs:543-557).
                    if crate::macro_reg::has_derive(name) || (s2 && crate::parser::derive::EXPANDED.contains(&name)) {
                        continue;
                    }
                    if let Some(s) = prog.syms.get(name) {
                        if let Some(td) = prog.lookup_in_scope(module, s, true) {
                            if prog.def(td).kind == DefKind::Trait {
                                if !parts.derived.contains(&td) {
                                    parts.derived.push(td);
                                }
                            }
                        }
                    }
                }
            }
        }
        let (valid_start, valid_end, no_niche) = read_layout_attrs(prog, file, ast.list(it.attrs));
        let param_maybe_unsized = match &it.kind {
            ItemKind::Struct(g, _) | ItemKind::Enum(g, _) | ItemKind::Union(g, _) => maybe_unsized_params(prog, file, g),
            _ => Vec::new(),
        };
        let mut flags = match it.kind {
            ItemKind::Enum(..) => AdtFlags::IS_ENUM,
            ItemKind::Union(..) => AdtFlags::IS_UNION,
            _ => AdtFlags::IS_STRUCT,
        };
        if matches!(it.kind, ItemKind::Struct(_, VariantData::Unit | VariantData::Tuple(_))) {
            flags.insert(AdtFlags::HAS_CTOR);
        }
        if matches!(it.kind, ItemKind::Enum(..)) && crate::lang_items::has_attr(prog, file, ast.list(it.attrs), "non_exhaustive") {
            flags.insert(AdtFlags::IS_VARIANT_LIST_NON_EXHAUSTIVE);
        }
        if let Some(lang) = self.lang_items.by_def.get(&d) {
            let identity = match lang {
                LangItem::OwnedBox => AdtFlags::IS_BOX,
                LangItem::PhantomData => AdtFlags::IS_PHANTOM_DATA,
                LangItem::ManuallyDrop => AdtFlags::IS_MANUALLY_DROP,
                LangItem::UnsafeCell => AdtFlags::IS_UNSAFE_CELL,
                LangItem::UnsafePinned => AdtFlags::IS_UNSAFE_PINNED,
                _ => AdtFlags::default(),
            };
            flags.insert(identity);
        }
        let mut adt = AdtT { region_contract: self.region_contract(cx, prog, d, &env), generic_indices: crate::types::variance::GenericIndices::from_env(&env), flags, region_params: env.regions.identity_args(&self.tys), is_enum: false, is_union: false, n_generics, variants: Vec::new(), repr_c, repr_int, repr_align, repr_packed, valid_start, valid_end, no_niche, param_maybe_unsized, ext_from: u32::MAX, ext_conv: Vec::new() };
        match &it.kind {
            ItemKind::Struct(_, data) => {
                let (shape, fields) = self.lower_fields(cx, prog, file, module, &env, data);
                adt.variants.push(VariantT { def: d, name: def.name, shape, fields, disc: 0 });
            }
            ItemKind::Union(_, fields) => {
                adt.is_union = true;
                let (_, f) = self.lower_fields(cx, prog, file, module, &env, &VariantData::Struct(fields.clone()));
                adt.variants.push(VariantT { def: d, name: def.name, shape: 2, fields: f, disc: 0 });
            }
            ItemKind::Enum(_, vars) => {
                adt.is_enum = true;
                let mut next_disc: i128 = 0;
                let dty = repr_int.map(crate::types::Types::int_info).unwrap_or((8, true));
                for (vi, v) in ast.list(*vars).iter().enumerate() {
                    let (shape, fields) = self.lower_fields(cx, prog, file, module, &env, &v.data);
                    let disc = match v.disc {
                        Some(e) => match crate::consteval::eval_disc(prog, file, module, e, dty) {
                            Some(x) => x,
                            None => {
                                // anything else is evaluated by running it: the variant's
                                // discriminant const (parser enum_disc_consts), CTFE via the JIT;
                                // the enum is re-collected once it is known
                                let ename = prog.syms.str(def.name).to_string();
                                let cname = crate::parser::derive::disc_const_name(&ename, vi);
                                let cd = prog.syms.get(&cname).and_then(|s| prog.lookup_in_scope(module, s, false));
                                match cd {
                                    Some(cd) if self.const_values.contains_key(&cd) => {
                                        let v = self.const_values.get(&cd).unwrap_or(0) as i128;
                                        crate::consteval::wrap_disc(v, dty)
                                    }
                                    Some(cd) if !self.const_failed.contains(&cd) => {
                                        request_const(cx, self, cd);
                                        cx.state.pending_const_hit.set(true);
                                        next_disc
                                    }
                                    _ => {
                                        let (l, c) = prog.files[file as usize].line_col(prog.files[file as usize].ast.expr(e).lo);
                                        cx.state.errors.borrow_mut().get_or_insert_with(Vec::new).push(format!("{}:{}:{}: enum discriminant could not be evaluated -- see the constant's own error", prog.file_paths[file as usize], l, c));
                                        next_disc
                                    }
                                }
                            }
                        },
                        None => next_disc,
                    };
                    next_disc = disc + 1;
                    let vdef = prog.variants[def.sub as usize][vi];
                    adt.variants.push(VariantT { def: vdef, name: prog.def(vdef).name, shape, fields, disc });
                }
            }
            _ => {}
        }
        parts.adt = Some(adt);
    }

    fn lower_fields(&self, cx: &crate::tcx::EvalCx<'_>, prog: &Program, file: u32, module: u32, env: &GenEnv, data: &VariantData) -> (u8, Vec<FieldT>) {
        let mut out = Vec::new();
        let (shape, fields) = match data {
            VariantData::Unit => (0, None),
            VariantData::Tuple(f) => (1, Some(f)),
            VariantData::Struct(f) => (2, Some(f)),
        };
        if let Some(fs) = fields {
            for (i, f) in prog.files[file as usize].ast.list(*fs).iter().enumerate() {
                let ty = self.lower_ty(cx, prog, file, module, env, f.ty);
                let name = match f.name {
                    Some(n) => {
                        let s = prog.files[file as usize].text(n);
                        prog.syms.get(s).unwrap_or(u32::MAX)
                    }
                    None => i as u32 | 0x8000_0000,
                };
                let vis_mod = prog.vis_module(file, module, &f.vis).unwrap_or(u32::MAX);
                out.push(FieldT { name, ty, is_pub: !matches!(f.vis, ast::Vis::Private), vis_mod });
            }
        }
        (shape, out)
    }

    /// Re-collects the items blocked on consts that have been evaluated since.
    /// Returns whether a type definition changed (its layouts must be recomputed).
    pub fn has_blocked_consts(&self) -> bool {
        !self.const_blocked.is_empty() || self.pending_signature_consts.load(std::sync::atomic::Ordering::Acquire)
    }

    pub fn recollect_blocked(&mut self, prog: &Program) -> bool {
        let cx_state = crate::tcx::EvalState::new();
        let cx = &EvalCx::new(prog, TypingEnv::fully_monomorphized(), &cx_state);
        let mut blocked = std::mem::take(&mut self.const_blocked);
        if *self.pending_signature_consts.get_mut() {
            *self.pending_signature_consts.get_mut() = false;
            blocked.extend(self.sigs.iter().filter_map(|(&d, cell)| cell.get().filter(|p| p.const_hit).map(|_| d)));
        }
        if blocked.is_empty() { return false; }
        let mut adts = false;
        for d in blocked {
            match prog.def(d).kind {
                DefKind::Struct | DefKind::Enum | DefKind::Union => {
                    self.collect_adt(cx, prog, d);
                    adts = true;
                }
                DefKind::Fn | DefKind::AssocFn | DefKind::ForeignFn => {
                    // its return-position `impl Trait` bounds were recorded with the waiting
                    // length too (`impl Iterator<Item = [T; LEN]>`): lowered again
                    self.opaques.retain(|k, _| k.0 != d);
                    self.collect_sig(cx, prog, d)
                }
                DefKind::Const | DefKind::Static | DefKind::AssocConst | DefKind::ForeignStatic => self.collect_const(cx, prog, d),
                _ => {}
            }
        }
        self.flush_errs();
        self.publish_collected();
        adts
    }

    fn collect_sig(&mut self, _cx: &crate::tcx::EvalCx<'_>, prog: &Program, d: DefId) {
        self.sigs.insert(d, Default::default());
        self.fn_sig(prog, d);
    }

    /// sig_parts with this evaluation's errors and const waits captured into the result.
    fn sig_parts_captured(&self, cx: &crate::tcx::EvalCx<'_>, prog: &Program, d: DefId) -> SigParts {
        let mut parts = SigParts::default();
        cx.state.pending_const_hit.set(false);
        let outer = cx.state.errors.replace(Some(Vec::new()));
        let outer_req = cx.state.requests.replace(Some(Vec::new()));
        self.sig_parts(cx, prog, d, &mut parts);
        parts.errors = cx.state.errors.replace(outer).unwrap_or_default();
        parts.const_reqs = cx.state.requests.replace(outer_req).unwrap_or_default();
        parts.const_hit = cx.state.pending_const_hit.replace(false);
        parts
    }

    /// Publish a complete declaration under its own OnceLock. Readers of unrelated
    /// functions never contend, and an initialized read takes no lock.
    #[inline]
    pub(crate) fn signature_parts(&self, prog: &Program, d: DefId) -> Option<&SigParts> {
        let cell = self.sigs.get(&d)?;
        Some(match cell.get() {
            Some(parts) => parts,
            None => self.init_signature(prog, d, cell),
        })
    }

    #[cold]
    fn init_signature<'a>(&'a self, prog: &Program, d: DefId, cell: &'a std::sync::OnceLock<Box<SigParts>>) -> &'a SigParts {
        cell.get_or_init(|| {
            if crate::why::enabled() && prog.files.get(prog.def(d).file as usize)
                .and_then(|f| f.ast.items.get(prog.def(d).item.0 as usize)).is_some() {
                let cause = prog.why_def(d, "signature-demand");
                crate::why::event("item-demand", &cause.file, cause.line, &cause.symbol, None);
            }
            let _mem = crate::memstat::tag(crate::memstat::Tag::Sigs);
            let state = EvalState::new();
            let cx = EvalCx::new(prog, TypingEnv::fully_monomorphized(), &state);
            let mut parts = self.sig_parts_captured(&cx, prog, d);
            if parts.const_hit {
                self.pending_signature_consts.store(true, std::sync::atomic::Ordering::Release);
            }
            if !parts.const_reqs.is_empty() {
                let mut requests = self.const_requests.lock().unwrap_or_else(|e| e.into_inner());
                for cd in parts.const_reqs.drain(..) {
                    if !requests.contains(&cd) { requests.push(cd); }
                }
            }
            Box::new(parts)
        })
    }

    #[inline]
    /// Signatures computed with errors (a type in a module the lazy selection had skipped) are
    /// computed again on next use: the post-boot loader calls this after it loads modules.
    /// Only errored ones: a correct signature never changes when items are added.
    pub fn forget_error_signatures(&mut self) -> usize {
        let errored: Vec<DefId> = self.sigs.iter().filter(|(_, cell)| cell.get().is_some_and(|p| {
            !p.errors.is_empty() || p.sig.as_ref().is_some_and(|sig| sig.params.iter().any(|t| self.tys.has_error(*t)) || self.tys.has_error(sig.ret))
        })).map(|(d, _)| *d).collect();
        for d in &errored { self.sigs.insert(*d, std::sync::OnceLock::new()); }
        errored.len()
    }

    pub fn fn_sig(&self, prog: &Program, d: DefId) -> Option<&FnSigT> {
        self.signature_parts(prog, d)?.sig.as_ref()
    }

    /// Diagnostics belong to the declaration and are available to every checker,
    /// including readers that arrive after another worker initialized it.
    pub fn signature_errors(&self, prog: &Program, d: DefId) -> &[String] {
        self.signature_parts(prog, d).map_or(&[], |p| p.errors.as_slice())
    }

    /// A full check requests declarations without bodies too (foreign and trait
    /// methods). Runtime loading only requests the declarations it uses.
    pub fn check_signature_errors(&self, prog: &Program, krate: u32) -> Vec<String> {
        let mut errors = Vec::new();
        for (i, def) in prog.defs.iter().enumerate() {
            if def.krate == krate {
                errors.extend_from_slice(self.signature_errors(prog, DefId(i as u32)));
            }
        }
        errors
    }

    pub fn signature_count(&self) -> usize {
        self.sigs.values().filter(|cell| cell.get().is_some()).count()
    }

    pub fn signature_bytes(&self) -> usize {
        self.sigs.capacity() * (std::mem::size_of::<DefId>() + std::mem::size_of::<std::sync::OnceLock<Box<SigParts>>>() + 1)
            + self.signature_count() * std::mem::size_of::<SigParts>()
    }

    #[inline]
    pub fn item_clauses(&self, prog: &Program, d: DefId) -> Option<&Vec<crate::solve::goal::Clause>> {
        self.signature_parts(prog, d).map(|p| &p.item_clauses).filter(|v| !v.is_empty())
    }
    #[inline]
    pub fn fn_trait_bounds(&self, prog: &Program, d: DefId) -> Option<&Vec<(u32, DefId, Vec<TyId>)>> {
        self.signature_parts(prog, d).map(|p| &p.trait_bounds).filter(|v| !v.is_empty())
    }
    #[inline]
    pub fn fn_ty_bounds(&self, prog: &Program, d: DefId) -> Option<&Vec<(TyId, DefId, Vec<TyId>)>> {
        self.signature_parts(prog, d).map(|p| &p.ty_bounds).filter(|v| !v.is_empty())
    }
    #[inline]
    pub fn fn_bound_bindings(&self, prog: &Program, d: DefId) -> Option<&Vec<(u32, DefId, Vec<TyId>, TyId)>> {
        self.signature_parts(prog, d).map(|p| &p.bindings).filter(|v| !v.is_empty())
    }
    #[inline]
    pub fn self_sized_method(&self, prog: &Program, d: DefId) -> bool {
        self.signature_parts(prog, d).is_some_and(|p| p.self_sized)
    }

    #[cfg(test)]
    pub(crate) fn insert_test_signature(&mut self, d: DefId, sig: FnSigT) {
        self.sigs.insert(d, std::sync::OnceLock::from(Box::new(SigParts { sig: Some(sig), ..Default::default() })));
    }

    fn sig_parts(&self, cx: &crate::tcx::EvalCx<'_>, prog: &Program, d: DefId, parts: &mut SigParts) {
        let def = prog.def(d);
        let file = def.file;
        let module = self.item_module(prog, d);
        let mut env = self.item_env(prog, d);
        let n_parent = match prog.def(def.parent).kind {
            DefKind::Impl => self.impl_generics.get(&def.parent).map_or(0, |e| e.names.len() as u32),
            DefKind::Trait => 1 + self.trait_generic_count(prog, def.parent) as u32,
            _ => 0,
        };
        let ast = &prog.files[file as usize].ast;
        let sig = match &ast.item(def.item).kind {
            ItemKind::Fn(s, _, _) => ast.fn_sig(*s),
            _ => return,
        };
        self.fn_region_env(cx, prog, file, module, &mut env, sig, d);
        let mut params = Vec::new();
        let mut region_uses = Vec::new();
        let mut self_kind = 0;
        if let Some(sp) = &sig.self_param {
            env.regions.start_parameter();
            let st = env.self_ty.unwrap_or(self.tys.error);
            let t = match sp {
                ast::SelfParam::Value(_) => {
                    self_kind = 1;
                    st
                }
                ast::SelfParam::Ref(lt, m) => {
                    self_kind = if *m { 3 } else { 2 };
                    self.tys.intern(TyKind::Ref(*m, st, env.regions.resolve(&self.tys, prog, file, *lt)))
                }
                ast::SelfParam::Typed(_, t) => {
                    self_kind = 1;
                    let lt = self.lower_ty(cx, prog, file, module, &env, *t);
                    if let TyKind::Ref(m, _, _) = self.tys.kind(lt) {
                        self_kind = if *m { 3 } else { 2 };
                    }
                    lt
                }
            };
            params.push(t);
            region_uses.push(env.regions.parameter_uses());
        }
        for p in ast.list(sig.params) {
            env.regions.start_parameter();
            params.push(self.lower_ty(cx, prog, file, module, &env, p.ty));
            region_uses.push(env.regions.parameter_uses());
        }
        let self_regions = self.self_elision_regions(prog, file, module, &env, sig.self_param.as_ref(), &params);
        self.output_region_env(&mut env, &params, self_regions, &region_uses);
        let bound_regions = env.regions.bound_count();
        let ret = match sig.ret {
            Some(r) => {
                let mut renv = env.clone();
                renv.opaque_owner = Some(d);
                self.lower_ty(cx, prog, file, module, &renv, r)
            }
            None => self.tys.unit,
        };
        // `async fn f() -> T` returns `impl Future<Output = T>` (rustc's async fn desugaring;
        // the hidden type is the body's coroutine)
        let ret = if sig.asyncness { self.async_opaque(prog, d, ret, env.names.len()) } else { ret };
        let mut callable_signatures = Vec::new();
        parts.item_clauses = self.collect_item_clauses(cx, prog, file, module, &env, &sig.generics, n_parent, &mut callable_signatures);
        // Associated items inherit their parent's predicates, including callable
        // Output equalities (rustc_middle/src/ty/generics.rs:431-441 @8d1a764).
        let parent = prog.def(def.parent);
        if matches!(parent.kind, DefKind::Impl | DefKind::Trait) {
            let parent_ast = &prog.files[parent.file as usize].ast;
            let (generics, offset) = match &parent_ast.item(parent.item).kind {
                ItemKind::Impl { generics, .. } => (generics, 0),
                ItemKind::Trait { generics, .. } => (generics, 1),
                _ => unreachable!(),
            };
            let mut parent_env = env.clone();
            parent_env.impl_params.clear();
            parts.item_clauses.extend(self.collect_item_clauses(cx, prog, parent.file, module, &parent_env, generics, offset, &mut callable_signatures));
        }
        let mut tb = Vec::new();
        for (pi, bfile, path) in env.bounds.clone() {
            if let Some(td) = self.resolve_type_path_def(prog, bfile, module, &path) {
                if pi == 0 && n_parent > 0 && prog.name(td) == "Sized" && prog.def(def.parent).kind == DefKind::Trait {
                    parts.self_sized = true;
                }
                if prog.def(td).kind != DefKind::Trait {
                    continue;
                }
                let targs = self.lower_generic_args(cx, prog, bfile, module, &env, &path);
                // (default trait args filled: `D: OverlayEdgeData` is OverlayEdgeData<ShapeCountBoolean>,
                // as the signature's `D::Store` projection spells it, and a binding's projection too)
                let p = self.tys.intern(TyKind::Param(pi));
                let targs = self.fill_trait_defaults(cx, prog, td, p, targs);
                // `I: IntoIterator<Item = D>`: the binding determines D from I at calls
                let bast = &prog.files[bfile as usize].ast;
                if let Some(GenericArgs::Angle(v)) = bast.segs(path.segs).last().and_then(|l| bast.gargs(l.args)) {
                    for g in bast.list(*v) {
                        if let GenericArg::Binding(n, _, ty) = g {
                            let f = &prog.files[bfile as usize];
                            let sym = prog.syms.get(f.text(*n)).unwrap_or(u32::MAX);
                            if let Some(ad) = self.trait_assoc(prog, td, sym) {
                                let pat = self.lower_ty(cx, prog, bfile, module, &env, *ty);
                                parts.bindings.push((pi, ad, targs.clone(), pat));
                            }
                        }
                    }
                }
                tb.push((pi, td, targs));
            }
        }
        // a trait's method has the trait's own predicate `Self: Trait<P..>` (rustc
        // predicates_of a trait item): a call `From::from(5)` / `T::from(x)` selects the impl
        // through it, fixing the trait args from the unique applicable impl
        if prog.def(def.parent).kind == DefKind::Trait {
            let nt = self.trait_generic_count(prog, def.parent) as u32;
            let targs: Vec<TyId> = (1..=nt).map(|i| self.tys.intern(TyKind::Param(i))).collect();
            if !targs.is_empty() {
                tb.push((0, def.parent, targs));
            }
        }
        if let Some(sized) = self.lang_items.get(LangItem::Sized) {
            for &pi in &env.sized_params { tb.push((pi, sized, Vec::new())); }
        }
        parts.trait_bounds = tb;
        // where-clauses on a type that is not one of the params (rustc predicates_of)
        let mut tyb = Vec::new();
        let f = &prog.files[file as usize];
        // (and the enclosing impl's: `impl<A: Array> SmallVec<A> where A::Item: Clone`)
        let impl_where: &[ast::WherePred] = if prog.def(def.parent).kind == DefKind::Impl {
            let im = &prog.impls[prog.def(def.parent).sub as usize];
            match &prog.files[im.file as usize].ast.item(im.item).kind {
                ItemKind::Impl { generics, .. } if im.file == file => f.ast.list(generics.where_),
                _ => &[],
            }
        } else {
            &[]
        };
        for w in f.ast.list(sig.generics.where_).iter().chain(impl_where.iter()) {
            if let ast::WherePred::Bound { ty, bounds, .. } = w {
                let simple = match f.ast.ty(*ty) {
                    ast::Ty::Path(p) => p.qself.is_none() && p.segs.len() == 1 && f.ast.segs(p.segs)[0].args.is_none(),
                    _ => false,
                };
                if simple {
                    continue;
                }
                let mut tds = Vec::new();
                for b in f.ast.list(*bounds) {
                    if let ast::Bound::Trait { path, maybe: false, .. } = b {
                        if let Some(td) = self.resolve_type_path_def(prog, file, module, path) {
                            if prog.def(td).kind == DefKind::Trait {
                                tds.push((td, path));
                            }
                        }
                    }
                }
                if tds.is_empty() {
                    continue;
                }
                // a self type Relax cannot lower here (`M::Item` through a where-clause
                // supertrait) only loses this inference aid: its errors are not the program's
                let nerr = self.captured_len(cx).unwrap_or(0);
                let st = self.lower_ty(cx, prog, file, module, &env, *ty);
                if st == self.tys.error || self.captured_len(cx).unwrap_or(0) != nerr {
                    {
                        if let Some(v) = cx.state.errors.borrow_mut().as_mut() {
                            v.truncate(nerr);
                        }
                     };
                    continue;
                }
                for (td, path) in tds {
                    let targs = self.lower_generic_args(cx, prog, file, module, &env, path);
                    tyb.push((st, td, targs));
                }
            }
        }
        parts.ty_bounds = tyb;
        let header = self.lower_fn_header(cx, prog, file, sig.unsafe_, sig.abi, sig.variadic);
        let mut region_contract = self.region_contract(cx, prog, d, &env);
        region_contract.callable_signatures = callable_signatures;
        parts.sig = Some(FnSigT {
                region_contract, generic_indices: crate::types::variance::GenericIndices::from_env(&env),
                bound_regions,
                params,
                ret,
                self_kind,
                n_generics: env.names.len() as u32,
                n_parent_generics: n_parent,
                is_const: sig.konst,
                rustc_promotable: sig.konst && ast.list(ast.item(def.item).attrs).iter().any(|a| {
                    a.toks.hi > a.toks.lo && crate::cfg::tok_str(prog.src(file), a.toks.lo as usize) == b"rustc_promotable"
                }),
                header,
                track_caller: {
                    let has = |d2: DefId| {
                        let dd = prog.def(d2);
                        let src = prog.src(dd.file);
                        prog.files[dd.file as usize].ast.list(prog.files[dd.file as usize].ast.item(dd.item).attrs).iter().any(|a| a.toks.hi > a.toks.lo && crate::cfg::tok_str(src, a.toks.lo as usize) == b"track_caller")
                    };
                    // (an `extern "C"` fn cannot take the implicit argument: C calls it); a trait
                    // method declared #[track_caller] makes its impls' methods tracked too (rustc
                    // codegen_fn_attrs inherits the attribute from the trait item)
                    !header.abi.is_c_like()
                        && (has(d)
                            || (prog.def(def.parent).kind == DefKind::Impl
                                && self.impl_trait.get(&def.parent).map_or(false, |td| prog.traits[prog.def(*td).sub as usize].iter().any(|&m| prog.def(m).name == def.name && prog.def(m).kind == DefKind::AssocFn && has(m)))))
                },
                legacy_const: {
                    let src = prog.src(file);
                    let mut v = Vec::new();
                    for a in ast.list(ast.item(def.item).attrs) {
                        if a.toks.hi > a.toks.lo && crate::cfg::tok_str(src, a.toks.lo as usize) == b"rustc_legacy_const_generics" {
                            for i in a.toks.lo + 1..a.toks.hi {
                                if let Some(n) = std::str::from_utf8(crate::cfg::tok_str(src, i as usize)).ok().and_then(|t| t.parse::<u32>().ok()) {
                                    v.push(n);
                                }
                            }
                        }
                    }
                    v
                },
        });
    }

    /// Fn-family bounds on an item's generic params (inline, `where`, and `impl Fn(..)`).
    fn collect_item_clauses(&self, cx: &crate::tcx::EvalCx<'_>, prog: &Program, file: u32, module: u32, env: &GenEnv, generics: &ast::Generics, n_parent: u32, callable_signatures: &mut Vec<callable::CallableSignature>) -> Vec<crate::solve::goal::Clause> {
        let ast = &prog.files[file as usize].ast;
        let f = &prog.files[file as usize];
        let mut pending: Vec<(u32, &ast::Bound, ast::List<ast::GenericParam>)> = Vec::new();
        let mut k = n_parent;
        for gp in ast.list(generics.params) {
            match &gp.kind {
                GenericParamKind::Type(bs, _) => {
                    for b in ast.list(*bs) {
                        pending.push((k, b, ast::List::new(0, 0)));
                    }
                    k += 1;
                }
                GenericParamKind::Const(..) => k += 1,
                GenericParamKind::Lifetime(_) => {}
            }
        }
        for w in ast.list(generics.where_) {
            if let ast::WherePred::Bound { ty, bounds, hrtb } = w {
                if let ast::Ty::Path(p) = ast.ty(*ty) {
                    if p.segs.len() == 1 && prog.files[file as usize].ast.segs(p.segs)[0].args.is_none() {
                        let name = prog.syms.get(f.text(prog.files[file as usize].ast.segs(p.segs)[0].name)).unwrap_or(u32::MAX - 1);
                        if let Some(i) = env.names.iter().rposition(|n| *n == name) {
                            if i as u32 >= n_parent {
                                for b in ast.list(*bounds) {
                                    pending.push((i as u32, b, *hrtb));
                                }
                            }
                        }
                    }
                }
            }
        }
        for &(t, i) in &env.impl_params {
            if let ast::Ty::ImplTrait(bs) = ast.ty(ast::TyId(t)) {
                for b in ast.list(*bs) {
                    pending.push((i, b, ast::List::new(0, 0)));
                }
            }
        }
        let mut out = Vec::new();
        for (i, b, where_hrtb) in pending {
            if let ast::Bound::Trait { path, hrtb, .. } = b {
                if let Some(last) = prog.files[file as usize].ast.segs(path.segs).last() {
                    let n = f.text(last.name);
                    let is_async = matches!(n, "AsyncFn" | "AsyncFnMut" | "AsyncFnOnce");
                    if n == "Fn" || n == "FnMut" || n == "FnOnce" || is_async {
                        if let Some(a) = ast.gargs(last.args) {
                            if let GenericArgs::Paren(ps, r) = a {
                                let fp = ast::FnPtr { hrtb: *hrtb, unsafe_: false, abi: None, params: *ps, ret: *r, variadic: false };
                                let bound = self.lower_fn_bound_pointer(cx, prog, file, module, env, &fp, where_hrtb);
                                if let Some(trait_def) = self.resolve_type_path_def(prog, file, module, path) {
                                    self.push_callable_clauses(&mut out, i, trait_def, bound);
                                    callable_signatures.push(callable::CallableSignature { param: i, trait_def, signature: bound });
                                }
                            }
                        }
                    } else if let Some(td) = self.resolve_type_path_def(prog, file, module, path) {
                        // a trait whose supertrait is Fn sugar (`F: KeyFn<T, K>` with
                        // `trait KeyFn<T, K>: Fn(&T) -> K`): that signature (rustc elaborates the
                        // bound to its supertraits; closures passed for F are typed by it)
                        if prog.def(td).kind == DefKind::Trait && !matches!(n, "Fn" | "FnMut" | "FnOnce") {
                            let targs = self.lower_generic_args(cx, prog, file, module, env, path);
                            let p = self.tys.intern(TyKind::Param(i));
                            for (sd, sa) in self.trait_super_refs_of(cx, prog, td, p, &targs) {
                                if matches!(prog.name(sd), "Fn" | "FnMut" | "FnOnce") {
                                    if let Some(TyKind::Tuple(ps)) = sa.first().map(|t| self.tys.kind(*t)) {
                                        if let Some(output) = self.callable_output(sd) {
                                            let mut args = vec![p]; args.extend_from_slice(&sa);
                                            let projection = self.tys.intern(TyKind::Assoc(output, args, RegionArgsId::EMPTY));
                                            for (lhs, ret) in self.trait_super_bindings(cx, prog, td, p, &targs) {
                                                if lhs == projection {
                                                    let sig = self.tys.intern(TyKind::FnPtr(ps.clone(), ret, FnHeader::RUST, 0));
                                                    self.push_callable_clauses(&mut out, i, sd, sig);
                                                    callable_signatures.push(callable::CallableSignature { param: i, trait_def: sd, signature: sig });
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        out
    }

    fn collect_const(&mut self, cx: &crate::tcx::EvalCx<'_>, prog: &Program, d: DefId) {
        let def = prog.def(d);
        let file = def.file;
        let module = self.item_module(prog, d);
        let mut env = self.item_env(prog, d);
        env.regions.enabled = true;
        env.regions.static_elision = env.regions.names.is_empty();
        let ast = &prog.files[file as usize].ast;
        let t = match &ast.item(def.item).kind {
            ItemKind::Const(Some(t), _) => *t,
            ItemKind::Static(_, t, _) => *t,
            _ => return,
        };
        cx.state.pending_const_hit.set(false);
        let ty = self.lower_ty(cx, prog, file, module, &env, t);
        if cx.state.pending_const_hit.replace(false) {
            self.const_blocked.push(d);
        }
        self.const_region_contracts.insert(d, self.region_contract(cx, prog, d, &env));
        self.const_tys.insert(d, ty);
    }

    // ------------------------------------------------------------ type lowering

    pub fn lower_ty(&self, cx: &crate::tcx::EvalCx<'_>, prog: &Program, file: u32, module: u32, env: &GenEnv, t: AstTy) -> TyId {
        let ast = &prog.files[file as usize].ast;
        match ast.ty(t) {
            ast::Ty::Tuple(v) => {
                let mut out = Vec::new();
                for x in ast.list(*v) {
                    out.push(self.lower_ty(cx, prog, file, module, env, *x));
                }
                self.tys.intern(TyKind::Tuple(out))
            }
            ast::Ty::Paren(x) => self.lower_ty(cx, prog, file, module, env, *x),
            ast::Ty::Never => self.tys.never,
            ast::Ty::Ref(lt, m, x) => {
                let r = env.regions.resolve(&self.tys, prog, file, *lt);
                env.regions.record_reference(file, t, r);
                let mut inner_env = env.clone();
                inner_env.regions.object_default = Some(r);
                let inner = self.lower_ty(cx, prog, file, module, &inner_env, *x);
                self.tys.intern(TyKind::Ref(*m, inner, r))
            }
            ast::Ty::Ptr(m, x) => {
                let inner = self.lower_ty(cx, prog, file, module, env, *x);
                self.tys.intern(TyKind::Ptr(*m, inner))
            }
            ast::Ty::Slice(x) => {
                let inner = self.lower_ty(cx, prog, file, module, env, *x);
                self.tys.intern(TyKind::Slice(inner))
            }
            ast::Ty::Array(x, n) => {
                let inner = self.lower_ty(cx, prog, file, module, env, *x);
                // `[T; _]`: an inferred length, a variable in a body (typeck
                // replace_errors_with_vars); the error length marks it
                if is_infer_len(ast, *n) {
                    return self.tys.mk_array(inner, self.tys.error);
                }
                // a constant, or a const generic param (`[T; N]`: rustc's ty::Const param)
                cx.state.const_wait.set(false);
                let lt = self.const_arg(cx, prog, file, module, env, *n);
                if lt == self.tys.error && cx.state.const_wait.get() {
                    // waits for a const evaluated by running it: the item is re-collected then
                    cx.state.pending_const_hit.set(true);
                    return self.tys.error;
                }
                if lt == self.tys.error {
                    let lo = ast.expr(*n).lo;
                    self.err(cx, prog, file, lo, "array length must be a constant".to_string());
                    // an unknown length is an error type: a 0-length stand-in silently gave
                    // structs a wrong layout
                    return self.tys.error;
                }
                // `[u8; N]` with `const N: u64`: an array length is a usize (rustc E0308 "the
                // constant `N` is not of type `usize`")
                if let TyKind::Param(i) = self.tys.kind(lt).clone() {
                    if let Some(&(_, cfile, cty)) = env.consts.iter().find(|c| c.0 == i) {
                        let cast = &prog.files[cfile as usize].ast;
                        if let ast::Ty::Path(cp) = cast.ty(cty) {
                            if cp.qself.is_none() && cp.segs.len() == 1 {
                                let tn = prog.files[cfile as usize].text(cast.segs(cp.segs)[0].name);
                                if crate::program::PRIMS.iter().any(|(pn, _)| *pn == tn) && tn != "usize" {
                                    let lo = ast.expr(*n).lo;
                                    let pn = env.names.get(i as usize).map_or(String::new(), |s| prog.syms.str(*s).to_string());
                                    self.err(cx, prog, file, lo, format!("E0308: the constant `{}` is not of type `usize` (it is `{}`)", pn, tn));
                                    return self.tys.error;
                                }
                            }
                        }
                    }
                }
                self.tys.mk_array(inner, lt)
            }
            ast::Ty::Fn(f) => self.lower_fn_pointer(cx, prog, file, module, env, ast.fn_ptr(*f)),
            ast::Ty::Infer => self.tys.error,
            ast::Ty::Path(p) => self.lower_path_ty(cx, prog, file, module, env, p),
            ast::Ty::DynTrait(bounds, _) => self.lower_dyn(cx, prog, file, module, env, ast.list(*bounds), 0),
            ast::Ty::ImplTrait(_) if env.impl_params.iter().any(|x| x.0 == t.0) => {
                let i = env.impl_params.iter().find(|x| x.0 == t.0).unwrap().1;
                self.tys.intern(TyKind::Param(i))
            }
            ast::Ty::ImplTrait(bs) if env.opaque_owner.is_some() => self.lower_opaque(cx, prog, file, module, env, t, ast.list(*bs)),
            ast::Ty::Mac(m) => {
                let lo = m.path.lo;
                let name = prog.files[file as usize].ast.segs(m.path.segs).last().map(|sg| prog.files[file as usize].text(sg.name).to_string()).unwrap_or_default();
                self.err(cx, prog, file, lo, format!("type macro `{}!` is not expanded here", name));
                self.tys.error
            }
            ast::Ty::ImplTrait(_) => {
                self.err(cx, prog, file, 0, "`impl Trait` in this position is not supported".to_string());
                self.tys.error
            }
            _ => {
                self.err(cx, prog, file, 0, "unsupported type".to_string());
                self.tys.error
            }
        }
    }

    /// Return-position `impl Bounds` of `env.opaque_owner`: Opaque(fn, ty, the fn's generics as
    /// args), its bounds recorded once (rustc: an opaque type item whose generics are the fn's,
    /// collect::item_bounds). `Assoc = impl X` bindings nest further opaques.
    fn lower_opaque(&self, cx: &crate::tcx::EvalCx<'_>, prog: &Program, file: u32, module: u32, env: &GenEnv, t: AstTy, bs: &[ast::Bound]) -> TyId {
        let owner = env.opaque_owner.unwrap();
        let args: Vec<TyId> = (0..env.names.len() as u32).map(|i| self.tys.intern(TyKind::Param(i))).collect();
        let me = self.tys.intern(TyKind::Opaque(owner, t.0, args, crate::types::RegionArgsId::EMPTY));
        if self.opaques.contains_key(&(owner, t.0)) {
            return me;
        }
        self.opaques.insert((owner, t.0), OpaqueDecl::default());
        let f = &prog.files[file as usize];
        let mut decl = OpaqueDecl::default();
        decl.region_contract = self.region_contract(cx,prog,owner,env);
        if !bs.iter().any(|b| matches!(b, ast::Bound::Trait { maybe: true, .. })) {
            if let Some(sized) = self.lang_items.get(LangItem::Sized) { decl.bounds.push((sized, Vec::new())); decl.traits.push(sized); }
        }
        for b in bs {
            let path = match b {
                ast::Bound::Trait { path, maybe: false, .. } => path,
                _ => continue,
            };
            let td = match self.resolve_type_path_def(prog, file, module, path) {
                Some(d) if prog.def(d).kind == DefKind::Trait => d,
                _ => continue,
            };
            let last = f.ast.segs(path.segs).last();
            if let Some(GenericArgs::Paren(ps, r)) = last.and_then(|l| f.ast.gargs(l.args)) {
                let pts: Vec<TyId> = f.ast.list(*ps).iter().map(|x| self.lower_ty(cx, prog, file, module, env, *x)).collect();
                let rt = match r {
                    Some(r) => self.lower_ty(cx, prog, file, module, env, *r),
                    None => self.tys.unit,
                };
                let args = vec![self.tys.intern(TyKind::Tuple(pts))];
                if let Some(output) = self.callable_output(td) { decl.bindings.push((output, args.clone(), rt)); }
                decl.bounds.push((td, args));
            } else {
                let explicit = self.lower_generic_args(cx, prog, file, module, env, path);
                let targs = self.fill_trait_defaults(cx, prog, td, me, explicit);
                if let Some(GenericArgs::Angle(v)) = last.and_then(|l| f.ast.gargs(l.args)) {
                    for g in f.ast.list(*v) {
                        if let GenericArg::Binding(n, _, ty) = g {
                            let sym = prog.syms.get(f.text(*n)).unwrap_or(u32::MAX);
                            if let Some(ad) = self.trait_assoc(prog, td, sym) {
                                let bt = self.lower_ty(cx, prog, file, module, env, *ty);
                                let ta = if prog.def(ad).parent == td { targs.clone() } else { Vec::new() };
                                decl.bindings.push((ad, ta, bt));
                            }
                        }
                    }
                }
                decl.bounds.push((td, targs));
            }
            let mut todo = vec![td];
            while let Some(x) = todo.pop() {
                if !decl.traits.contains(&x) {
                    decl.traits.push(x);
                    todo.extend(self.trait_supers(prog, x));
                }
            }
        }
        self.opaques.insert((owner, t.0), decl);
        me
    }

    /// core::future::Future and its Output associated type.
    pub fn future_defs(&self, prog: &Program) -> Option<(DefId, DefId)> {
        if let Some(x) = self.future_defs.get() {
            return *x;
        }
        let mut r = None;
        for di in 0..prog.defs.len() {
            let d = DefId(di as u32);
            if prog.def(d).kind == DefKind::Trait && prog.def_path(d) == "core::future::Future" {
                let sym = prog.syms.get("Output").unwrap_or(u32::MAX);
                if let Some(ad) = self.trait_assoc(prog, d, sym) {
                    r = Some((d, ad));
                }
                break;
            }
        }
        let _ = self.future_defs.set(r);
        r
    }

    /// The opaque `impl Future<Output = out>` an async fn `d` returns.
    fn async_opaque(&self, prog: &Program, d: DefId, out: TyId, n_generics: usize) -> TyId {
        self.async_fns.insert(d, out);
        let args: Vec<TyId> = (0..n_generics as u32).map(|i| self.tys.intern(TyKind::Param(i))).collect();
        let me = self.tys.intern(TyKind::Opaque(d, ASYNC_OPAQUE, args, crate::types::RegionArgsId::EMPTY));
        if let Some((fd, out_ad)) = self.future_defs(prog) {
            let mut decl = OpaqueDecl::default();
            decl.bounds.push((fd, Vec::new()));
            if let Some(sized) = self.lang_items.get(LangItem::Sized) { decl.bounds.push((sized, Vec::new())); decl.traits.push(sized); }
            decl.bindings.push((out_ad, Vec::new(), out));
            let mut todo = vec![fd];
            while let Some(x) = todo.pop() {
                if !decl.traits.contains(&x) {
                    decl.traits.push(x);
                    todo.extend(self.trait_supers(prog, x));
                }
            }
            self.opaques.insert((d, ASYNC_OPAQUE), decl);
        }
        me
    }

    /// A coroutine (async block / async fn body) closure type.
    pub fn is_coroutine(&self, t: TyId) -> bool {
        matches!(self.tys.kind(t), TyKind::Closure(f, e, ..) if self.coroutines.contains(&(*f, *e)))
    }

    /// Does `t` mention a generic parameter?
    pub fn has_param(&self, t: TyId) -> bool {
        match self.tys.kind(t) {
            TyKind::Param(_) => true,
            TyKind::Tuple(v) | TyKind::Adt(_, v, _) | TyKind::FnDef(_, v, _) | TyKind::Assoc(_, v, _) | TyKind::Opaque(_, _, v, _) => v.iter().any(|x| self.has_param(*x)),
            TyKind::Array(e, l) => self.has_param(*e) || crate::types::len_ty(*l).map_or(false, |x| self.has_param(x)),
            TyKind::Slice(e) | TyKind::Ref(_, e, _) | TyKind::Ptr(_, e) => self.has_param(*e),
            TyKind::FnPtr(ps, r, _, _) => ps.iter().any(|x| self.has_param(*x)) || self.has_param(*r),
            TyKind::Dyn(_, v, bs, _, _, _, _) => v.iter().any(|x| self.has_param(*x)) || bs.iter().any(|x| self.has_param(x.1)),
            TyKind::Closure(_, _, sg, u, _) => self.has_param(*sg) || self.has_param(*u),
            _ => false,
        }
    }

    /// Whether opaque type `t` implements `td` through its bounds (rustc: the opaque's item
    /// bounds are its only impls, auto traits aside).
    pub fn opaque_implements(&self, td: DefId, t: TyId) -> bool {
        match self.tys.kind(t) {
            TyKind::Opaque(d, i, _, _) => self.opaques.get(&(*d, *i)).map_or(false, |o| o.traits.contains(&td)),
            _ => false,
        }
    }

    /// Built-in impls of Copy / Clone for primitive and pointer-like types (rustc
    /// assemble_builtin_bound_candidates; core has no impl items for them in every case).
    /// `dyn Tr` implements Tr and its supertraits (rustc object candidates; the vtable has them).
    pub fn dyn_implements(&self, td: DefId, t: TyId) -> bool {
        match self.tys.kind(t) {
            TyKind::Dyn(p, _, _, _, _, _, autos) => autos.contains(&td) || self.trait_closure.get(p).map_or(*p == td, |v| v.contains(&td)),
            _ => false,
        }
    }

    /// `dyn Principal<..> + AutoTraits + 'a`
    fn lower_dyn(&self, cx: &crate::tcx::EvalCx<'_>, prog: &Program, file: u32, module: u32, env: &GenEnv, bounds: &[ast::Bound], lo: u32) -> TyId {
        let f = &prog.files[file as usize];
        let mut autos = Vec::new();
        for bound in bounds {
            if let ast::Bound::Trait { path, .. } = bound {
                if let Some(td) = self.resolve_type_path_def(prog, file, module, path) {
                    let d = prog.def(td);
                    if matches!(prog.files[d.file as usize].ast.item(d.item).kind, ItemKind::Trait { auto: true, .. }) {
                        autos.push(td);
                    }
                }
            }
        }
        autos.sort_by_key(|d| d.0);
        autos.dedup();
        for b in bounds {
            let (path, hrtb) = match b {
                ast::Bound::Trait { path, hrtb, .. } => (path, *hrtb),
                _ => continue,
            };
            let td = match self.resolve_type_path_def(prog, file, module, path) {
                Some(d) if prog.def(d).kind == DefKind::Trait => d,
                _ => continue,
            };
            if autos.contains(&td) { continue; }
            let outer_env = env;
            let mut predicate_env = env.clone();
            predicate_env.regions = env.regions.predicate_binder(&self.tys, prog, file, hrtb);
            let env = &predicate_env;
            let regions = self.lower_region_args(prog, file, module, env, path);
            let region = self.object_region_with_bounds(prog, file, outer_env, bounds, td, regions);
            let defaults = self.generic_object_defaults(prog, td, regions);
            let last = f.ast.segs(path.segs).last().unwrap();
            let mut args = Vec::new();
            let mut binds = Vec::new();
            let mut predicate_bound = env.regions.bound_count();
            match f.ast.gargs(last.args) {
                Some(GenericArgs::Paren(ps, r)) => {
                    let sig = ast::FnPtr { hrtb, unsafe_: false, abi: None, params: *ps, ret: *r, variadic: false };
                    let sig = self.tys.erase_all_regions(self.lower_fn_pointer(cx, prog, file, module, outer_env, &sig));
                    let TyKind::FnPtr(ps, ret, _, _) = self.tys.kind(sig) else { unreachable!() };
                    predicate_bound = 0;
                    args.push(self.tys.intern(TyKind::Tuple(ps.clone())));
                    if let Some(output) = self.callable_output(td) { binds.push((output, *ret, 0)); }
                }
                Some(GenericArgs::Angle(v)) => {
                    for g in f.ast.list(*v) {
                        match g {
                            GenericArg::Type(t) => {
                                let mut env = env.clone();
                                env.regions.object_default = defaults.get(args.len()).copied();
                                args.push(self.type_or_const_arg(cx, prog, file, module, &env, *t));
                            },
                            GenericArg::Const(e) => args.push(self.const_arg(cx, prog, file, module, env, *e)),
                            GenericArg::Binding(n, _, t) => {
                                let sym = prog.syms.get(f.text(*n)).unwrap_or(u32::MAX);
                                if let Some(ad) = self.trait_assoc(prog, td, sym) {
                                    let bt = self.lower_ty(cx, prog, file, module, env, *t);
                                    binds.push((ad, bt, 0));
                                }
                            }
                            _ => {}
                        }
                    }
                }
                None => {}
            }
            let bound = predicate_bound;
            for b in &mut binds { b.2 = bound; }
            binds.sort_by_key(|b| b.0 .0);
            if let Some(why) = self.dyn_incompatible(prog, td) {
                self.err(cx, prog, file, lo, format!("E0038: the trait `{}` is not dyn compatible: {}", prog.name(td), why));
                return self.tys.error;
            }
            // omitted trait args take their defaults (`dyn Trait` with `trait Trait<const N: u8 =
            // 12>`); a default naming Self cannot be used in an object type, left as written
            let n = self.trait_generic_count(prog, td);
            if args.len() < n && !matches!(prog.name(td), "Fn" | "FnMut" | "FnOnce" | "AsyncFn" | "AsyncFnMut" | "AsyncFnOnce") {
                let filled = self.fill_trait_defaults(cx, prog, td, self.tys.error, args.clone());
                if filled.len() == n && filled[args.len()..].iter().all(|t| !self.tys.has_error(*t)) {
                    args = filled;
                }
            }
            return self.tys.intern(TyKind::Dyn(td, args.into(), binds.into(), regions, region, bound, autos.into()));
        }
        // only auto traits (`dyn Send`, `dyn Send + Sync`): a trait object without a principal
        // (rustc: its vtable is drop, size and align alone); the first auto trait stands for it
        if let Some(&td) = autos.first() {
            let region = self.object_region(prog, file, env, bounds);
            return self.tys.intern(TyKind::Dyn(td, Default::default(), Default::default(), RegionArgsId::EMPTY, region, 0, autos.into()));
        }
        self.err(cx, prog, file, lo, "trait object without a principal trait".to_string());
        self.tys.error
    }

    fn core_crate(&self, prog: &Program) -> u32 {
        prog.prelude_crate.unwrap_or(u32::MAX)
    }

    pub fn lower_path_ty(&self, cx: &crate::tcx::EvalCx<'_>, prog: &Program, file: u32, module: u32, env: &GenEnv, p: &ast::Path) -> TyId {
        let f = &prog.files[file as usize];
        // `<T as Trait>::Name`
        if let Some(q) = prog.files[file as usize].ast.qself(p) {
            let self_t = self.lower_ty(cx, prog, file, module, env, q.ty);
            if let Some(tp) = &q.trait_path {
                if let Some(td) = self.resolve_type_path_def(prog, file, module, tp) {
                    let name = prog.syms.get(f.text(prog.files[file as usize].ast.segs(p.segs)[p.segs.len() - 1].name)).unwrap_or(u32::MAX);
                    if let Some(ad) = self.trait_assoc(prog, td, name) {
                        let tr = self.lower_region_args(prog, file, module, env, tp);
                        let explicit = self.lower_type_args_with_regions(cx, prog, file, module, env, tp, tr);
                        let mut args = vec![self_t];
                        args.extend(self.fill_trait_defaults(cx, prog, td, self_t, explicit));
                        let tr = if prog.def(ad).parent == td { tr } else { RegionArgsId::EMPTY };
                        let own = self.lower_region_args(prog, file, module, env, p);
                        let mut rs = self.tys.region_args(tr).to_vec();
                        rs.extend_from_slice(&self.tys.region_args(own));
                        return self.tys.intern(TyKind::Assoc(ad, args, self.tys.intern_region_args(&rs)));
                    }
                }
            }
            self.err(cx, prog, file, p.lo, "unsupported qualified type path".to_string());
            return self.tys.error;
        }
        // `Self::Name`: inside an impl the impl's own associated type, inside a trait a projection
        if p.segs.len() == 2 && prog.files[file as usize].ast.segs(p.segs)[0].kind == SegKind::SelfType {
            let name = prog.syms.get(f.text(prog.files[file as usize].ast.segs(p.segs)[1].name)).unwrap_or(u32::MAX);
            // `Self::Assoc` of a generic associated type without its args (rustc E0107; elided
            // lifetimes are not allowed there either)
            if prog.files[file as usize].ast.segs(p.segs)[1].args.is_none() {
                let td = env.impl_def.and_then(|imp| self.impl_trait.get(&imp).copied()).or(env.trait_def);
                if let Some(td) = td {
                    let gat = prog.traits[prog.def(td).sub as usize].iter().copied().find(|&it| prog.def(it).name == name && prog.def(it).kind == DefKind::AssocTy).map_or(false, |it| {
                        let d = prog.def(it);
                        matches!(&prog.files[d.file as usize].ast.item(d.item).kind, ItemKind::TypeAlias { generics, .. } if !generics.params.is_empty())
                    });
                    if gat {
                        // (reported, then lowered as written: an expression path takes it, typeck
                        // type_of_prefix drops the error there)
                        self.err(cx, prog, file, p.lo, format!("E0107: missing generics for associated type `{}` -- write `Self::{}<..>`", prog.syms.str(name), prog.syms.str(name)));
                    }
                }
            }
            if let Some(imp) = env.impl_def {
                if let Some(t) = self.impl_assoc_ty(cx, prog, imp, name) {
                    return t;
                }
                // a supertrait's associated type (`Self::Output` in `impl IndexMut`): the
                // projection on the impl's self type through the supertrait bound
                if let (Some(&td), Some(st)) = (self.impl_trait.get(&imp), env.self_ty) {
                    let mut args = vec![st];
                    args.extend(self.impl_trait_args.get(&imp).cloned().unwrap_or_default());
                    if let Some(t) = self.assoc_projection(cx, prog, td, args, name, 0) {
                        return t;
                    }
                }
            }
            if let Some(td) = env.trait_def {
                let mut args = Vec::new();
                for i in 0..1 + self.trait_generic_count(prog, td) {
                    args.push(self.tys.intern(TyKind::Param(i as u32)));
                }
                if let Some(t) = self.assoc_projection(cx, prog, td, args, name, 0) {
                    return t;
                }
            }
        }
        // `T::Name` on a generic param: the associated type of one of its bounds
        if p.qself.is_none() && p.segs.len() == 2 && prog.files[file as usize].ast.segs(p.segs)[0].kind == SegKind::Ident && prog.files[file as usize].ast.segs(p.segs)[0].args.is_none() {
            let pn = prog.syms.get(f.text(prog.files[file as usize].ast.segs(p.segs)[0].name)).unwrap_or(u32::MAX - 1);
            if let Some(pi) = env.names.iter().rposition(|n| *n == pn) {
                let name = prog.syms.get(f.text(prog.files[file as usize].ast.segs(p.segs)[1].name)).unwrap_or(u32::MAX);
                if let Some(t) = self.param_assoc(cx, prog, module, env, pi as u32, name) {
                    if let TyKind::Assoc(ad, args, rs) = self.tys.kind(t) {
                        let own = self.lower_region_args(prog, file, module, env, p);
                        let mut regions = self.tys.region_args(*rs).to_vec();
                        regions.extend_from_slice(&self.tys.region_args(own));
                        return self.tys.intern(TyKind::Assoc(*ad, args.clone(), self.tys.intern_region_args(&regions)));
                    }
                    return t;
                }
                self.err(cx, prog, file, p.lo, format!("no bound of `{}` has an associated type `{}` -- add the bound (T: Trait)", f.text(prog.files[file as usize].ast.segs(p.segs)[0].name), f.text(prog.files[file as usize].ast.segs(p.segs)[1].name)));
                return self.tys.error;
            }
        }
        if p.qself.is_none() && p.segs.len() == 1 {
            let seg = &prog.files[file as usize].ast.segs(p.segs)[0];
            if seg.kind == SegKind::SelfType {
                return env.self_ty.unwrap_or(self.tys.error);
            }
            let name = f.text(seg.name);
            if let Some(s) = prog.syms.get(name) {
                for (i, n) in env.names.iter().enumerate() {
                    if *n == s {
                        return self.tys.intern(TyKind::Param(i as u32));
                    }
                }
            }
        }
        let relaxed = || -> Option<DefId> {
            if p.segs.len() != 1 || p.qself.is_some() || p.global() {
                return None;
            }
            let s = prog.syms.get(prog.files[file as usize].text(prog.files[file as usize].ast.segs(p.segs)[0].name))?;
            prog.relaxed_import(module, s, true, file, p.lo)
        };
        let mark = crate::program::missing_mark();
        let d = match self.resolve_type_path_def(prog, file, module, p).or_else(relaxed) {
            Some(d) => d,
            None => {
                // (lazy loading) the skipped files this lookup missed in may define it
                crate::program::missing_confirm(mark);
                // a single name that exists elsewhere in the program: where to import it from
                let help = if p.segs.len() == 1 && p.qself.is_none() {
                    let f = &prog.files[file as usize];
                    match prog.syms.get(f.text(prog.files[file as usize].ast.segs(p.segs)[0].name)) {
                        Some(s) => crate::typeck::import_help(prog, module, s, true),
                        None => String::new(),
                    }
                } else {
                    String::new()
                };
                self.err(cx, prog, file, p.lo, format!("E0412: cannot find type `{}` in this scope{}", path_str(prog, file, p), help));
                return self.tys.error;
            }
        };
        let regions = self.lower_region_args(prog, file, module, env, p);
        let mut args = self.lower_type_args_with_regions(cx, prog, file, module, env, p, regions);
        let def = prog.def(d);
        // a module named like a primitive (`use std::str;`, globs re-exporting std's modules)
        // does not hide the primitive type
        if def.kind == DefKind::Mod && p.segs.len() == 1 && p.qself.is_none() {
            let name = f.text(prog.files[file as usize].ast.segs(p.segs)[0].name);
            for (pn, pr) in crate::program::PRIMS {
                if pn == name {
                    return self.tys.prim(pr);
                }
            }
        }
        match def.kind {
            DefKind::Prim(pr) => self.tys.prim(pr),
            DefKind::Struct | DefKind::Enum | DefKind::Union => {
                // `HashMap<K, V>` with `S = RandomState` defaulted
                self.fill_type_defaults(cx, prog, d, &mut args, env.regions.enabled.then_some(regions));
                self.tys.intern(TyKind::Adt(d, args, regions))
            }
            DefKind::TypeAlias => {
                let a = self.alias_ty(cx, prog, d);
                self.fill_type_defaults(cx, prog, d, &mut args, env.regions.enabled.then_some(regions));
                let rs = regions;
                let aenv = self.item_env(prog, d);
                let a = self.subst_decl_regions(a, &aenv, rs);
                let a = self.tys.subst(a, &args);
                if env.regions.enabled { a } else { self.tys.erase_all_regions(a) }
            }
            // a bare trait in a type (`&mut FnMut(&mut [u8])`): edition 2015's trait object
            // (rustc: `dyn` is implied there; later editions reject it, E0782)
            DefKind::Trait if prog.crates[prog.mods[module as usize].krate as usize].edition == 2015 => {
                let b = ast::Bound::Trait { hrtb: ast::List::EMPTY, maybe: false, konst: false, path: p.clone() };
                self.lower_dyn(cx, prog, file, module, env, &[b], p.lo)
            }
            _ => {
                self.err(cx, prog, file, p.lo, format!("`{}` is not a type", path_str(prog, file, p)));
                self.tys.error
            }
        }
    }

    /// Appends the defaults of type params left out of `args` (`struct HashMap<K, V, S =
    /// RandomState>` written `HashMap<u32, u64>`). Only when some args were given: `HashMap`
    /// alone in an expression path gets inference variables instead.
    pub fn fill_type_defaults(&self, cx: &crate::tcx::EvalCx<'_>, prog: &Program, d: DefId, args: &mut Vec<TyId>, regions: Option<RegionArgsId>) {
        let def = prog.def(d);
        let ast = &prog.files[def.file as usize].ast;
        let g = match &ast.item(def.item).kind {
            ItemKind::Struct(g, _) | ItemKind::Enum(g, _) | ItemKind::Union(g, _) => g.clone(),
            // `type Result<T, E = Error> = ..` written `Result<()>` (rustc: alias params default
            // like any other generic params)
            ItemKind::TypeAlias { generics, .. } => generics.clone(),
            _ => return,
        };
        let params: Vec<&ast::GenericParam> = ast.list(g.params).iter().filter(|p| !matches!(p.kind, GenericParamKind::Lifetime(_))).collect();
        if args.len() >= params.len() {
            return;
        }
        // no args at all: in a type, `Foo` with `struct Foo<A = (isize, char)>` is
        // `Foo<(isize, char)>` when every param has a default (else the args are inferred)
        if args.is_empty() && !params.iter().all(|p| matches!(p.kind, GenericParamKind::Type(_, Some(_)) | GenericParamKind::Const(_, Some(_)))) {
            return;
        }
        let mut env = self.item_env(prog, d);
        env.regions.enabled = regions.is_some();
        let module = self.item_module(prog, d);
        for i in args.len()..params.len() {
            let t = match &params[i].kind {
                GenericParamKind::Type(_, Some(dt)) => {
                    let lt = self.lower_ty(cx, prog, def.file, module, &env, *dt);
                    let lt = regions.map_or(lt, |rs| self.subst_decl_regions(lt, &env, rs));
                    self.tys.subst(lt, args)
                }
                // a const param's default (`const M: usize = N`): its value, or an earlier param
                GenericParamKind::Const(_, Some(de)) => {
                    let lt = self.const_arg(cx, prog, def.file, module, &env, *de);
                    self.tys.subst(lt, args)
                }
                _ => self.tys.error,
            };
            args.push(t);
        }
    }

    /// `<Param(pi) as Bound>::name` for the first bound of param `pi` (or a supertrait of it)
    /// that declares the associated type `name`.
    fn param_assoc(&self, cx: &crate::tcx::EvalCx<'_>, prog: &Program, module: u32, env: &GenEnv, pi: u32, name: Sym) -> Option<TyId> {
        let bounds: Vec<(u32, ast::Path)> = env.bounds.iter().filter(|b| b.0 == pi).map(|b| (b.1, b.2.clone())).collect();
        let pt = self.tys.intern(TyKind::Param(pi));
        for (bfile, path) in bounds {
            let td = match self.resolve_type_path_def(prog, bfile, module, &path) {
                Some(d) if prog.def(d).kind == DefKind::Trait => d,
                _ => continue,
            };
            let ad = match self.trait_assoc(prog, td, name) {
                Some(a) => a,
                None => continue,
            };
            let owner = prog.def(ad).parent;
            let regions = if owner == td { self.lower_region_args(prog, bfile, module, env, &path) } else { RegionArgsId::EMPTY };
            let explicit = if owner == td { self.lower_type_args_with_regions(cx, prog, bfile, module, env, &path, regions) } else { Vec::new() };
            let mut args = vec![pt];
            args.extend(self.fill_trait_defaults(cx, prog, owner, pt, explicit));
            return Some(self.tys.intern(TyKind::Assoc(ad, args, regions)));
        }
        None
    }

    pub fn alias_ty(&self, cx: &crate::tcx::EvalCx<'_>, prog: &Program, d: DefId) -> TyId {
        if let Some(t) = self.alias_tys.get(&(cx.typing_env, d)) {
            return t;
        }
        let ik = (cx.typing_env, d);
        if cx.state.alias_inprog.borrow().contains(&ik) {
            return self.tys.error;
        }
        cx.state.alias_inprog.borrow_mut().insert(ik.clone());
        let read0 = cx.state.impl_read.replace(false);
        let def = prog.def(d);
        let module = self.item_module(prog, d);
        let mut env = self.item_env(prog, d);
        env.regions.enabled = true;
        let ast = &prog.files[def.file as usize].ast;
        let t = match &ast.item(def.item).kind {
            ItemKind::TypeAlias { ty: Some(t), .. } => self.lower_ty(cx, prog, def.file, module, &env, *t),
            _ => self.tys.error,
        };
        cx.state.alias_inprog.borrow_mut().remove(&ik);
        let read = cx.state.impl_read.get();
        cx.state.impl_read.set(read0 || read);
        if !(read && cx.state.par_impls.get()) {
            self.alias_tys.insert((cx.typing_env, d), t);
        }
        t
    }

    pub fn lower_generic_args(&self, cx: &crate::tcx::EvalCx<'_>, prog: &Program, file: u32, module: u32, env: &GenEnv, p: &ast::Path) -> Vec<TyId> {
        let rs = self.lower_region_args(prog, file, module, env, p);
        self.lower_type_args_with_regions(cx, prog, file, module, env, p, rs)
    }

    fn lower_type_args_with_regions(&self, cx: &crate::tcx::EvalCx<'_>, prog: &Program, file: u32, module: u32, env: &GenEnv, p: &ast::Path, rs: RegionArgsId) -> Vec<TyId> {
        let defaults = if env.regions.enabled {
            self.resolve_type_path_def(prog, file, module, p).map(|d| self.generic_object_defaults(prog, d, rs)).unwrap_or_default()
        } else { Vec::new() };
        let mut out = Vec::new();
        let ast = &prog.files[file as usize].ast;
        if let Some(last) = ast.segs(p.segs).last() {
            if let Some(GenericArgs::Paren(ps, _)) = ast.gargs(last.args) {
                let mut args = Vec::new();
                for t in ast.list(*ps) { args.push(self.tys.erase_all_regions(self.lower_ty(cx, prog, file, module, env, *t))); }
                return vec![self.tys.intern(TyKind::Tuple(args))];
            }
            if let Some(GenericArgs::Angle(v)) = ast.gargs(last.args) {
                for g in ast.list(*v) {
                    match g {
                        GenericArg::Type(t) => {
                            let mut env = env.clone();
                            env.regions.object_default = defaults.get(out.len()).copied();
                            out.push(self.type_or_const_arg(cx, prog, file, module, &env, *t));
                        }
                        GenericArg::Const(e) => out.push(self.const_arg(cx, prog, file, module, env, *e)),
                        _ => {}
                    }
                }
            }
        }
        out
    }

    /// A const generic argument / array length expression: its value as ConstVal, or the
    /// const param it names (`N`, `{ N }`) as Param; Error when neither.
    pub fn const_arg(&self, cx: &crate::tcx::EvalCx<'_>, prog: &Program, file: u32, module: u32, env: &GenEnv, e: ast::ExprId) -> TyId {
        let outer = crate::consteval::set_const_self(cx, env.self_ty.map(|t| (t, env.impl_def)));
        let v = crate::consteval::eval_usize_expr(cx, prog, self, file, module, e);
        crate::consteval::set_const_self(cx, outer);
        if let Some(v) = v {
            return self.tys.intern(TyKind::ConstVal(v));
        }
        let ast = &prog.files[file as usize].ast;
        let mut x = e;
        loop {
            match &ast.expr(x).kind {
                ast::ExprKind::Paren(y) => x = *y,
                ast::ExprKind::Block(b, None) => match ast.stmts(*b) {
                    [ast::Stmt::Expr(y, false)] => x = *y,
                    _ => break,
                },
                _ => break,
            }
        }
        if let ast::ExprKind::Path(p) = &ast.expr(x).kind {
            // `Self::CONST` in an impl / struct: the self type's inherent associated const
            if p.qself.is_none() && !p.global() && p.segs.len() == 2 && prog.files[file as usize].text(prog.files[file as usize].ast.segs(p.segs)[0].name) == "Self" {
                if let Some(st) = env.self_ty {
                    let name = prog.syms.get(prog.files[file as usize].text(prog.files[file as usize].ast.segs(p.segs)[1].name)).unwrap_or(u32::MAX);
                    if let Some((it, _)) = self.inherent_item(cx, prog, st, name) {
                        if let Some(v) = crate::consteval::eval_const_def(cx, prog, self, it, 0) {
                            return self.tys.intern(TyKind::ConstVal(v as u64));
                        }
                    }
                }
                // in a trait impl: the trait's associated const (`[u8; Self::BYTE_LEN]` in
                // `impl FixedSizeEncoding<8, 0> for X` with `const BYTE_LEN: usize = BYTE_LEN;`)
                if let Some(imp) = env.impl_def {
                    let name = prog.syms.get(prog.files[file as usize].text(prog.files[file as usize].ast.segs(p.segs)[1].name)).unwrap_or(u32::MAX);
                    if let Some(t) = self.impl_trait_const(cx, prog, imp, name) {
                        return t;
                    }
                }
            }
            if p.qself.is_none() && !p.global() && p.segs.len() == 1 && prog.files[file as usize].ast.segs(p.segs)[0].args.is_none() {
                let name = prog.syms.get(prog.files[file as usize].text(prog.files[file as usize].ast.segs(p.segs)[0].name)).unwrap_or(u32::MAX);
                if let Some(i) = env.consts.iter().map(|c| c.0).find(|i| env.names.get(*i as usize) == Some(&name)) {
                    return self.tys.intern(TyKind::Param(i));
                }
            }
        }
        self.tys.error
    }

    /// The value of trait const `name` in impl `imp`: the impl's own item, else the trait's
    /// default -- evaluated, or (a default naming one of the trait's const params) the impl's
    /// trait argument for that param.
    pub fn impl_trait_const(&self, cx: &crate::tcx::EvalCx<'_>, prog: &Program, imp: DefId, name: Sym) -> Option<TyId> {
        let ii = prog.def(imp).sub as usize;
        for &it in &prog.impls[ii].items {
            if prog.def(it).name == name && prog.def(it).kind == DefKind::AssocConst {
                return crate::consteval::eval_const_def(cx, prog, self, it, 0).map(|v| self.tys.intern(TyKind::ConstVal(v as u64)));
            }
        }
        let td = *self.impl_trait.get(&imp)?;
        let item = prog.traits[prog.def(td).sub as usize].iter().copied().find(|&it| prog.def(it).name == name && prog.def(it).kind == DefKind::AssocConst)?;
        let d = prog.def(item);
        let iast = &prog.files[d.file as usize].ast;
        let init = match &iast.item(d.item).kind {
            ItemKind::Const(_, Some(_)) => prog.const_body(d.file, d.item).ok().flatten()?,
            _ => return None,
        };
        if let ast::ExprKind::Path(ip) = &iast.expr(init).kind {
            if ip.segs.len() == 1 && ip.qself.is_none() && !ip.global() {
                let pname = prog.files[d.file as usize].text(iast.segs(ip.segs)[0].name);
                let tdd = prog.def(td);
                if let ItemKind::Trait { generics, .. } = &prog.files[tdd.file as usize].ast.item(tdd.item).kind {
                    let names: Vec<&ast::GenericParam> = prog.files[tdd.file as usize].ast.list(generics.params).iter().filter(|g| !matches!(g.kind, GenericParamKind::Lifetime(_))).collect();
                    if let Some(k) = names.iter().position(|g| prog.files[tdd.file as usize].text(g.name) == pname) {
                        let have = self.impl_trait_args.get(&imp).and_then(|a| a.get(k).copied());
                        if have.map_or(false, |t| t != self.tys.error) {
                            return have;
                        }
                        // the impl head was collected before the constant it names could be
                        // evaluated (`impl Tr<{ u64::BYTE_LEN }, 0> for X`, impl heads are
                        // collected in parallel): its argument, evaluated now
                        let im = &prog.impls[ii];
                        if let ItemKind::Impl { trait_: Some(tp), .. } = &prog.files[im.file as usize].ast.item(im.item).kind {
                            let mast = &prog.files[im.file as usize].ast;
                            if let Some(GenericArgs::Angle(v)) = mast.segs(tp.segs).last().and_then(|l| mast.gargs(l.args)) {
                                let ga: Vec<&GenericArg> = mast.list(*v).iter().filter(|g| matches!(g, GenericArg::Type(_) | GenericArg::Const(_))).collect();
                                let mut env = self.impl_generics.get(&imp).cloned().unwrap_or_default();
                                env.impl_def = Some(imp);
                                if env.self_ty.is_none() {
                                    env.self_ty = self.impl_self.get(&imp).copied();
                                }
                                let r = match ga.get(k) {
                                    Some(GenericArg::Const(e)) => self.const_arg(cx, prog, im.file, im.module, &env, *e),
                                    Some(GenericArg::Type(t)) => self.type_or_const_arg(cx, prog, im.file, im.module, &env, *t),
                                    _ => return have,
                                };
                                return Some(r);
                            }
                        }
                        return have;
                    }
                }
            }
        }
        // a trait default depends on Self: only a Self-free expression is evaluated here (never
        // run: the trait's own item has no Self to run with)
        crate::consteval::eval_usize_expr(cx, prog, self, d.file, d.scope, init).map(|v| self.tys.intern(TyKind::ConstVal(v)))
    }

    /// A generic argument written as a type that may name a constant (`Foo<SIZE>`, `Foo<N>`:
    /// the parser cannot tell them from types).
    pub fn type_or_const_arg(&self, cx: &crate::tcx::EvalCx<'_>, prog: &Program, file: u32, module: u32, env: &GenEnv, t: ast::TyId) -> TyId {
        let ast = &prog.files[file as usize].ast;
        if let ast::Ty::Path(p) = ast.ty(t) {
            if p.qself.is_none() && p.segs.len() == 1 && prog.files[file as usize].ast.segs(p.segs)[0].args.is_none() {
                let name = prog.syms.get(prog.files[file as usize].text(prog.files[file as usize].ast.segs(p.segs)[0].name)).unwrap_or(u32::MAX);
                if !env.names.contains(&name) && prog.lookup_in_scope(module, name, true).is_none() {
                    if let Some(d) = prog.lookup_in_scope(module, name, false) {
                        if prog.def(d).kind == DefKind::Const {
                            // a const fn call initializer (`const_min_usize(A, B)`) is evaluated
                            // by running it (CTFE): requested here, the body checked again after
                            if let Some(v) = crate::consteval::eval_const_def(cx, prog, self, d, 0) {
                                return self.tys.intern(TyKind::ConstVal(v as u64));
                            }
                        }
                    }
                }
            }
        }
        self.lower_ty(cx, prog, file, module, env, t)
    }

    /// Resolves a path in the type namespace to a def.
    pub fn resolve_type_path_def(&self, prog: &Program, file: u32, module: u32, p: &ast::Path) -> Option<DefId> {
        let segs = crate::program::path_segs(prog, file, p);
        if segs.is_empty() {
            return None;
        }
        if segs.len() == 1 && !p.global() {
            if segs[0].0 != SegKind::Ident {
                return prog.resolve_mod_path(module, false, &segs, false, false);
            }
            return prog.lookup_in_scope(module, segs[0].1, true);
        }
        let parent = prog.resolve_mod_path(module, p.global(), &segs[..segs.len() - 1], false, false)?;
        prog.lookup_in_container(parent, segs[segs.len() - 1].1, true)
    }

    /// Inherent associated item `name` on type `t`: (item def, impl def).
    pub fn inherent_item(&self, cx: &crate::tcx::EvalCx<'_>, prog: &Program, t: TyId, name: Sym) -> Option<(DefId, DefId)> {
        cx.state.impl_read.set(true);
        let key = ty_key(&self.tys, t);
        if let Some(list) = self.inherent.get(&key) {
            for &imp in list {
                let ii = prog.def(imp).sub as usize;
                for &it in &prog.impls[ii].items {
                    if prog.def(it).name == name {
                        // non-generic impls must match exactly (e.g. impl Foo<u8> vs Foo<u16>)
                        if let Some(&st) = self.impl_self.get(&imp) {
                            if !self.impl_matches(cx, st, t) {
                                continue;
                            }
                        }
                        return Some((it, imp));
                    }
                }
            }
        }
        None
    }

    /// Could impl self type `pat` (with params) match `t`? Shallow structural check.
    pub fn impl_matches(&self, cx: &crate::tcx::EvalCx<'_>, pat: TyId, t: TyId) -> bool {
        if self.tys.eq_mod_regions(pat, t) {
            return true;
        }
        match (self.tys.kind(pat), self.tys.kind(t)) {
            (TyKind::Param(_), _) => true,
            // a projection of the impl's params (`Foo<D, D::Resources>`): decided once bound
            (TyKind::Assoc(..), _) if self.has_param(pat) => true,
            (_, TyKind::Infer(v)) => self.infer_may_be(cx, *v, pat),
            (TyKind::Adt(a, pa, _), TyKind::Adt(b, ta, _)) => {
                if a != b || pa.len() != ta.len() {
                    return false;
                }
                for i in 0..pa.len() {
                    if !self.impl_matches(cx, pa[i], ta[i]) {
                        return false;
                    }
                }
                true
            }
            (TyKind::Ref(m1, a, _), TyKind::Ref(m2, b, _)) => m1 == m2 && self.impl_matches(cx, *a, *b),
            (TyKind::Slice(a), TyKind::Slice(b)) => self.impl_matches(cx, *a, *b),
            (TyKind::Array(a, n1), TyKind::Array(b, n2)) => {
                (n1 == n2 || crate::types::len_ty(*n1).is_some() || crate::types::len_ty(*n2).is_some()) && self.impl_matches(cx, *a, *b)
            }
            (TyKind::Ptr(m1, a), TyKind::Ptr(m2, b)) => m1 == m2 && self.impl_matches(cx, *a, *b),
            (TyKind::Tuple(a), TyKind::Tuple(b)) => {
                if a.len() != b.len() {
                    return false;
                }
                for i in 0..a.len() {
                    if !self.impl_matches(cx, a[i], b[i]) {
                        return false;
                    }
                }
                true
            }
            (TyKind::FnPtr(..), TyKind::FnPtr(..)) => self.relate_impl_pattern(cx, pat, t, &mut Vec::new()),
            _ => false,
        }
    }
}

/// Reads `#[repr(..)]`: C, the integer type, and returns (align(N), packed(N)) (0 = absent;
/// `packed` alone is packed(1)).
/// `#[rustc_layout_scalar_valid_range_start(N)]`, `_end(N)` and `#[rustc_layout_no_niche]`.
fn read_layout_attrs(prog: &Program, file: u32, attrs: &[ast::Attr]) -> (Option<u128>, Option<u128>, bool) {
    let f = &prog.files[file as usize];
    let (mut start, mut end, mut no_niche) = (None, None, false);
    for a in attrs {
        if a.toks.hi <= a.toks.lo {
            continue;
        }
        let name = f.tok_text(a.toks.lo);
        let arg = || -> Option<u128> {
            if a.toks.lo + 2 < a.toks.hi && f.tok_text(a.toks.lo + 1) == "(" {
                crate::consteval::parse_int_lit(f.tok_text(a.toks.lo + 2)).map(|v| v as u128)
            } else {
                None
            }
        };
        match name {
            "rustc_layout_scalar_valid_range_start" => start = arg(),
            "rustc_layout_scalar_valid_range_end" => end = arg(),
            "rustc_layout_no_niche" => no_niche = true,
            _ => {}
        }
    }
    (start, end, no_niche)
}

/// Which type params of a generics list are `?Sized` (inline bound or where clause).
fn maybe_unsized_params(prog: &Program, file: u32, g: &ast::Generics) -> Vec<bool> {
    let f = &prog.files[file as usize];
    let mut names = Vec::new();
    let mut out = Vec::new();
    for p in f.ast.list(g.params) {
        if let GenericParamKind::Type(bounds, _) = &p.kind {
            names.push(f.text(p.name).to_string());
            out.push(f.ast.list(*bounds).iter().any(|b| matches!(b, ast::Bound::Trait { maybe: true, .. })));
        }
    }
    for w in f.ast.list(g.where_) {
        if let ast::WherePred::Bound { ty, bounds, .. } = w {
            if let ast::Ty::Path(pth) = f.ast.ty(*ty) {
                if pth.segs.len() == 1 && f.ast.list(*bounds).iter().any(|b| matches!(b, ast::Bound::Trait { maybe: true, .. })) {
                    let n = f.text(prog.files[file as usize].ast.segs(pth.segs)[0].name);
                    if let Some(i) = names.iter().position(|x| x == n) {
                        out[i] = true;
                    }
                }
            }
        }
    }
    out
}

fn read_repr(prog: &Program, file: u32, attrs: &[ast::Attr], repr_c: &mut bool, repr_int: &mut Option<Prim>) -> (u32, u32) {
    let f = &prog.files[file as usize];
    let (mut align, mut packed) = (0u32, 0u32);
    for a in attrs {
        if a.toks.hi <= a.toks.lo || f.tok_text(a.toks.lo) != "repr" {
            continue;
        }
        for i in a.toks.lo + 1..a.toks.hi {
            let t = f.tok_text(i);
            // repr(transparent) lays out as its one field: as repr(C) does for it (and it keeps
            // the type out of live layout edits, layout.rs live_editable)
            if t == "C" || t == "transparent" {
                *repr_c = true;
            }
            if t == "align" || t == "packed" {
                // `align(N)` / `packed(N)` / bare `packed`
                let n = if i + 3 < a.toks.hi && f.tok_text(i + 1) == "(" {
                    crate::consteval::parse_int_lit(f.tok_text(i + 2)).map_or(0, |v| v.min(1 << 29) as u32)
                } else {
                    1
                };
                if t == "align" {
                    align = align.max(n);
                } else {
                    packed = if packed == 0 { n } else { packed.min(n) };
                }
            }
            for (n, p) in crate::program::PRIMS {
                if n == t {
                    *repr_int = Some(p);
                }
            }
        }
    }
    (align, packed)
}

pub fn push_generics(prog: &Program, file: u32, g: &ast::Generics, env: &mut GenEnv) {
    let f = &prog.files[file as usize];
    for p in f.ast.list(g.params) {
        let region_index = env.regions.next_param;
        env.regions.next_param += 1;
        match &p.kind {
            GenericParamKind::Type(bounds, _) => {
                let i = env.names.len() as u32;
                env.names.push(prog.syms.get(f.text(p.name)).unwrap_or(u32::MAX));
                env.sized_params.push(i);
                for b in f.ast.list(*bounds) {
                    if let ast::Bound::Trait { path, maybe, .. } = b {
                        if *maybe { env.sized_params.retain(|p| *p != i); continue; }
                        env.bounds.push((i, file, path.clone()));
                    }
                }
            }
            GenericParamKind::Const(ty, _) => {
                env.consts.push((env.names.len() as u32, file, *ty));
                env.names.push(prog.syms.get(f.text(p.name)).unwrap_or(u32::MAX));
            }
            GenericParamKind::Lifetime(_) => env.regions.names.push((f.text(p.name).to_owned(), RegionKind::ReEarlyParam(region_index))),
        }
    }
    // `where T: Trait` on one of the params
    for w in f.ast.list(g.where_) {
        if let ast::WherePred::Bound { ty, bounds, .. } = w {
            if let ast::Ty::Path(p) = f.ast.ty(*ty) {
                if p.qself.is_none() && p.segs.len() == 1 && prog.files[file as usize].ast.segs(p.segs)[0].args.is_none() {
                    let name = prog.syms.get(f.text(prog.files[file as usize].ast.segs(p.segs)[0].name)).unwrap_or(u32::MAX - 1);
                    if let Some(i) = env.names.iter().rposition(|n| *n == name) {
                        for b in f.ast.list(*bounds) {
                            if let ast::Bound::Trait { path, maybe, .. } = b {
                                if *maybe { env.sized_params.retain(|p| *p != i as u32); continue; }
                                env.bounds.push((i as u32, file, path.clone()));
                            }
                        }
                    }
                }
            }
        }
    }
}

pub fn path_str(prog: &Program, file: u32, p: &ast::Path) -> String {
    let f = &prog.files[file as usize];
    let mut s = String::new();
    for (i, seg) in prog.files[file as usize].ast.segs(p.segs).iter().enumerate() {
        if i > 0 {
            s.push_str("::");
        }
        s.push_str(f.text(seg.name));
    }
    s
}

// ---------------------------------------------------------------- traits

impl Tcx {
    pub fn trait_generic_count(&self, prog: &Program, td: DefId) -> usize {
        let pd = prog.def(td);
        let ast = &prog.files[pd.file as usize].ast;
        if let ItemKind::Trait { generics, .. } = &ast.item(pd.item).kind {
            let mut n = 0;
            for g in ast.list(generics.params) {
                if !matches!(g.kind, GenericParamKind::Lifetime(_)) {
                    n += 1;
                }
            }
            return n;
        }
        0
    }

    /// Trait args with defaults filled (`Rhs = Self` etc.).
    pub fn fill_trait_defaults(&self, cx: &crate::tcx::EvalCx<'_>, prog: &Program, td: DefId, self_t: TyId, explicit: Vec<TyId>) -> Vec<TyId> {
        let pd = prog.def(td);
        let ast = &prog.files[pd.file as usize].ast;
        let mut out = explicit;
        let generics = match &ast.item(pd.item).kind {
            ItemKind::Trait { generics, .. } => generics.clone(),
            _ => return out,
        };
        // (type and const params in order: `trait Traitor<const N: u8 = 1, const M: u8 = N>`)
        let mut k = 0;
        for g in ast.list(generics.params) {
            let (tdef, cdef) = match &g.kind {
                GenericParamKind::Type(_, d) => (*d, None),
                GenericParamKind::Const(_, d) => (None, *d),
                GenericParamKind::Lifetime(_) => continue,
            };
            if k >= out.len() {
                let t = if tdef.is_some() || cdef.is_some() {
                    let mut env = GenEnv::default();
                    env.names.push(prog.syms.get("Self").unwrap_or(u32::MAX));
                    env.regions.next_param += 1;
                    push_generics(prog, pd.file, &generics, &mut env);
                    env.self_ty = Some(self.tys.intern(TyKind::Param(0)));
                    let lt = match (tdef, cdef) {
                        (Some(dt), _) => self.lower_ty(cx, prog, pd.file, pd.scope, &env, dt),
                        (_, Some(de)) => self.const_arg(cx, prog, pd.file, pd.scope, &env, de),
                        _ => self.tys.error,
                    };
                    let mut sub = vec![self_t];
                    sub.extend(out.iter().copied());
                    self.tys.subst(lt, &sub)
                } else {
                    self.tys.error
                };
                out.push(t);
            }
            k += 1;
        }
        out
    }

    /// Associated type `name` of trait `td` or (transitively) its supertraits.
    pub fn trait_assoc(&self, prog: &Program, td: DefId, name: Sym) -> Option<DefId> {
        for &it in &prog.traits[prog.def(td).sub as usize] {
            let d = prog.def(it);
            if d.name == name && d.kind == DefKind::AssocTy {
                return Some(it);
            }
        }
        for sup in self.trait_supers(prog, td) {
            if sup != td {
                if let Some(x) = self.trait_assoc(prog, sup, name) {
                    return Some(x);
                }
            }
        }
        None
    }

    /// `<Self as Td<args..>>::name`, where `name` may belong to a supertrait: walks the `: Super<..>`
    /// bounds with their own generic args substituted (rustc hir_ty_lowering finds the assoc item
    /// through the trait's supertrait bounds, keeping their args). `args` = [Self, Td's args].
    pub fn assoc_projection(&self, cx: &crate::tcx::EvalCx<'_>, prog: &Program, td: DefId, args: Vec<TyId>, name: Sym, depth: u32) -> Option<TyId> {
        if depth > 16 {
            return None;
        }
        for &it in &prog.traits[prog.def(td).sub as usize] {
            let d = prog.def(it);
            if d.name == name && d.kind == DefKind::AssocTy {
                return Some(self.tys.intern(TyKind::Assoc(it, args, crate::types::RegionArgsId::EMPTY)));
            }
        }
        let pd = prog.def(td);
        let ast = &prog.files[pd.file as usize].ast;
        let (generics, supers) = match &ast.item(pd.item).kind {
            ItemKind::Trait { generics, supers, .. } => (generics.clone(), supers.clone()),
            _ => return None,
        };
        // the trait's own environment: Self = param 0, then its generics
        let mut env = GenEnv::default();
        env.names.push(prog.syms.get("Self").unwrap_or(u32::MAX));
                    env.regions.next_param += 1;
        push_generics(prog, pd.file, &generics, &mut env);
        env.self_ty = Some(self.tys.intern(TyKind::Param(0)));
        env.trait_def = Some(td);
        for b in ast.list(supers) {
            if let ast::Bound::Trait { path, .. } = b {
                let sd = match self.resolve_type_path_def(prog, pd.file, pd.scope, path) {
                    Some(d) if prog.def(d).kind == DefKind::Trait => d,
                    _ => continue,
                };
                let explicit = self.lower_generic_args(cx, prog, pd.file, pd.scope, &env, path);
                let p0 = self.tys.intern(TyKind::Param(0));
                let sargs = self.fill_trait_defaults(cx, prog, sd, p0, explicit);
                let mut full = vec![args[0]];
                for a in sargs {
                    full.push(self.tys.subst(a, &args));
                }
                if let Some(t) = self.assoc_projection(cx, prog, sd, full, name, depth + 1) {
                    return Some(t);
                }
            }
        }
        None
    }

    /// Direct supertraits of a trait (resolved from its `: A + B` bounds).
    /// Does trait `td` require `Self: Sized` (a `Sized` supertrait, directly or through its
    /// supertraits: `Clone`, `Copy`)? Such a trait is not dyn compatible (rustc E0038).
    /// The signature of a fn item type's def: a fn's, or a tuple constructor's.
    #[inline]
    pub fn fn_item_sig(&self, prog: &Program, d: DefId) -> Option<&FnSigT> {
        self.fn_sig(prog, d).or_else(|| self.ctor_sigs.get(&d))
    }

    /// Is trait `td` `Sized` itself or does it require it through its supertraits?
    pub fn trait_entails_sized(&self, prog: &Program, td: DefId) -> bool {
        let core = self.core_crate(prog);
        let mut seen: Vec<DefId> = vec![td];
        let mut i = 0;
        while i < seen.len() && i < 64 {
            let cur = seen[i];
            if prog.name(cur) == "Sized" && prog.def(cur).krate == core {
                return true;
            }
            for s in self.trait_supers(prog, cur) {
                if !seen.contains(&s) {
                    seen.push(s);
                }
            }
            i += 1;
        }
        false
    }

    /// Why trait `td` is not dyn compatible (rustc E0038), for the cases checked here: a
    /// `Sized` supertrait (`Clone`, `Copy`), or an associated fn without a `self` receiver and
    /// without `where Self: Sized` (`trait B { fn f(a: A) -> A; }`) -- in it or a supertrait.
    pub fn dyn_incompatible(&self, prog: &Program, td: DefId) -> Option<String> {
        let core = self.core_crate(prog);
        let mut seen: Vec<DefId> = vec![td];
        let mut i = 0;
        while i < seen.len() && i < 64 {
            let cur = seen[i];
            for &it in &prog.traits[prog.def(cur).sub as usize] {
                let d = prog.def(it);
                if d.kind != DefKind::AssocFn {
                    continue;
                }
                let f = &prog.files[d.file as usize];
                if let ItemKind::Fn(sig, _, _) = &f.ast.item(d.item).kind {
                    let sig = f.ast.fn_sig(*sig);
                    if sig.self_param.is_some() {
                        continue;
                    }
                    // (`where Self: Sized`, or a bound on Self whose trait entails it:
                    // `where Self: Tr1<..>` with `trait Tr1: Sized`)
                    let self_sized = f.ast.list(sig.generics.where_).iter().any(|w| match w {
                        ast::WherePred::Bound { ty, bounds, .. } => {
                            matches!(f.ast.ty(*ty), ast::Ty::Path(p) if p.segs.len() == 1 && f.ast.segs(p.segs)[0].kind == SegKind::SelfType)
                                && f.ast.list(*bounds).iter().any(|b| match b {
                                    ast::Bound::Trait { path, maybe: false, .. } => self.resolve_type_path_def(prog, d.file, d.scope, path).map_or(false, |bd| prog.def(bd).kind == DefKind::Trait && self.trait_entails_sized(prog, bd)),
                                    _ => false,
                                })
                        }
                        _ => false,
                    });
                    if !self_sized {
                        return Some(format!("its associated fn `{}` has no `self` receiver (add `where Self: Sized` to it)", prog.syms.str(d.name)));
                    }
                }
            }
            for s in self.trait_supers(prog, cur) {
                if prog.name(s) == "Sized" && prog.def(s).krate == core {
                    return Some("it requires `Self: Sized`".to_string());
                }
                if !seen.contains(&s) {
                    seen.push(s);
                }
            }
            i += 1;
        }
        None
    }

    pub fn trait_supers(&self, prog: &Program, td: DefId) -> Vec<DefId> {
        let pd = prog.def(td);
        let ast = &prog.files[pd.file as usize].ast;
        let mut out = Vec::new();
        if let ItemKind::Trait { supers, .. } = &ast.item(pd.item).kind {
            for b in ast.list(*supers) {
                if let ast::Bound::Trait { path, .. } = b {
                    if let Some(d) = self.resolve_type_path_def(prog, pd.file, pd.scope, path) {
                        if prog.def(d).kind == DefKind::Trait {
                            out.push(d);
                        }
                    }
                }
            }
        }
        out
    }

    /// The supertraits of `td<targs>` as trait refs: (trait, its args without Self), the
    /// bounds' args substituted (`trait Foo<T>: Bar<i32> + Bar<T>` for Foo<bool>: Bar<i32>,
    /// Bar<bool>); Self stands for the error type (a trait object's Self is not a type here).
    pub fn trait_super_refs(&self, cx: &crate::tcx::EvalCx<'_>, prog: &Program, td: DefId, targs: &[TyId]) -> Vec<(DefId, Vec<TyId>)> {
        self.trait_super_refs_of(cx, prog, td, self.tys.error, targs)
    }

    /// The associated-type bindings of a trait's supertrait bounds with Self = `self_t`
    /// (`trait FloatNumber: Neg<Output = Self>` for T: `<T as Neg>::Output == T`): the
    /// projection and its value (rustc elaborates them as projection predicates).
    pub fn trait_super_bindings(&self, cx: &crate::tcx::EvalCx<'_>, prog: &Program, td: DefId, self_t: TyId, targs: &[TyId]) -> Vec<(TyId, TyId)> {
        let pd = prog.def(td);
        let ast = &prog.files[pd.file as usize].ast;
        let paths: Vec<ast::Path> = match &ast.item(pd.item).kind {
            ItemKind::Trait { supers, .. } => ast.list(*supers).iter().filter_map(|b| match b {
                ast::Bound::Trait { path, .. } => Some(path.clone()),
                _ => None,
            }).collect(),
            _ => return Vec::new(),
        };
        let mut env = GenEnv::default();
        env.names.push(prog.syms.get("Self").unwrap_or(u32::MAX));
                    env.regions.next_param += 1;
        if let ItemKind::Trait { generics, .. } = &ast.item(pd.item).kind {
            push_generics(prog, pd.file, generics, &mut env);
        }
        env.self_ty = Some(self.tys.intern(TyKind::Param(0)));
        env.trait_def = Some(td);
        let module = self.item_module(prog, td);
        let mut sub = vec![self_t];
        sub.extend(targs.iter().copied());
        let mut out = Vec::new();
        for path in paths {
            if let Some(GenericArgs::Paren(_, ret)) = ast.segs(path.segs).last().and_then(|l| ast.gargs(l.args)) {
                if let Some(d) = self.resolve_type_path_def(prog, pd.file, pd.scope, &path) {
                    if let Some(output) = self.callable_output(d) {
                        let written = self.lower_generic_args(cx, prog, pd.file, module, &env, &path);
                        let mut args = vec![self_t];
                        for t in written { args.push(self.tys.subst_for_inference(t, &sub)); }
                        let projection = self.tys.intern(TyKind::Assoc(output, args, RegionArgsId::EMPTY));
                        let ret = match ret { Some(t) => self.lower_ty(cx, prog, pd.file, module, &env, *t), None => self.tys.unit };
                        out.push((projection, self.tys.subst_for_inference(ret, &sub)));
                    }
                }
                continue;
            }
            let binds: Vec<(ast::Ident, AstTy)> = match ast.segs(path.segs).last().and_then(|l| ast.gargs(l.args)) {
                Some(GenericArgs::Angle(v)) => ast.list(*v).iter().filter_map(|g| match g {
                    GenericArg::Binding(n, _, t) => Some((*n, *t)),
                    _ => None,
                }).collect(),
                _ => continue,
            };
            if binds.is_empty() {
                continue;
            }
            let d = match self.resolve_type_path_def(prog, pd.file, pd.scope, &path) {
                Some(d) if prog.def(d).kind == DefKind::Trait => d,
                _ => continue,
            };
            let explicit = self.lower_generic_args(cx, prog, pd.file, module, &env, &path);
            let explicit: Vec<TyId> = explicit.iter().map(|x| self.tys.subst(*x, &sub)).collect();
            let args = self.fill_trait_defaults(cx, prog, d, self_t, explicit);
            for (n, t) in binds {
                let sym = match prog.syms.get(prog.files[pd.file as usize].text(n)) {
                    Some(x) => x,
                    None => continue,
                };
                if let Some(ad) = self.trait_assoc(prog, d, sym) {
                    let mut pa = vec![self_t];
                    pa.extend(args.iter().copied());
                    let proj = self.tys.intern(TyKind::Assoc(ad, pa, crate::types::RegionArgsId::EMPTY));
                    let v = self.lower_ty(cx, prog, pd.file, module, &env, t);
                    out.push((proj, self.tys.subst(v, &sub)));
                }
            }
        }
        out
    }

    /// trait_super_refs with Self = `self_t` (`trait Try: FromResidual` is
    /// `FromResidual<<Self as Try>::Residual>`, `trait Ord: PartialOrd` is `PartialOrd<Self>`).
    pub fn trait_super_refs_of(&self, cx: &crate::tcx::EvalCx<'_>, prog: &Program, td: DefId, self_t: TyId, targs: &[TyId]) -> Vec<(DefId, Vec<TyId>)> {
        let pd = prog.def(td);
        let ast = &prog.files[pd.file as usize].ast;
        let paths: Vec<ast::Path> = match &ast.item(pd.item).kind {
            ItemKind::Trait { supers, .. } => ast
                .list(*supers)
                .iter()
                .filter_map(|b| match b {
                    ast::Bound::Trait { path, .. } => Some(path.clone()),
                    _ => None,
                })
                .collect(),
            _ => Vec::new(),
        };
        if paths.is_empty() {
            return Vec::new();
        }
        // the trait's own environment: Self is param 0, its params follow
        let mut env = GenEnv::default();
        env.names.push(prog.syms.get("Self").unwrap_or(u32::MAX));
                    env.regions.next_param += 1;
        if let ItemKind::Trait { generics, .. } = &ast.item(pd.item).kind {
            push_generics(prog, pd.file, generics, &mut env);
        }
        env.self_ty = Some(self.tys.intern(TyKind::Param(0)));
        env.trait_def = Some(td);
        let module = self.item_module(prog, td);
        let mut sub = vec![self_t];
        sub.extend(targs.iter().copied());
        let mut out = Vec::new();
        for path in paths {
            let d = match self.resolve_type_path_def(prog, pd.file, pd.scope, &path) {
                Some(d) if prog.def(d).kind == DefKind::Trait => d,
                _ => continue,
            };
            let explicit = self.lower_generic_args(cx, prog, pd.file, module, &env, &path);
            let explicit: Vec<TyId> = explicit.iter().map(|x| self.tys.subst(*x, &sub)).collect();
            let args = self.fill_trait_defaults(cx, prog, d, self_t, explicit);
            let args: Vec<TyId> = args.into_iter().map(|x| self.normalize(cx, prog, x)).collect();
            out.push((d, args));
        }
        out
    }

    /// An impl's `type Name = T;` lowered in the impl's environment.
    pub fn impl_assoc_ty(&self, cx: &crate::tcx::EvalCx<'_>, prog: &Program, imp: DefId, name: Sym) -> Option<TyId> {
        cx.state.impl_read.set(true);
        if imp == DERIVED_IMPL || imp == crate::program::NO_DEF {
            return None;
        }
        let ii = prog.def(imp).sub as usize;
        for &it in &prog.impls[ii].items {
            let d = prog.def(it);
            if d.name == name && d.kind == DefKind::AssocTy {
                let env = match self.impl_generics.get(&imp) {
                    Some(e) => e.clone(),
                    None => GenEnv::default(),
                };
                let ast = &prog.files[d.file as usize].ast;
                if let ItemKind::TypeAlias { ty: Some(t), .. } = &ast.item(d.item).kind {
                    return Some(self.lower_ty(cx, prog, d.file, d.scope, &env, *t));
                }
            }
        }
        None
    }

    /// Whether inference variable `v` may still become type `pat`: a literal's variable only
    /// an integral (resp. float) type, an open pattern position, or another variable.
    pub fn infer_may_be(&self, cx: &crate::tcx::EvalCx<'_>, v: u32, pat: TyId) -> bool {
        match cx.lit_vars.borrow().get(v as usize).copied() {
            Some(1) => matches!(self.tys.kind(pat), TyKind::Int(_) | TyKind::Param(_) | TyKind::Infer(_) | TyKind::Error),
            Some(2) => matches!(self.tys.kind(pat), TyKind::Float(_) | TyKind::Param(_) | TyKind::Infer(_) | TyKind::Error),
            _ => true,
        }
    }

    /// Structural match of an impl pattern (with impl params) against a concrete type.
    pub fn match_ty(&self, cx: &crate::tcx::EvalCx<'_>, pat: TyId, t: TyId, binds: &mut Vec<Option<TyId>>) -> bool {
        let pat = self.tys.erase_all_regions(pat);
        let t = self.tys.erase_all_regions(t);
        if pat == t {
            // the same type, but an impl's params may coincide with the caller's own params of
            // the same index (`impl<T> [T]` against a polymorphic body's `[T0]`): bind them
            if self.tys.is_concrete(pat) {
                return true;
            }
            let mut b2 = binds.clone();
            if self.match_ty_struct(cx, pat, t, &mut b2) {
                *binds = b2;
            }
            return true;
        }
        self.match_ty_struct(cx, pat, t, binds)
    }

    fn match_ty_struct(&self, cx: &crate::tcx::EvalCx<'_>, pat: TyId, t: TyId, binds: &mut Vec<Option<TyId>>) -> bool {
        match (self.tys.kind(pat), self.tys.kind(t)) {
            (TyKind::Param(i), _) => {
                let i = *i as usize;
                if i >= binds.len() {
                    binds.resize(i + 1, None);
                }
                match binds[i] {
                    Some(b) => self.tys.eq_mod_regions(b, t),
                    None => {
                        binds[i] = Some(t);
                        true
                    }
                }
            }
            // an impl self type naming a projection of its params (`impl<D: Device> Tr for
            // Foo<D, D::Resources>`): once the params it names are bound, its normal form must be
            // the type (rustc normalizes the impl header before unifying); until then it matches
            (TyKind::Assoc(_, pa, _), _) if !matches!(self.tys.kind(t), TyKind::Assoc(..)) && pa.iter().any(|x| self.has_param(*x)) => {
                let bound: Vec<TyId> = binds.iter().enumerate().map(|(k, b)| b.unwrap_or_else(|| self.tys.intern(TyKind::Param(k as u32)))).collect();
                let inst = self.tys.subst(pat, &bound);
                if self.has_param(inst) || !self.impl_projection_ready {
                    return true;
                }
                let prog = cx.prog;
                let n = self.normalize(cx, prog, inst);
                matches!(self.tys.kind(n), TyKind::Assoc(..)) || n == t || self.tys.has_infer(t)
            }
            (TyKind::Adt(a, pa, _), TyKind::Adt(b, ta, _)) if a == b && pa.len() == ta.len() => {
                for k in 0..pa.len() {
                    if !self.match_ty(cx, pa[k], ta[k], binds) {
                        return false;
                    }
                }
                true
            }
            (TyKind::Tuple(pa), TyKind::Tuple(ta)) if pa.len() == ta.len() => {
                for k in 0..pa.len() {
                    if !self.match_ty(cx, pa[k], ta[k], binds) {
                        return false;
                    }
                }
                true
            }
            (TyKind::Ref(m1, a, _), TyKind::Ref(m2, b, _)) if m1 == m2 => self.match_ty(cx, *a, *b, binds),
            (TyKind::Ptr(m1, a), TyKind::Ptr(m2, b)) if m1 == m2 => self.match_ty(cx, *a, *b, binds),
            (TyKind::Slice(a), TyKind::Slice(b)) => self.match_ty(cx, *a, *b, binds),
            (TyKind::Array(a, n), TyKind::Array(b, m)) => {
                // `impl<T, const N: usize> .. for [T; N]`: the pattern's length param binds
                let len_ok = match (crate::types::len_ty(*n), crate::types::len_ty(*m)) {
                    (None, None) => n == m,
                    (Some(pl), None) => match self.tys.lookup(&TyKind::ConstVal(*m)) {
                        Some(v) => self.match_ty(cx, pl, v, binds),
                        None => false,
                    },
                    (Some(pl), Some(tl)) => self.match_ty(cx, pl, tl, binds),
                    (None, Some(_)) => false,
                };
                len_ok && self.match_ty(cx, *a, *b, binds)
            }
            (TyKind::ConstVal(a), TyKind::ConstVal(b)) => a == b,
            (TyKind::Opaque(a, i, pa, _), TyKind::Opaque(b, j, ta, _)) if a == b && i == j && pa.len() == ta.len() => {
                let (pa, ta) = (pa.clone(), ta.clone());
                (0..pa.len()).all(|k| self.match_ty(cx, pa[k], ta[k], binds))
            }
            // impls for fn pointer types (`impl<T, R, A> M for extern "C" fn(&T, A) -> R`)
            (TyKind::FnPtr(..), TyKind::FnPtr(..)) => self.relate_impl_pattern(cx, pat, t, binds),
            _ => false,
        }
    }

    /// The impl of trait `td` for `self_t` with trait args `targs`, and the impl's args.
    /// Impls whose self type is a bare generic param (`impl<T: Display> ToString for T`).
    pub fn blanket_impls(&self, cx: &crate::tcx::EvalCx<'_>) -> std::sync::Arc<[DefId]> {
        cx.state.impl_read.set(true);
        if let Some(b) = &self.blanket_cache {
            return b.clone();
        }
        self.compute_blanket().into()
    }

    fn compute_blanket(&self) -> Vec<DefId> {
        let mut v = Vec::new();
        if let Some(list) = self.impls_by_key.get(&TyKey::Other) {
            for &imp in list {
                if let Some(&pat) = self.impl_self.get(&imp) {
                    if matches!(self.tys.kind(pat), TyKind::Param(_)) {
                        v.push(imp);
                    }
                }
            }
        }
        v
    }

    /// The param-env predicates on `t` (TypingEnv::param_env), as (trait, trait args).
    pub fn param_env_of(&self, cx: &crate::tcx::EvalCx<'_>, t: TyId) -> Vec<(DefId, Vec<TyId>)> {
        match self.param_env(cx.typing_env.param_env) {
            Some(env) => env.preds.iter().filter(|e| self.tys.eq_mod_regions(e.0, t)).map(|e| (e.1, e.2.clone())).collect(),
            None => Vec::new(),
        }
    }

    /// The declared bounds of associated type `ad` (`type IntoIter: Iterator<Item = ..>;`), as
    /// (trait, trait args) with `args` (the projection's [Self, trait args..]) substituted: rustc
    /// item_bounds of the associated type.
    pub fn assoc_decl_bounds(&self, cx: &crate::tcx::EvalCx<'_>, prog: &Program, ad: DefId, args: &[TyId]) -> Vec<(DefId, Vec<TyId>)> {
        self.assoc_decl_bounds_eqs(cx, prog, ad, args).0
    }

    /// assoc_decl_bounds and the bounds' bindings as projection equalities (`type IntoIter:
    /// Iterator<Item = Self::Item>`: `<<T as IntoIterator>::IntoIter as Iterator>::Item ==
    /// <T as IntoIterator>::Item`).
    pub fn assoc_decl_bounds_eqs(&self, cx: &crate::tcx::EvalCx<'_>, prog: &Program, ad: DefId, args: &[TyId]) -> (Vec<(DefId, Vec<TyId>)>, Vec<(TyId, TyId)>) {
        let d = prog.def(ad);
        let td = d.parent;
        if td == crate::program::NO_DEF || prog.def(td).kind != DefKind::Trait {
            return (Vec::new(), Vec::new());
        }
        let ast = &prog.files[d.file as usize].ast;
        let paths: Vec<ast::Path> = match &ast.item(d.item).kind {
            ItemKind::TypeAlias { bounds, .. } => ast
                .list(*bounds)
                .iter()
                .filter_map(|b| match b {
                    ast::Bound::Trait { maybe: false, path, .. } => Some(path.clone()),
                    _ => None,
                })
                .collect(),
            _ => Vec::new(),
        };
        let maybe_sized = match ast.item(d.item).kind {
            ItemKind::TypeAlias { bounds, .. } => ast.list(bounds).iter().any(|b| matches!(b, ast::Bound::Trait { maybe: true, .. })),
            _ => false,
        };
        let proj = self.tys.intern(TyKind::Assoc(ad, args.to_vec(), crate::types::RegionArgsId::EMPTY));
        let mut eqs = Vec::new();
        let pd = prog.def(td);
        let tast = &prog.files[pd.file as usize].ast;
        let mut env = GenEnv::default();
        env.names.push(prog.syms.get("Self").unwrap_or(u32::MAX));
                    env.regions.next_param += 1;
        if let ItemKind::Trait { generics, .. } = &tast.item(pd.item).kind {
            push_generics(prog, pd.file, generics, &mut env);
        }
        env.self_ty = Some(self.tys.intern(TyKind::Param(0)));
        env.trait_def = Some(td);
        let module = self.item_module(prog, td);
        let mut out = Vec::new();
        if !maybe_sized { if let Some(sized) = self.lang_items.get(LangItem::Sized) { out.push((sized, Vec::new())); } }
        for path in paths {
            let bd = match self.resolve_type_path_def(prog, d.file, d.scope, &path) {
                Some(x) if prog.def(x).kind == DefKind::Trait => x,
                _ => continue,
            };
            let explicit = self.lower_generic_args(cx, prog, d.file, module, &env, &path);
            let explicit: Vec<TyId> = explicit.iter().map(|x| self.tys.subst(*x, args)).collect();
            let ba = self.fill_trait_defaults(cx, prog, bd, proj, explicit);
            if let Some(GenericArgs::Angle(v)) = ast.segs(path.segs).last().and_then(|l| ast.gargs(l.args)) {
                for g in ast.list(*v) {
                    if let GenericArg::Binding(n, _, ty) = g {
                        let sym = prog.syms.get(prog.files[d.file as usize].text(*n)).unwrap_or(u32::MAX);
                        if let Some(bad) = self.trait_assoc(prog, bd, sym) {
                            let v = self.lower_ty(cx, prog, d.file, module, &env, *ty);
                            let mut pa = vec![proj];
                            pa.extend(ba.iter().copied());
                            eqs.push((self.tys.intern(TyKind::Assoc(bad, pa, crate::types::RegionArgsId::EMPTY)), self.tys.subst(v, args)));
                        }
                    }
                }
            }
            out.push((bd, ba));
        }
        (out, eqs)
    }

    /// Written impl bounds for param-environment elaboration; proof goes through solve.
    fn resolve_impl_bounds(&mut self, cx: &EvalCx<'_>, imp: DefId, prog: &Program) {
        if let Some(env) = self.impl_generics.get(&imp).cloned() {
            let module = self.item_module(prog, imp);
            for (param, file, path) in &env.bounds {
                if let Some(td) = self.resolve_type_path_def(prog, *file, module, path) {
                    if prog.def(td).kind != DefKind::Trait { continue; }
                    let args = self.lower_generic_args(cx, prog, *file, module, &env, path);
                    self.impl_trait_bounds.entry(imp).or_default().push((*param, td, args));
                }
            }
        }
    }

    /// Whether `t` is known not to implement Copy (an ADT without a Copy impl, a `&mut`, a str /
    /// slice / dyn, a tuple or array of such); open parts count as possibly Copy.
    pub fn known_not_copy(&self, cx: &crate::tcx::EvalCx<'_>, t: TyId) -> bool {
        match self.tys.kind(t).clone() {
            TyKind::Int(_) | TyKind::Float(_) | TyKind::Bool | TyKind::Char | TyKind::Never | TyKind::Ptr(..) | TyKind::FnPtr(..) | TyKind::FnDef(..) | TyKind::Ref(false, _, _) => false,
            TyKind::Ref(true, _, _) | TyKind::Str | TyKind::Slice(_) | TyKind::Dyn(..) => true,
            TyKind::Tuple(v) => v.iter().any(|x| self.known_not_copy(cx, *x)),
            TyKind::Array(e, _) => self.known_not_copy(cx, e),
            TyKind::Adt(d, _, _) => {
                let ct = match self.copy_trait {
                    Some(c) => c,
                    None => return false,
                };
                !self.derived.contains_key(&(d, ct)) && matches!(self.select_trait(cx, ct, t, &[]), SelectionResult::NoSolution)
            }
            _ => false,
        }
    }

    /// A blanket impl's self param matched against a body's own param of the same index
    /// (`impl<I> .. for I` with `I` = the body's `T0`): match_ty sees the same TyId and binds
    /// nothing; the impl's bounds are still on that type.
    fn bind_blanket_self(&self, pat: TyId, t: TyId, binds: &mut [Option<TyId>]) {
        if let TyKind::Param(k) = self.tys.kind(pat).clone() {
            if let Some(b @ None) = binds.get_mut(k as usize) {
                *b = Some(t);
            }
        }
    }

    /// Replaces resolvable associated type projections by the impl's types.
    /// The type of a field with declared type `decl` in an ADT instance with `args`: substituted
    /// and normalized (rustc FieldDef::ty + normalize_erasing_regions) -- a field declared as a
    /// projection (`<StandardAlloc as Allocator<u8>>::AllocatedMemory`) is its concrete type.
    /// Body inference has no region solver yet; item queries retain written regions.
    pub fn normalize_for_inference(&self, cx: &crate::tcx::EvalCx<'_>, prog: &Program, t: TyId) -> TyId {
        self.tys.erase_all_regions(self.normalize(cx, prog, self.tys.erase_all_regions(t)))
    }

    pub fn normalize(&self, cx: &crate::tcx::EvalCx<'_>, prog: &Program, t: TyId) -> TyId {
        // only projections normalize: a type without one is already itself
        if !self.tys.may_project(t) {
            return t;
        }
        // Concrete projections are memoized per typing environment; never an answer
        // cut short by the depth limit or by a cycle cut of a selection further out, nor one
        // seen while the impl tables are incomplete (parallel impl heads)
        let cacheable = self.tys.is_concrete(t) && !cx.state.par_impls.get() && self.norm_ready.load(std::sync::atomic::Ordering::Acquire);
        if cacheable {
            if let Some(r) = self.norm_cache.get(&(cx.typing_env, t)) {
                return r;
            }
        }
        let outer_cut = cx.state.norm_cut.replace(false);
        let r = self.normalize_inner(cx, prog, t);
        let cut = cx.state.norm_cut.get();
        cx.state.norm_cut.set(outer_cut || cut);
        if cacheable && !cut && !self.tys.has_stuck_assoc(r) {
            self.norm_cache.insert((cx.typing_env, t), r);
        }
        r
    }

    fn normalize_inner(&self, cx: &crate::tcx::EvalCx<'_>, prog: &Program, t: TyId) -> TyId {
        let k = self.tys.kind(t).clone();
        match k {
            TyKind::Assoc(ad, args, regions) => {
                let Some(_depth) = Depth::enter_solver(cx.state) else {
                    cx.state.norm_cut.set(true);
                    cx.state.norm_overflow.set(true);
                    return t;
                };
                let mut n = Vec::new();
                for x in &args {
                    n.push(self.normalize(cx, prog, *x));
                }
                // a projection equality of the polymorphic body being checked (its where-clause
                // `I: IntoIterator<Item = u32>`, or an associated type's declared binding)
                if let Some(env) = self.param_env(cx.typing_env.param_env) {
                    if !env.eqs.is_empty() {
                        let pt = self.tys.intern(TyKind::Assoc(ad, n.clone(), regions));
                        if let Some(&(_, v)) = env.eqs.iter().find(|e| e.0 == pt) {
                            return self.normalize(cx, prog, v);
                        }
                    }
                }
                // a projection on a rigid projection: the inner associated type's declared
                // bindings (`type IntoIter: Iterator<Item = Self::Item>` makes
                // `<<O as IntoIterator>::IntoIter as Iterator>::Item` = `<O as IntoIterator>::Item`)
                if let Some(TyKind::Assoc(ad2, a2, _)) = n.first().map(|x| self.tys.kind(*x).clone()) {
                    let pt = self.tys.intern(TyKind::Assoc(ad, n.clone(), regions));
                    let (_, eqs) = self.assoc_decl_bounds_eqs(cx, prog, ad2, &a2);
                    if let Some(&(_, v)) = eqs.iter().find(|e| e.0 == pt) {
                        if v != pt {
                            return self.normalize(cx, prog, v);
                        }
                    }
                }
                if let Some(TyKind::Dyn(_, _, bs, _, _, _, _)) = n.first().map(|x| self.tys.kind(*x).clone()) {
                    if let Some(b) = bs.iter().find(|b| b.0 == ad) {
                        return b.1;
                    }
                }
                // `<coroutine as Future>::Output`: the body's type
                if let Some(TyKind::Closure(f, e, sig, _, _)) = n.first().map(|x| self.tys.kind(*x).clone()) {
                    if self.coroutines.contains(&(f, e)) && self.future_defs.get().copied().flatten().map_or(false, |x| x.1 == ad) {
                        if let TyKind::FnPtr(_, r, _, _) = self.tys.kind(sig).clone() {
                            return r;
                        }
                    }
                }
                // a projection on an opaque type: its bound's binding, else it stays rigid
                // (rustc normalizes `<impl Iterator<Item = T> as Iterator>::Item` to T through
                // the opaque's item bounds and reveals the rest only in codegen)
                if let Some(TyKind::Opaque(od, oi, oargs, _)) = n.first().map(|x| self.tys.kind(*x).clone()) {
                    let decl = self.opaques.get(&(od, oi)).unwrap_or_default();
                    for (bad, bta, bt) in &decl.bindings {
                        if *bad != ad {
                            continue;
                        }
                        let ta: Vec<TyId> = bta.iter().map(|x| self.tys.subst(*x, &oargs)).collect();
                        let same = |tys: &Types, x: &TyId, y: &TyId| x == y || !tys.is_concrete(*x) || !tys.is_concrete(*y);
                        if (ta.is_empty() && n.len() == 1) || (ta.len() + 1 == n.len() && ta.iter().zip(&n[1..]).all(|(x, y)| same(&self.tys, x, y))) {
                            let r = self.tys.subst(*bt, &oargs);
                            return self.normalize(cx, prog, r);
                        }
                    }
                    if decl.traits.contains(&prog.def(ad).parent) {
                        return self.tys.intern(TyKind::Assoc(ad, n, regions));
                    }
                }
                let projection = self.tys.intern(TyKind::Assoc(ad, n.clone(), regions));
                let mut infcx = crate::solve::infer::Inference::with_inputs(&self.tys, cx, &n);
                match crate::solve::select::normalize_projection(self, cx, &mut infcx, projection) {
                    // (a body's `<(Wrap<?0>,) as Indirect>::Out` selects with ?0 bound to the
                    // impl's fresh `U`: no answer of this query; the body normalizes it in its own
                    // inference context, Fcx::normalize_body_type)
                    Ok((value, crate::solve::goal::Certainty::Yes)) if value != projection && infcx.answer_in_inputs(value) => return self.normalize(cx, prog, value),
                    Ok((_, crate::solve::goal::Certainty::Maybe(cause))) => {
                        cx.state.norm_cut.set(true);
                        if matches!(cause, crate::solve::goal::MaybeCause::Overflow { .. }) {
                            cx.state.norm_overflow.set(true);
                        }
                    }
                    _ => {}
                }
                self.tys.intern(TyKind::Assoc(ad, n, regions))
            }
            TyKind::Tuple(v) => {
                let mut n = Vec::new();
                for x in v {
                    n.push(self.normalize(cx, prog, x));
                }
                self.tys.intern(TyKind::Tuple(n))
            }
            TyKind::Adt(d, v, regions) => {
                let mut n = Vec::new();
                for x in v {
                    n.push(self.normalize(cx, prog, x));
                }
                self.tys.intern(TyKind::Adt(d, n, regions))
            }
            TyKind::Ref(m, e, region) => {
                let e = self.normalize(cx, prog, e);
                self.tys.intern(TyKind::Ref(m, e, region))
            }
            TyKind::Ptr(m, e) => {
                let e = self.normalize(cx, prog, e);
                self.tys.intern(TyKind::Ptr(m, e))
            }
            TyKind::Slice(e) => {
                let e = self.normalize(cx, prog, e);
                self.tys.intern(TyKind::Slice(e))
            }
            TyKind::Array(e, l) => {
                let e = self.normalize(cx, prog, e);
                match crate::types::len_ty(l) {
                    Some(lt) => self.tys.mk_array(e, lt),
                    None => self.tys.intern(TyKind::Array(e, l)),
                }
            }
            TyKind::Dyn(d, v, bs, regions, region, bound, autos) => {
                let mut n = Vec::new();
                for x in v {
                    n.push(self.normalize(cx, prog, x));
                }
                let mut nb = Vec::new();
                for (a, x, n) in bs {
                    nb.push((a, self.normalize(cx, prog, x), n));
                }
                self.tys.intern(TyKind::Dyn(d, n.into(), nb.into(), regions, region, bound, autos.clone()))
            }
            // generic args of fn items (`size_of::<A::Item>`) and fn signatures
            TyKind::FnDef(d, v, regions) => {
                let n: Vec<TyId> = v.iter().map(|x| self.normalize(cx, prog, *x)).collect();
                self.tys.intern(TyKind::FnDef(d, n, regions))
            }
            TyKind::Opaque(d, i, v, regions) => {
                let n: Vec<TyId> = v.iter().map(|x| self.normalize(cx, prog, *x)).collect();
                self.tys.intern(TyKind::Opaque(d, i, n, regions))
            }
            TyKind::FnPtr(ps, r, c, bound) => {
                let n: Vec<TyId> = ps.iter().map(|x| self.normalize(cx, prog, *x)).collect();
                let r = self.normalize(cx, prog, r);
                self.tys.intern(TyKind::FnPtr(n, r, c, bound))
            }
            TyKind::Closure(f, e, sig, up, owner) => {
                let sig = self.normalize(cx, prog, sig);
                let up = self.normalize(cx, prog, up);
                self.tys.intern(TyKind::Closure(f, e, sig, up, owner))
            }
            _ => t,
        }
    }

    /// A call to trait method `d` with args [Self, trait args.., own..] -> the concrete
    /// function to run: the impl's method, or the trait's default body.
    pub fn resolve_trait_method(&self, cx: &crate::tcx::EvalCx<'_>, prog: &Program, d: DefId, args: &[TyId]) -> MethodResolution {
        let td = prog.def(d).parent;
        if prog.def(td).kind != DefKind::Trait || args.is_empty() {
            return MethodResolution::Resolved(d, args.to_vec());
        }
        let nt = self.trait_generic_count(prog, td);
        let self_t = args[0];
        let targs: Vec<TyId> = args[1..(1 + nt).min(args.len())].to_vec();
        let own: Vec<TyId> = if args.len() > 1 + nt { args[1 + nt..].to_vec() } else { Vec::new() };
        let result = self.select_trait(cx, td, self_t, &targs);
        let selected = match result {
            SelectionResult::Ok(selected) => selected,
            SelectionResult::Ambiguous(cause) => return MethodResolution::Ambiguous(crate::solve::select::trait_goal(cx, td, self_t, &targs), cause),
            SelectionResult::NoSolution => return MethodResolution::NoSolution(crate::solve::select::trait_goal(cx, td, self_t, &targs)),
        };
        {
            let (imp, iargs) = (selected.method_owner(), selected.args);
            if imp == DERIVED_IMPL || imp == NO_DEF {
                // compiler-generated (lowered as glue), or a trait object's own method
                // (virtual): the call stays on the trait method
                return MethodResolution::Resolved(d, args.to_vec());
            }
            let name = prog.def(d).name;
            let ii = prog.def(imp).sub as usize;
            let kind = prog.def(d).kind;
            for &it in &prog.impls[ii].items {
                if prog.def(it).name == name && prog.def(it).kind == kind {
                    let mut a = iargs.clone();
                    a.extend(own.iter().copied());
                    return MethodResolution::Resolved(it, a);
                }
            }
        }
        MethodResolution::Resolved(d, args.to_vec())
    }

    /// Trait methods named `name` callable on `t` (via trait impls for its type constructor):
    /// (trait method def, impl def).
    pub fn trait_methods_for(&self, cx: &crate::tcx::EvalCx<'_>, prog: &Program, t: TyId, name: Sym) -> Vec<(DefId, DefId)> {
        self.trait_methods_for_uncached(cx, prog, t, name)
    }

    fn trait_methods_for_uncached(&self, cx: &crate::tcx::EvalCx<'_>, prog: &Program, t: TyId, name: Sym) -> Vec<(DefId, DefId)> {
        cx.state.impl_read.set(true);
        let key = ty_key(&self.tys, t);
        let mut out = Vec::new();
        // only impls of traits that have a method `name` can contribute: that test is cheap,
        // matching the impl and proving its where-clauses is not (rustc probes the traits
        // that have an item of that name: method/probe.rs assemble_extension_candidates_for_trait)
        let has = |tcx: &Tcx, imp: DefId| tcx.impl_trait.get(&imp).map_or(false, |&td| prog.traits[prog.def(td).sub as usize].iter().any(|&it| prog.def(it).name == name && prog.def(it).kind == DefKind::AssocFn));
        let mut list: Vec<DefId> = self.impls_by_key_method.get(&(key, name)).cloned().unwrap_or_default();
        // blanket impls (`impl<I: Iterator> IntoIterator for I`) whose bounds `t` meets
        if key != TyKey::Other {
            for &imp in self.blanket_impls(cx).iter() {
                if !has(self, imp) {
                    continue;
                }
                let n = self.impl_generics.get(&imp).map_or(0, |e| e.names.len());
                let mut binds: Vec<Option<TyId>> = vec![None; n];
                let pat = self.impl_self[&imp];
                if self.match_ty(cx, pat, t, &mut binds) && {
                    self.bind_blanket_self(pat, t, &mut binds);
                    !matches!(self.evaluate_impl(cx, imp, &binds), Err(_))
                } {
                    list.push(imp);
                }
            }
        }
        if let (TyKind::Tuple(..) | TyKind::Closure(..) | TyKind::FnPtr(..) | TyKind::FnDef(..), Some(ct)) = (self.tys.kind(t).clone(), self.clone_trait) {
            if !matches!(self.select_trait(cx, ct, t, &[]), SelectionResult::NoSolution) {
                for &it in &prog.traits[prog.def(ct).sub as usize] {
                    if prog.def(it).name == name && prog.def(it).kind == DefKind::AssocFn {
                        out.push((it, DERIVED_IMPL));
                    }
                }
            }
        }
        // a coroutine's Future::poll (builtin impl: no impl item)
        if self.is_coroutine(t) {
            if let Some((fd, _)) = self.future_defs.get().copied().flatten() {
                for &it in &prog.traits[prog.def(fd).sub as usize] {
                    if prog.def(it).name == name && prog.def(it).kind == DefKind::AssocFn {
                        out.push((it, crate::program::NO_DEF));
                    }
                }
            }
        }
        if let TyKind::Adt(ad, _, _) = self.tys.kind(t).clone() {
            let derived: Vec<DefId> = self.derived_by_adt.get(&ad).cloned().unwrap_or_default();
            for td in derived {
                for &it in &prog.traits[prog.def(td).sub as usize] {
                    if prog.def(it).name == name && prog.def(it).kind == DefKind::AssocFn {
                        out.push((it, DERIVED_IMPL));
                    }
                }
            }
        }
        {
            for &imp in &list {
                if let Some(&pat) = self.impl_self.get(&imp) {
                    if !self.impl_matches(cx, pat, t) {
                        continue;
                    }
                    // a candidate only when its where-clauses can hold (rustc method/probe.rs
                    // consider_probe: `ExactSizeIterator for Box<I> where I: ExactSizeIterator`
                    // is no candidate for `Box<str>.len()`, which autoderefs to str::len)
                    let n = self.impl_generics.get(&imp).map_or(0, |e| e.names.len());
                    let mut binds: Vec<Option<TyId>> = vec![None; n];
                    if self.match_ty(cx, pat, t, &mut binds) && {
                        self.bind_blanket_self(pat, t, &mut binds);
                        !!matches!(self.evaluate_impl(cx, imp, &binds), Err(_))
                    } {
                        continue;
                    }
                }
                let td = match self.impl_trait.get(&imp) {
                    Some(t) => *t,
                    None => continue,
                };
                for &it in &prog.traits[prog.def(td).sub as usize] {
                    if prog.def(it).name == name && prog.def(it).kind == DefKind::AssocFn {
                        out.push((it, imp));
                    }
                }
            }
        }
        out
    }
}

/// Predicate environment and typing mode, following rustc_middle/src/ty/mod.rs:1050.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct TypingEnv {
    pub param_env: ParamEnvId,
    pub mode: TypingMode,
}

/// rustc_type_ir/src/infer_ctxt.rs:66. Empty Analysis still treats parameters as rigid.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum TypingMode {
    Coherence,
    Analysis { defining_opaques: DefiningOpaquesId },
    Borrowck,
    PostAnalysis,
}

impl TypingEnv {
    /// rustc_middle/src/ty/mod.rs:1073: codegen has no predicates in scope.
    pub fn fully_monomorphized() -> Self {
        Self { param_env: ParamEnvId::EMPTY, mode: TypingMode::PostAnalysis }
    }
}

/// One explicit query stack. Mutable traversal state is not part of cache equality
/// (rustc_infer/src/infer/mod.rs:244; rustc_trait_selection/src/traits/select/mod.rs:1354).
pub struct EvalCx<'p> {
    pub prog: &'p Program,
    pub typing_env: TypingEnv,
    pub state: &'p EvalState,
    pub lit_vars: std::cell::RefCell<Vec<u8>>,
}

/// Selection stacks and constant frames follow one explicit evaluation. Constant inputs
/// mirror rustc_const_eval/src/interpret/eval_context.rs:27 (InterpCx and its typing env).
#[derive(Default)]
pub struct EvalState {
    /// Region obligations registered by normalization/selection. The N0/N1
    /// response producer must populate this channel; borrowck never fabricates
    /// obligations from type arguments or trait names.
    pub registered_region_obligations: std::cell::RefCell<Vec<outlives::OutlivesPredicate>>,
    pub(crate) solver_depth: std::cell::Cell<u32>,
    pending_const_hit: std::cell::Cell<bool>,
    pub const_wait: std::cell::Cell<bool>,
    pub const_asked: std::cell::Cell<u64>,
    impl_read: std::cell::Cell<bool>,
    par_impls: std::cell::Cell<bool>,
    norm_cut: std::cell::Cell<bool>,
    pub(crate) norm_overflow: std::cell::Cell<bool>,
    pub(crate) overflow_traced: std::cell::Cell<bool>,
    errors: std::cell::RefCell<Option<Vec<String>>>,
    requests: std::cell::RefCell<Option<Vec<DefId>>>,
    pub const_self: std::cell::Cell<Option<(TyId, Option<DefId>)>>,
    pub call_env: std::cell::RefCell<Vec<Vec<(Sym, i128)>>>,
    pub const_args: std::cell::RefCell<Option<(DefId, Vec<TyId>)>>,
    alias_inprog: std::cell::RefCell<crate::fxhash::HashSet<(TypingEnv, DefId)>>,
    pub opaque_inprog: std::cell::RefCell<crate::fxhash::HashSet<TyId>>,
    pub(crate) typeck_inprog: std::cell::RefCell<Vec<DefId>>,
    /// Selection requests hidden definitions; fulfillment services them outside probing.
    pub(crate) opaque_requests: std::cell::RefCell<Vec<TyId>>,
    pub tc_depth: std::cell::Cell<u32>,
}

impl EvalState {
    pub fn new() -> Self {
        Self::default()
    }
}

impl<'p> EvalCx<'p> {
    pub fn new(prog: &'p Program, typing_env: TypingEnv, state: &'p EvalState) -> Self {
        Self { prog, typing_env, state, lit_vars: Default::default() }
    }

    pub fn body(&self) -> Self {
        Self { prog: self.prog, typing_env: self.typing_env, state: self.state, lit_vars: Default::default() }
    }


}

pub(crate) struct Depth<'a>(&'a std::cell::Cell<u32>);
impl<'a> Depth<'a> {
    /// One obligation budget across nested evaluations, as in nightly
    /// rustc_type_ir/src/search_graph/mod.rs:294-319 @8d1a764.
    pub(crate) fn enter_solver(state: &'a EvalState) -> Option<Self> {
        if state.solver_depth.get() >= 128 { return None; }
        Some(Self::enter(&state.solver_depth))
    }

    fn enter(cell: &'a std::cell::Cell<u32>) -> Self {
        cell.set(cell.get() + 1);
        Self(cell)
    }
}
impl Drop for Depth<'_> {
    fn drop(&mut self) { self.0.set(self.0.get() - 1); }
}

/// A polymorphic body's where-clauses (rustc's ParamEnv): trait predicates (self type, trait,
/// trait args), elaborated, and projection equalities (`<I as IntoIterator>::Item == u32`).
#[derive(Default, Clone, Debug, PartialEq, Eq, Hash)]
pub struct ParamEnv {
    pub preds: Vec<(TyId, DefId, Vec<TyId>)>,
    pub eqs: Vec<(TyId, TyId)>,
}

/// `_` (also parenthesized) as an array length / repeat count: inferred (rustc
/// generic_arg_infer, stable since 1.89).
pub fn is_infer_len(ast: &crate::ast::Ast, n: crate::ast::ExprId) -> bool {
    match &ast.expr(n).kind {
        crate::ast::ExprKind::Underscore => true,
        crate::ast::ExprKind::Paren(x) => is_infer_len(ast, *x),
        _ => false,
    }
}

/// Tcx and Program are shared across compile threads.
#[allow(dead_code)]
fn _assert_sync() {
    fn s<T: Sync + Send>() {}
    s::<Tcx>();
    s::<crate::program::Program>();
}

#[cfg(test)]
mod typing_tests;

mod callable;

mod selection;
pub use selection::MethodResolution;
