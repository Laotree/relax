//! The interner's IDs are part of a collected graph, including its resolved array lengths.
//! Restore entries verbatim instead of interning them again (which would change those IDs).
use super::*;
use crate::crate_image::{Codec, Decode};
use std::sync::atomic::Ordering;

crate::collected_id!(UniverseIndex, BoundVar);

struct Semantic {
    types: *const Types,
    hashes: Vec<Option<u128>>,
}
thread_local! {
    static SEMANTIC: std::cell::RefCell<Option<Semantic>> = const { std::cell::RefCell::new(None) };
}
struct SemanticGuard(Option<Semantic>);
impl Drop for SemanticGuard {
    fn drop(&mut self) { SEMANTIC.with(|s| { s.replace(self.0.take()); }); }
}
impl Types {
    /// Verification-only encoding uses structural identities, including lifetimes and
    /// tagged const-generic array lengths. Parallel collection assigns nondeterministic IDs.
    pub fn with_semantic_ids<R>(&self, f: impl FnOnce() -> R) -> R {
        let _guard = SemanticGuard(SEMANTIC.with(|s| s.replace(Some(Semantic {
            types: self, hashes: vec![None; self.len()],
        }))));
        f()
    }
}
impl Codec for TyId {
    fn put(&self, w: &mut Vec<u8>) {
        // Cache publication can run from atexit, after verification's TLS was destroyed.
        let semantic = SEMANTIC.try_with(|s| s.borrow().as_ref().map(|s| (s.types, s.hashes[self.0 as usize]))).ok().flatten();
        let Some((types, hash)) = semantic else { self.0.put(w); return; };
        let hash = hash.unwrap_or_else(|| {
            // The scoped guard holds a borrow of Types for every use of this pointer.
            let types = unsafe { &*types };
            let mut bytes = Vec::new();
            match types.kind(*self) {
                TyKind::Array(t, n) => {
                    7u8.put(&mut bytes); t.put(&mut bytes);
                    len_ty(*n).is_some().put(&mut bytes);
                    if let Some(id) = len_ty(*n) { id.put(&mut bytes); } else { n.put(&mut bytes); }
                }
                kind => kind.put(&mut bytes),
            }
            let e = types.entry(*self);
            e.flags.put(&mut bytes); e.outer_exclusive_binder.put(&mut bytes); e.depth.put(&mut bytes);
            let mut h = crate::sip::Sip128::new(); h.write(&bytes); let hash = h.finish128();
            SEMANTIC.with(|s| s.borrow_mut().as_mut().unwrap().hashes[self.0 as usize] = Some(hash));
            hash
        });
        hash.put(w);
    }
    fn get(r: &mut Decode<'_>) -> Option<Self> { Some(Self(u32::get(r)?)) }
}
impl Codec for RegionId {
    fn put(&self, w: &mut Vec<u8>) {
        let types = SEMANTIC.try_with(|s| s.borrow().as_ref().map(|s| s.types)).ok().flatten();
        if let Some(types) = types { unsafe { &*types }.region_kind(*self).put(w); } else { self.0.put(w); }
    }
    fn get(r: &mut Decode<'_>) -> Option<Self> { Some(Self(u32::get(r)?)) }
}
impl Codec for RegionArgsId {
    fn put(&self, w: &mut Vec<u8>) {
        let types = SEMANTIC.try_with(|s| s.borrow().as_ref().map(|s| s.types)).ok().flatten();
        if let Some(types) = types { unsafe { &*types }.region_args(*self).put(w); } else { self.0.put(w); }
    }
    fn get(r: &mut Decode<'_>) -> Option<Self> { Some(Self(u32::get(r)?)) }
}
crate::collected_enum!(BoundTyKind; 0 => Anon, 1 => Param(d));
crate::collected_fields!(BoundTy, var, kind);
crate::collected_fields!(PlaceholderType, universe, bound);
crate::collected_enum!(LateParamKind; 0 => Anon(n), 1 => Named(d), 2 => ClosureEnv);
crate::collected_enum!(Safety; 0 => Safe, 1 => Unsafe);
crate::collected_enum!(Abi; 0 => Rust, 1 => RustCall, 2 => C, 3 => CUnwind,
    4 => System, 5 => SystemUnwind, 6 => RelaxIntrinsic);
crate::collected_fields!(FnHeader, safety, abi, c_variadic);
impl<T: Codec> Codec for DynList<T> {
    fn put(&self, w: &mut Vec<u8>) {
        self.len().put(w);
        for v in self.iter() { v.put(w); }
    }
    fn get(r: &mut Decode<'_>) -> Option<Self> { Some(Vec::<T>::get(r)?.into()) }
}
crate::collected_enum!(TyKind;
    0 => Bool, 1 => Char, 2 => Str, 3 => Int(p), 4 => Float(p), 5 => Never,
    6 => Tuple(v), 7 => Array(t,n), 8 => Slice(t), 9 => Ref(m,t,r), 10 => Ptr(m,t),
    11 => Adt(d,v,r), 12 => FnPtr(v,t,h,n), 13 => FnDef(d,v,r), 14 => Param(n),
    15 => Infer(n), 16 => Closure(f,e,s,c,o), 17 => Assoc(d,v,r),
    18 => Dyn(d,v,b,a,r,n,auto), 19 => ConstVal(n), 20 => Opaque(d,n,v,r),
    21 => Error, 22 => Bound(n,b), 23 => Placeholder(p));
impl Codec for RegionScope {
    fn put(&self, w: &mut Vec<u8>) {
        match self {
            Self::Item(d) => { 0u8.put(w); d.put(w); }
            Self::Closure { owner, expr } => { 1u8.put(w); owner.put(w); expr.put(w); }
        }
    }
    fn get(r: &mut Decode<'_>) -> Option<Self> {
        Some(match u8::get(r)? {
            0 => Self::Item(Codec::get(r)?),
            1 => Self::Closure { owner: Codec::get(r)?, expr: Codec::get(r)? },
            _ => return None,
        })
    }
}
impl Codec for RegionKind {
    fn put(&self, w: &mut Vec<u8>) {
        match self {
            Self::ReEarlyParam(n) => { 0u8.put(w); n.put(w); }
            Self::ReBound(d,v) => { 1u8.put(w); d.put(w); v.put(w); }
            Self::ReLateParam(s,k) => { 2u8.put(w); s.put(w); k.put(w); }
            Self::ReStatic => 3u8.put(w),
            Self::ReVar(n) => { 4u8.put(w); n.put(w); }
            Self::RePlaceholder { universe, var } => { 5u8.put(w); universe.put(w); var.put(w); }
            Self::ReErased => 6u8.put(w),
            Self::ReError => 7u8.put(w),
        }
    }
    fn get(r: &mut Decode<'_>) -> Option<Self> {
        Some(match u8::get(r)? {
            0 => Self::ReEarlyParam(Codec::get(r)?),
            1 => Self::ReBound(Codec::get(r)?, Codec::get(r)?),
            2 => Self::ReLateParam(Codec::get(r)?, Codec::get(r)?),
            3 => Self::ReStatic,
            4 => Self::ReVar(Codec::get(r)?),
            5 => Self::RePlaceholder { universe: Codec::get(r)?, var: Codec::get(r)? },
            6 => Self::ReErased,
            7 => Self::ReError,
            _ => return None,
        })
    }
}
crate::collected_fields!(Entry, kind, hash, next, flags, outer_exclusive_binder, depth, erased, inference_erased);

#[repr(C)]
#[derive(Clone, Copy)]
struct TypeRow {
    hash: u64,
    offset: u32,
    bytes: u32,
    next: u32,
    flags: u32,
    binder: u32,
    erased: u32,
    inference_erased: u32,
    depth: u16,
    padding: u16,
}
// Same-build, position-independent metadata; the kind uses the checked tagged codec.
unsafe impl crate::image::Pod for TypeRow {}

pub(super) struct MappedTypes {
    rows: &'static [TypeRow],
    kinds: &'static [u8],
    /// decoded on first use: a warm boot touches a few thousand of the image's types
    ready: crate::collected::LazySlots<Entry>,
}
impl MappedTypes {
    pub(super) fn len(&self) -> usize { self.rows.len() }
    pub(super) fn entry(&self, i: usize) -> &Entry {
        self.ready.get_or_init(i, || {
            let r = &self.rows[i];
            let bytes = &self.kinds[r.offset as usize..r.offset as usize + r.bytes as usize];
            Entry {
                kind: crate::crate_image::decode(bytes).expect("checksummed collected type"),
                hash: r.hash, next: r.next, flags: r.flags,
                outer_exclusive_binder: r.binder, depth: r.depth,
                erased: TyId(r.erased), inference_erased: TyId(r.inference_erased),
            }
        })
    }
}

impl Types {
    pub fn collected_image(&self) -> Option<Vec<u8>> {
        Some(self.collected_writer()?.finish())
    }

    pub fn collected_writer(&self) -> Option<crate::image::Writer<'_>> {
        let mut meta = Vec::new();
        let regions = self.regions.lock().unwrap_or_else(|e| e.into_inner());
        regions.kinds.put(&mut meta); regions.args.put(&mut meta);
        drop(regions);
        self.free_regions.load(Ordering::Relaxed).put(&mut meta);
        for t in [self.unit, self.bool_, self.char_, self.str_, self.never, self.error,
            self.i32_, self.i64_, self.u8_, self.u32_, self.u64_, self.usize_, self.isize_,
            self.f32_, self.f64_, self.str_ref] { t.put(&mut meta); }
        let (mapped_rows, mapped_kinds) = self.image.as_ref().map_or((&[][..], &[][..]), |image| (image.rows, image.kinds));
        let mut rows = Vec::with_capacity(self.len() - mapped_rows.len());
        let mut kinds = Vec::new();
        for i in mapped_rows.len()..self.len() {
            let e = self.entry(TyId(i as u32));
            let offset = mapped_kinds.len() + kinds.len();
            e.kind.put(&mut kinds);
            rows.push(TypeRow { hash: e.hash, offset: u32::try_from(offset).expect("type image offset"),
                bytes: u32::try_from(mapped_kinds.len() + kinds.len() - offset).expect("type image length"),
                next: e.next, flags: e.flags, binder: e.outer_exclusive_binder,
                erased: e.erased.0, inference_erased: e.inference_erased.0, depth: e.depth, padding: 0 });
        }
        let n = mapped_rows.len() + rows.len();
        if !mapped_rows.iter().chain(&rows).all(|r|
            (r.offset as usize).checked_add(r.bytes as usize).is_some_and(|end| end <= mapped_kinds.len() + kinds.len())
            && r.next as usize <= n && (r.erased as usize) < n
            && (r.inference_erased as usize) < n) { return None; }
        let buckets: Vec<u32> = self.buckets.iter().enumerate().filter_map(|(i, head)| {
            let head = head.load(Ordering::Relaxed);
            (head != 0).then_some([i as u32, head])
        }).flatten().collect();
        let mut image = crate::image::Writer::default();
        image.add_bytes(0, meta); image.add_mapped_prefix(1, mapped_rows, &rows);
        image.add_chunks(2, vec![crate::image::Chunk::Mapped(mapped_kinds), crate::image::Chunk::Owned(kinds)]);
        image.add_owned(3, &buckets);
        Some(image)
    }

    pub fn restore_collected(bytes: &'static [u8]) -> Option<Self> {
        let image = crate::image::Reader::new(bytes)?;
        let rows: &'static [TypeRow] = image.slice(1, 1)?;
        let kinds = image.bytes(2, 2)?;
        let buckets: &'static [u32] = image.slice(3, 3)?;
        let n = rows.len();
        // The checksummed, same-build snapshot is constructed from valid interner entries.
        // Row relationships were certified at publication; demand decoding still uses
        // bounds-checked slices, without a pass over every type on each warm boot.
        if n > MAX_CHUNKS * CHUNK || buckets.len() % 2 != 0 { return None; }
        let mut r = Decode::new(image.bytes(0, 0)?);
        let region_kinds: Vec<RegionKind> = Codec::get(&mut r)?;
        let args: Vec<std::sync::Arc<[RegionId]>> = Codec::get(&mut r)?;
        // Zero is the implicit erased/empty value, not an element of either arena.
        if region_kinds.contains(&RegionKind::ReErased) || args.iter().any(|a| a.is_empty())
            || args.iter().flat_map(|a| a.iter()).any(|id| id.0 as usize > region_kinds.len()) { return None; }
        let mut t = Types::new();
        if n < t.len() { return None; }
        *t.regions.get_mut().ok()? = Regions { kinds: region_kinds, args, unindexed: true, ..Default::default() };
        *t.free_regions.get_mut() = bool::get(&mut r)?;
        for dst in [&mut t.unit, &mut t.bool_, &mut t.char_, &mut t.str_, &mut t.never,
            &mut t.error, &mut t.i32_, &mut t.i64_, &mut t.u8_, &mut t.u32_, &mut t.u64_,
            &mut t.usize_, &mut t.isize_, &mut t.f32_, &mut t.f64_, &mut t.str_ref] {
            *dst = Codec::get(&mut r)?;
            if dst.0 as usize >= n { return None; }
        }
        if !r.bytes.is_empty() { return None; }
        for b in &mut t.buckets { *b.get_mut() = 0; }
        for pair in buckets.chunks_exact(2) {
            if pair[0] as usize >= t.buckets.len() || pair[1] as usize > n { return None; }
            *t.buckets[pair[0] as usize].get_mut() = pair[1];
        }
        // Retire new()'s primitive arena. Mapped IDs need no Entry allocations until used;
        // subsequent interning starts after the image and retains the same append-only IDs.
        let first = *t.chunks[0].get_mut();
        for i in 0..t.len() { unsafe { std::ptr::drop_in_place(first.add(i)); } }
        unsafe { std::alloc::dealloc(first.cast(), std::alloc::Layout::array::<Entry>(CHUNK).ok()?); }
        *t.chunks[0].get_mut() = std::ptr::null_mut();
        t.image = Some(MappedTypes { rows, kinds, ready: crate::collected::LazySlots::new(n) });
        *t.len.get_mut() = n as u32;
        Some(t)
    }
}
