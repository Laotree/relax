//! Type properties on the shared query engine. Tcx owns tables; providers borrow the
//! collected program. rustc_middle/src/ty/context.rs:258 and query/plumbing.rs:25.

use crate::solve::SelectionResult;
use crate::fxhash::HashSet;
use crate::program::{DefId, Program};
use crate::query::{Fingerprint, QueryEngine, QueryError, QueryId, QueryTable};
use crate::tcx::{EvalCx, EvalState, Tcx, TypingEnv};
use crate::types::{TyId, TyKind};
use std::hash::{Hash, Hasher};

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct TypeKey { env: TypingEnv, ty: TyId }

struct KeyHasher(crate::sip::Sip128);
impl Hasher for KeyHasher {
    fn write(&mut self, bytes: &[u8]) { self.0.write(bytes); }
    fn finish(&self) -> u64 { self.0.clone().finish128() as u64 }
}

// Interned identities are session-local, as are these tables. Q7 must replace this
// encoding with DefPath/type encodings before persisting any of these nodes.
fn type_fp(key: &TypeKey) -> Fingerprint {
    let mut h = KeyHasher(crate::sip::Sip128::new());
    key.hash(&mut h);
    Fingerprint(h.0.finish128())
}
fn bool_fp(value: &bool) -> Fingerprint { Fingerprint::from_bytes(&[*value as u8]) }
fn ty_fp(value: &TyId) -> Fingerprint { Fingerprint::from_bytes(&value.0.to_le_bytes()) }

pub struct QueryCx {
    engine: QueryEngine,
    drop: QueryTable<TypeKey, bool>,
    freeze: QueryTable<TypeKey, bool>,
    normalize: QueryTable<TypeKey, TyId>,
}

impl QueryCx {
    pub fn new() -> Self {
        let mut engine = QueryEngine::new();
        engine.register_input(0, 0, Fingerprint::from_bytes(b"collected program")).unwrap();
        engine.set_input(0, 0, Fingerprint::from_bytes(&0u64.to_le_bytes())).unwrap();
        Self { engine, drop: QueryTable::new(1, type_fp, bool_fp), freeze: QueryTable::new(2, type_fp, bool_fp), normalize: QueryTable::new(3, type_fp, ty_fp) }
    }

    /// Publish only under the same exclusive Tcx borrow that edits the tables.
    /// Q3 replaces this coarse collected-program input with per-item inputs.
    pub(crate) fn collected(&mut self, epoch: u64) {
        self.engine.set_input(0, 0, Fingerprint::from_bytes(&epoch.to_le_bytes())).unwrap();
    }
}

struct Providers<'a> { tcx: &'a Tcx, prog: &'a Program }
impl Providers<'_> {
    fn force(&self, id: QueryId) -> Result<(), QueryError> {
        let q = &self.tcx.queries;
        match id.kind {
            1 => { self.needs_drop(q.drop.key(id.key).ok_or(QueryError::MissingQuery(id))?)?; }
            2 => { self.is_freeze(q.freeze.key(id.key).ok_or(QueryError::MissingQuery(id))?)?; }
            3 => { self.normalize_erasing_regions(q.normalize.key(id.key).ok_or(QueryError::MissingQuery(id))?)?; }
            _ => return Err(QueryError::MissingQuery(id)),
        }
        Ok(())
    }

    fn normalize_erasing_regions(&self, key: TypeKey) -> Result<TyId, QueryError> {
        let q = &self.tcx.queries;
        q.normalize.get(&q.engine, key, &mut |key| {
            q.engine.input(0, 0)?;
            let state = EvalState::new();
            let cx = EvalCx::new(self.prog, key.env, &state);
            Ok(self.tcx.tys.erase_regions(self.tcx.normalize(&cx, self.prog, key.ty)))
        }, &|id| self.force(id))
    }

    /// rustc_ty_utils/src/needs_drop.rs:108,193,236,354: traverse components,
    /// normalize fields, and stop at destructors. A seen set belongs to this walk,
    /// never a provisional false entry in the query cache.
    fn needs_drop(&self, key: TypeKey) -> Result<bool, QueryError> {
        let q = &self.tcx.queries;
        q.drop.get(&q.engine, key, &mut |key| {
            q.engine.input(0, 0)?;
            let tcx = self.tcx;
            let state = EvalState::new();
            let cx = EvalCx::new(self.prog, key.env, &state);
            let mut todo = vec![key.ty];
            let mut seen = HashSet::default();
            while let Some(ty) = todo.pop() {
                let ty = tcx.normalize_erasing_regions(self.prog, key.env, ty);
                if !seen.insert(ty) { continue; }
                if tcx.is_coroutine(ty) { return Ok(true); }
                match tcx.tys.kind(ty) {
                    TyKind::Adt(d, args, _) => {
                        let adt = &tcx.adts[d];
                        if adt.is_manually_drop() || adt.is_phantom_data() { continue; }
                        if adt.is_box() || tcx.adt_destructor(*d).is_some() { return Ok(true); }
                        if adt.is_union() { continue; }
                        for (vi, v) in adt.variants.iter().enumerate() {
                            for fi in 0..v.fields.len() {
                                todo.push(tcx.field_ty(self.prog, key.env, *d, vi as u32, fi as u32, args));
                            }
                        }
                    }
                    TyKind::Tuple(fields) => todo.extend_from_slice(fields),
                    TyKind::Array(elem, len) => { if *len != 0 { todo.push(*elem); } }
                    TyKind::Slice(elem) | TyKind::Closure(_, _, _, elem, _) => todo.push(*elem),
                    TyKind::Param(_) | TyKind::Assoc(..) | TyKind::Opaque(..) => {
                        let copy = tcx.lang_items.get(crate::lang_items::LangItem::Copy);
                        if !copy.is_some_and(|td| matches!(tcx.select_trait(&cx, td, ty, &[]), SelectionResult::Ok(_))) { return Ok(true); }
                    }
                    TyKind::Dyn(..) | TyKind::Error | TyKind::Infer(_) => return Ok(true),
                    _ => {}
                }
            }
            Ok(false)
        }, &|id| self.force(id))
    }

    /// Structural Freeze until T5: rustc_middle/src/ty/util.rs:1144 and
    /// library/core/src/marker.rs:904-917 (negative UnsafeCell, pointer/PhantomData impls).
    fn is_freeze(&self, key: TypeKey) -> Result<bool, QueryError> {
        let q = &self.tcx.queries;
        q.freeze.get(&q.engine, key, &mut |key| {
            q.engine.input(0, 0)?;
            let tcx = self.tcx;
            let mut todo = vec![key.ty];
            let mut seen = HashSet::default();
            while let Some(ty) = todo.pop() {
                let ty = tcx.normalize_erasing_regions(self.prog, key.env, ty);
                if !seen.insert(ty) { continue; }
                match tcx.tys.kind(ty) {
                    TyKind::Adt(d, args, _) => {
                        let adt = &tcx.adts[d];
                        if adt.is_unsafe_cell() { return Ok(false); }
                        if adt.is_phantom_data() { continue; }
                        for (vi, v) in adt.variants.iter().enumerate() {
                            for fi in 0..v.fields.len() {
                                todo.push(tcx.field_ty(self.prog, key.env, *d, vi as u32, fi as u32, args));
                            }
                        }
                    }
                    TyKind::Tuple(fields) => todo.extend_from_slice(fields),
                    TyKind::Array(elem, _) | TyKind::Slice(elem) => todo.push(*elem),
                    TyKind::Closure(_, _, _, up, _) => {
                        if tcx.is_coroutine(ty) { return Ok(false); }
                        todo.push(*up);
                    }
                    TyKind::Int(_) | TyKind::Float(_) | TyKind::Bool | TyKind::Char | TyKind::Never | TyKind::Str
                    | TyKind::Ref(..) | TyKind::Ptr(..) | TyKind::FnPtr(..) | TyKind::FnDef(..) => {}
                    _ => return Ok(false),
                }
            }
            Ok(true)
        }, &|id| self.force(id))
    }
}

impl Tcx {
    pub fn needs_drop(&self, prog: &Program, env: TypingEnv, ty: TyId) -> bool {
        Providers { tcx: self, prog }.needs_drop(TypeKey { env, ty }).expect("needs_drop query")
    }

    pub fn is_freeze(&self, prog: &Program, env: TypingEnv, ty: TyId) -> bool {
        Providers { tcx: self, prog }.is_freeze(TypeKey { env, ty }).expect("is_freeze query")
    }

    /// rustc_middle/src/ty/mod.rs:1449: field declaration + plain instantiation.
    /// Query providers reading declarations must first read the collected-program
    /// input, until Q3 supplies rustc's per-item type_of query.
    pub fn field_ty(&self, prog: &Program, env: TypingEnv, adt: DefId, variant: u32, field: u32, args: &[TyId]) -> TyId {
        let decl = self.adts[&adt].variants[variant as usize].fields[field as usize].ty;
        self.normalize_erasing_regions(prog, env, self.tys.subst(decl, args))
    }

    /// rustc_middle/src/ty/normalize_erasing_regions.rs:41,63,196: erase before
    /// keying; alias-free types bypass the query. may_project includes projections
    /// inside closures and trait objects, which has_assoc deliberately omits.
    pub fn normalize_erasing_regions(&self, prog: &Program, env: TypingEnv, ty: TyId) -> TyId {
        let ty = self.tys.erase_regions(ty);
        if !self.tys.may_project(ty) && !self.tys.has_opaque(ty) { return ty; }
        Providers { tcx: self, prog }.normalize_erasing_regions(TypeKey { env, ty }).expect("normalize_erasing_regions query")
    }

}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tcx::{ParamEnv, TypingMode};
    use crate::types::RegionArgsId;

    fn program(source: &[u8]) -> (Program, Tcx) {
        let dir = std::env::temp_dir().join(format!("relax-type-queries-{}-{}", std::process::id(), std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos()));
        std::fs::create_dir(&dir).unwrap();
        let path = dir.join("lib.rs");
        std::fs::write(&path, source).unwrap();
        let mut prog = Program::new(&std::sync::Arc::new(crate::Session::default()));
        prog.load_crate("query_tests", path.to_str().unwrap(), 2021, crate::cfg::CfgSet::host(&prog.session, &[]), Vec::new()).unwrap();
        let mut tcx = Tcx::new();
        tcx.collect(&prog);
        tcx.impl_projection_ready = true;
        tcx.publish_collected();
        std::fs::remove_file(path).unwrap();
        std::fs::remove_dir(dir).unwrap();
        assert!(tcx.errors.is_empty(), "{:?}", tcx.errors);
        (prog, tcx)
    }
    fn named(prog: &Program, name: &str) -> DefId {
        for i in 0..prog.defs.len() {
            let d = DefId(i as u32);
            if prog.name(d) == name { return d; }
        }
        panic!("missing {name}")
    }
    fn adt(prog: &Program, tcx: &Tcx, name: &str, args: Vec<TyId>) -> TyId {
        tcx.tys.intern(TyKind::Adt(named(prog, name), args, RegionArgsId::EMPTY))
    }
    #[test]
    fn drop_components_and_freeze() {
        let (prog, tcx) = program(br#"#![no_std]
            #[lang = "drop"] trait Drop { fn drop(&mut self); }
            #[lang = "copy"] trait Copy {}
            #[lang = "owned_box"] struct Heap<T>(*mut T);
            #[lang = "manually_drop"] struct Manual<T>(T);
            #[lang = "phantom_data"] struct Phantom<T>;
            #[lang = "unsafe_cell"] struct Cell<T>(T);
            struct D; impl Drop for D { fn drop(&mut self) {} }
            struct Node { next: Heap<Node> }
            struct Plain { next: *mut Plain }
            union U { d: D }
        "#);
        let env = TypingEnv::fully_monomorphized();
        let d = adt(&prog, &tcx, "D", vec![]);
        for name in ["D", "Node"] { assert!(tcx.needs_drop(&prog, env, adt(&prog, &tcx, name, vec![]))); }
        for name in ["Plain", "U"] { assert!(!tcx.needs_drop(&prog, env, adt(&prog, &tcx, name, vec![]))); }
        for name in ["Manual", "Phantom"] { assert!(!tcx.needs_drop(&prog, env, adt(&prog, &tcx, name, vec![d]))); }
        assert!(!tcx.needs_drop(&prog, env, tcx.tys.intern(TyKind::Array(d, 0))));
        assert!(tcx.needs_drop(&prog, env, tcx.tys.intern(TyKind::Array(d, 2))));
        assert!(tcx.needs_drop(&prog, env, tcx.tys.intern(TyKind::Slice(d))));
        let cell = adt(&prog, &tcx, "Cell", vec![tcx.tys.bool_]);
        assert!(!tcx.is_freeze(&prog, env, cell));
        assert!(!tcx.is_freeze(&prog, env, tcx.tys.intern(TyKind::Array(cell, 0))));
        assert!(tcx.is_freeze(&prog, env, adt(&prog, &tcx, "Phantom", vec![cell])));
        assert!(tcx.is_freeze(&prog, env, tcx.tys.intern(TyKind::Ptr(false, cell))));
        assert!(tcx.is_freeze(&prog, env, adt(&prog, &tcx, "Node", vec![])));
        let sig = tcx.tys.intern(TyKind::FnPtr(vec![], tcx.tys.unit, crate::types::FnHeader::RUST, 0));
        let owner = tcx.tys.intern(TyKind::FnDef(named(&prog, "drop"), vec![], RegionArgsId::EMPTY));
        let up = tcx.tys.intern(TyKind::Tuple(vec![d, cell]));
        let closure = tcx.tys.intern(TyKind::Closure(0, 0, sig, up, owner));
        assert!(tcx.needs_drop(&prog, env, closure));
        assert!(!tcx.is_freeze(&prog, env, closure));
    }
    #[test]
    fn polymorphic_copy_bounds() {
        let (prog, tcx) = program(br#"#![no_std]
            #[lang = "copy"] trait Copy {}
            trait Tr { type A: Copy; }
            struct S<T: Tr> { value: T::A }
        "#);
        let param = tcx.tys.intern(TyKind::Param(0));
        let mut predicates = ParamEnv::default();
        predicates.preds.push((param, named(&prog, "Copy"), vec![]));
        for mode in [TypingMode::Analysis { defining_opaques: Default::default() }, TypingMode::Borrowck, TypingMode::PostAnalysis] {
            let empty = TypingEnv { param_env: Default::default(), mode };
            assert!(tcx.needs_drop(&prog, empty, param));
            let env = TypingEnv { param_env: tcx.intern_param_env(predicates.clone()), mode };
            assert!(!tcx.needs_drop(&prog, env, param));
            let projection = tcx.field_ty(&prog, empty, named(&prog, "S"), 0, 0, &[param]);
            assert!(!tcx.needs_drop(&prog, empty, projection), "associated Copy bound in {mode:?}");
        }
    }
    #[test]
    fn collected_input_invalidates_fields_and_properties() {
        let (prog, mut tcx) = program(br#"#![no_std]
            #[lang = "drop"] trait Drop { fn drop(&mut self); }
            #[lang = "unsafe_cell"] struct Cell<T>(T);
            struct D; impl Drop for D { fn drop(&mut self) {} }
            struct S { value: bool }
        "#);
        let env = TypingEnv::fully_monomorphized();
        let d = adt(&prog, &tcx, "D", vec![]);
        let cell = adt(&prog, &tcx, "Cell", vec![d]);
        let sid = named(&prog, "S");
        let ty = adt(&prog, &tcx, "S", vec![]);
        let key = TypeKey { env, ty };
        assert!(!tcx.needs_drop(&prog, env, ty));
        assert!(tcx.is_freeze(&prog, env, ty));
        let drop_id = tcx.queries.drop.query_id(&key).unwrap();
        assert_eq!(tcx.queries.engine.dependencies(drop_id), vec![QueryId { kind: 0, key: 0 }]);
        assert!(tcx.queries.normalize.query_id(&TypeKey { env, ty: tcx.tys.bool_ }).is_none());
        for next in [cell, tcx.tys.bool_] {
            tcx.adts.get_mut(&sid).unwrap().variants[0].fields[0].ty = next;
            tcx.publish_collected();
            assert_eq!(tcx.field_ty(&prog, env, sid, 0, 0, &[]), next);
            assert_eq!(tcx.needs_drop(&prog, env, ty), next == cell);
            assert_eq!(tcx.is_freeze(&prog, env, ty), next != cell);
        }
    }

    #[test]
    fn check_session_invalidation_updates_type_queries() {
        let (prog, mut tcx) = program(br#"#![no_std]
            #[lang = "drop"] trait Drop { fn drop(&mut self); }
            struct D; impl Drop for D { fn drop(&mut self) {} }
            struct S { value: bool }
            struct Removed;
        "#);
        let env = TypingEnv::fully_monomorphized();
        let sid = named(&prog, "S");
        let ty = adt(&prog, &tcx, "S", vec![]);
        let droppable = adt(&prog, &tcx, "D", vec![]);
        assert!(!tcx.needs_drop(&prog, env, ty));
        tcx.adts.get_mut(&sid).unwrap().variants[0].fields[0].ty = droppable;
        tcx.invalidate_check(&[]);
        assert!(tcx.needs_drop(&prog, env, ty));
        tcx.adts.get_mut(&sid).unwrap().variants[0].fields[0].ty = tcx.tys.bool_;
        tcx.invalidate_check(&[named(&prog, "Removed")]);
        assert!(!tcx.needs_drop(&prog, env, ty));
    }

    #[test]
    fn fields_only_query_aliases_after_substitution_and_erasure() {
        let (prog, tcx) = program(br#"#![no_std]
            trait Tr { type A; }
            struct S<T> { first: T, second: T }
        "#);
        let env = TypingEnv::fully_monomorphized();
        let sid = named(&prog, "S");
        let region = tcx.tys.intern_region(crate::types::RegionKind::ReStatic);
        let reference = tcx.tys.intern(TyKind::Ref(false, tcx.tys.bool_, region));
        let erased = tcx.tys.erase_regions(reference);
        assert_eq!(tcx.field_ty(&prog, env, sid, 0, 0, &[reference]), erased);
        assert!(tcx.queries.normalize.query_id(&TypeKey { env, ty: erased }).is_none());

        let projection = tcx.tys.intern(TyKind::Assoc(named(&prog, "A"), vec![reference], RegionArgsId::EMPTY));
        let erased_projection = tcx.tys.erase_regions(projection);
        let mut predicates = ParamEnv::default();
        predicates.eqs.push((erased_projection, tcx.tys.char_));
        let env = TypingEnv { param_env: tcx.intern_param_env(predicates), mode: TypingMode::Borrowck };
        for field in 0..2 {
            assert_eq!(tcx.field_ty(&prog, env, sid, 0, field, &[projection]), tcx.tys.char_);
        }
        assert!(tcx.queries.normalize.query_id(&TypeKey { env, ty: projection }).is_none());
        let id = tcx.queries.normalize.query_id(&TypeKey { env, ty: erased_projection }).unwrap();
        assert_eq!(tcx.queries.engine.dependencies(id), vec![QueryId { kind: 0, key: 0 }]);
        // has_assoc excludes closure captures; the normalization fast path must not.
        let sig = tcx.tys.intern(TyKind::FnPtr(vec![], tcx.tys.unit, crate::types::FnHeader::RUST, 0));
        let closure = tcx.tys.intern(TyKind::Closure(0, 0, sig, projection, tcx.tys.unit));
        let normalized = tcx.normalize_erasing_regions(&prog, env, closure);
        assert!(matches!(tcx.tys.kind(normalized), TyKind::Closure(_, _, _, up, _) if *up == tcx.tys.char_));
    }

    #[test]
    fn collected_input_invalidates_alias_normalization() {
        let (prog, mut tcx) = program(br#"#![no_std]
            #[lang = "drop"] trait Drop { fn drop(&mut self); }
            struct D; impl Drop for D { fn drop(&mut self) {} }
            trait Tr { type A; }
            struct S<T> { value: T }
            fn owner() {}
        "#);
        let env = TypingEnv::fully_monomorphized();
        let owner = named(&prog, "owner");
        let assoc = named(&prog, "A");
        let param = tcx.tys.intern(TyKind::Param(0));
        let opaque = tcx.tys.intern(TyKind::Opaque(owner, 0, vec![param], RegionArgsId::EMPTY));
        let projection = tcx.tys.intern(TyKind::Assoc(assoc, vec![opaque], RegionArgsId::EMPTY));
        let ty = adt(&prog, &tcx, "S", vec![projection]);
        let droppable = adt(&prog, &tcx, "D", vec![]);
        for next in [tcx.tys.bool_, droppable, tcx.tys.bool_] {
            let mut decl = crate::tcx::OpaqueDecl::default();
            decl.bindings.push((assoc, vec![], next));
            tcx.opaques.insert((owner, 0), decl);
            tcx.publish_collected();
            assert_eq!(tcx.field_ty(&prog, env, named(&prog, "S"), 0, 0, &[projection]), next);
            assert_eq!(tcx.needs_drop(&prog, env, ty), next == droppable);
            let id = tcx.queries.normalize.query_id(&TypeKey { env, ty: projection }).unwrap();
            assert_eq!(tcx.queries.engine.dependencies(id), vec![QueryId { kind: 0, key: 0 }]);
            let drop_id = tcx.queries.drop.query_id(&TypeKey { env, ty }).unwrap();
            let normalized_id = tcx.queries.normalize.query_id(&TypeKey { env, ty }).unwrap();
            assert!(tcx.queries.engine.dependencies(drop_id).contains(&normalized_id));
        }
    }

    #[test]
    fn unresolved_components_and_coroutines() {
        let (prog, tcx) = program(br#"#![no_std]
            #[lang = "copy"] trait Copy {}
            #[lang = "phantom_data"] struct Phantom<T>;
            trait Tr { type A; }
            fn owner() {}
        "#);
        let env = TypingEnv::fully_monomorphized();
        let param = tcx.tys.intern(TyKind::Param(0));
        let projection = tcx.tys.intern(TyKind::Assoc(named(&prog, "A"), vec![param], RegionArgsId::EMPTY));
        let opaque = tcx.tys.intern(TyKind::Opaque(named(&prog, "owner"), 0, vec![], RegionArgsId::EMPTY));
        for ty in [param, projection, opaque] {
            assert!(tcx.needs_drop(&prog, env, ty));
            assert!(!tcx.is_freeze(&prog, env, ty));
        }
        let len = crate::types::LEN_TY | param.0 as u64;
        assert!(tcx.needs_drop(&prog, env, tcx.tys.intern(TyKind::Array(param, len))));
        let phantom = adt(&prog, &tcx, "Phantom", vec![param]);
        assert!(!tcx.needs_drop(&prog, env, tcx.tys.intern(TyKind::Array(phantom, len))));
        let sig = tcx.tys.intern(TyKind::FnPtr(vec![], tcx.tys.unit, crate::types::FnHeader::RUST, 0));
        let owner = tcx.tys.intern(TyKind::FnDef(named(&prog, "owner"), vec![], RegionArgsId::EMPTY));
        tcx.coroutines.insert((0, 1), ());
        let coroutine = tcx.tys.intern(TyKind::Closure(0, 1, sig, tcx.tys.unit, owner));
        assert!(tcx.needs_drop(&prog, env, coroutine));
        assert!(!tcx.is_freeze(&prog, env, coroutine));
    }

}
