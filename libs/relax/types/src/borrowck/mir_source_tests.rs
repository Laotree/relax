//! The whole MIR borrowck pipeline (build, signatures, type check, region inference, checks) on small
//! Rust sources over Relax's real core and alloc: the repros of what real crates showed.
use crate::program::{DefId, Program};
use crate::tcx::{EvalCx, EvalState, Tcx, TypingEnv};

/// Error codes (or messages) and unchecked reasons of every fn of `source`.
pub(super) fn borrowck_source(source: &str) -> (Vec<String>, Vec<String>) {
    let sess = &std::sync::Arc::new(crate::Session::default());
    let mut prog = Program::new(sess);
    let std_dir = concat!(env!("CARGO_MANIFEST_DIR"), "/../compiler/std");
    prog.load_crate("core", &format!("{std_dir}/core/lib.rs"), 2021, crate::cfg::CfgSet::host(sess, &[]), Vec::new()).unwrap();
    let core = prog.syms.intern("core");
    let alloc = prog.load_crate("alloc", &format!("{std_dir}/alloc/lib.rs"), 2021, crate::cfg::CfgSet::host(sess, &[]), vec![(core, 0)]).unwrap();
    let alloc_name = prog.syms.intern("alloc");
    static N: std::sync::atomic::AtomicU32 = std::sync::atomic::AtomicU32::new(0);
    let dir = std::env::temp_dir().join(format!("relax-mirsrc-{}-{}", std::process::id(), N.fetch_add(1, std::sync::atomic::Ordering::Relaxed)));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join("lib.rs");
    std::fs::write(&path, source).unwrap();
    let user = prog.load_crate("repro", path.to_str().unwrap(), 2021, crate::cfg::CfgSet::host(sess, &[]), vec![(core, 0), (alloc_name, alloc)]).unwrap();
    std::fs::remove_file(&path).unwrap(); std::fs::remove_dir(&dir).unwrap();
    prog.prelude_crate = Some(0);
    prog.resolve_imports();
    assert!(prog.errors.is_empty(), "{:?}", prog.errors);
    let mut tcx = Tcx::new();
    tcx.collect(&prog);
    assert!(tcx.errors.is_empty(), "{:?}", tcx.errors);
    let (mut errors, mut unchecked) = (vec![], vec![]);
    for owner in crate::borrowck::body::owners(&prog) {
        if prog.def(owner.owner).krate != user { continue; }
        let state = EvalState::new();
        let cx = EvalCx::new(&prog, &tcx, TypingEnv::fully_monomorphized(&prog), &state);
        let body = tcx.typeck(&prog, owner.owner);
        assert!(body.errors.is_empty(), "typeck: {:?}", body.errors);
        if std::env::var_os("PROBE").is_some() { for (ce, c) in body.min_captures.iter() { eprintln!("PROBE closure {ce:?} kind {:?} captures {:?}", c.kind, c.captures.iter().map(|c| (c.info.kind, c.place.projections.len())).collect::<Vec<_>>()); } }
        let v = crate::borrowck::driver::check_root(&cx, &prog, &tcx, &body, None);
        errors.extend(v.errors.iter().map(|e| format!("{} {} {}:{} {:?} {:?}", e.code, e.message, e.line, e.col, e.labels, e.notes)));
        unchecked.extend(v.unchecked);
    }
    let _ = DefId(0);
    (errors, unchecked)
}

#[test]
fn a_reference_to_self_implies_the_outlives_of_its_lifetime_arguments() {
    let (errors, unchecked) = borrowck_source("
        pub struct Line<'a> { data: &'a [u8] }
        pub struct Gradient<'a> { line: Line<'a> }
        pub struct Stops<'a, 'b> { line: &'b Line<'a>, index: u16 }
        impl<'a> Gradient<'a> {
            pub fn stops<'b>(&'b self, index: u16) -> Stops<'a, 'b> { Stops { line: &self.line, index } }
        }");
    assert!(errors.is_empty(), "{errors:?}");
    assert!(unchecked.is_empty(), "{unchecked:?}");
}

#[test]
fn a_closure_returning_a_reborrow_of_its_capture_is_fn_once_when_the_bound_says_so() {
    let (errors, unchecked) = borrowck_source("
        pub fn f(buf: &mut [u8], n: Option<usize>) -> Option<&mut [u8]> { n.and_then(|k| buf.get_mut(..k)) }");
    assert!(unchecked.is_empty(), "{unchecked:?}");
    assert!(errors.is_empty(), "{errors:?}");
}

#[test]
fn a_vec_of_borrows_may_dangle_at_its_drop() {
    let (errors, unchecked) = borrowck_source("
        pub struct Heap { slots: Vec<u32>, other: u32 }
        impl Heap {
            fn set(&mut self, v: u32) { self.other = v; }
            pub fn f(&mut self) {
                let mut kvs = Vec::new();
                for kv in self.slots.iter() { kvs.push(kv); }
                let n = kvs.len() as u32;
                self.set(n);
            }
        }");
    assert!(unchecked.is_empty(), "{unchecked:?}");
    assert!(errors.is_empty(), "{errors:?}");
}

#[test]
fn a_pointer_cast_may_change_the_lifetime_arguments_of_its_pointee() {
    let (errors, unchecked) = borrowck_source("
        pub struct Out<'a> { s: &'a str }
        pub struct Q { text: *mut Out<'static> }
        impl Q { pub fn f(&mut self, out: &mut Out) { self.text = out as *mut Out as *mut Out<'static>; } }");
    assert!(unchecked.is_empty(), "{unchecked:?}");
    assert!(errors.is_empty(), "{errors:?}");
}

#[test]
fn zz_probe_closure_kind() {
    let sess = &std::sync::Arc::new(crate::Session::default());
    let _ = sess;
}

#[test]
fn a_struct_with_a_reference_field_implies_its_inferred_outlives() {
    let (errors, unchecked) = borrowck_source("
        pub struct Image<T> { pixels: Vec<T>, w: usize }
        impl<T> core::ops::Index<usize> for Image<T> { type Output = T; fn index(&self, i: usize) -> &T { &self.pixels[i] } }
        #[derive(Clone, Copy)]
        pub struct Subimage<'a, T> { image: &'a Image<T>, off: usize }
        impl<'a, T> Subimage<'a, T> { pub fn first(&self) -> &T { &self.image[self.off] } }
        impl<'a, T> core::ops::Index<usize> for Subimage<'a, T> { type Output = T; fn index(&self, i: usize) -> &T { &self.image[self.off + i] } }");
    assert!(unchecked.is_empty(), "{unchecked:?}");
    assert!(errors.is_empty(), "{errors:?}");
}

#[test]
fn promoted_constants_are_checked_with_their_own_locations() {
    // `&[..]` and `&5` are promoted: their statements are numbered in the promoted body, not the parent.
    let (errors, unchecked) = borrowck_source("
        pub fn f(x: u32) -> (&'static [u32], &'static u32) { let a: &'static [u32] = &[1, 2, 3, 4, 5, 6]; if x > 1 { (a, &7) } else { (&[9], &8) } }");
    assert!(unchecked.is_empty(), "{unchecked:?}");
    assert!(errors.is_empty(), "{errors:?}");
}

#[test]
fn closure_shapes_map_their_external_regions_to_the_creator() {
    for (name, src) in [
        ("late-bound parameter", "pub fn f(v: &[&str]) -> usize { v.iter().map(|s| s.len()).sum() }"),
        ("captured reference returned", "pub fn f<'a>(x: &'a str) -> impl Fn() -> &'a str { move || x }"),
        ("annotated parameter", "pub fn f() -> usize { let g = |s: &str| s.len(); g(\"a\") + g(\"bc\") }"),
        ("nested", "pub fn f(v: &[&str]) -> usize { v.iter().map(|s| { let h = |t: &str| t.len(); h(s) }).sum() }"),
    ] {
        let (errors, unchecked) = borrowck_source(src);
        assert!(unchecked.is_empty(), "{name}: {unchecked:?}");
        assert!(errors.is_empty(), "{name}: {errors:?}");
    }
}
