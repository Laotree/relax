//! Values the JIT computes at run time are rustc's: each case runs a small program's function
//! (writing its results to `out`) and compares them with what rustc's build gives.
//!
//! `cfg!` is the literal the crate's cfg gives (rustc_builtin_macros cfg.rs expand_cfg) wherever
//! it is read: in run-time code, and in the consts the type layer evaluates for it (an array
//! length, a const generic argument, a constant pattern). sdf_engine bake.rs:127's
//! `const _: () = assert!(cfg!(target_endian = "little"))` failed `makepad check` (E0080) on
//! x86_64: the check-mode interpreter runs MIR built by the type layer, which had made every
//! `cfg!` false (check_lint_tests covers that path). The run-time lowering reads the crate's cfg
//! itself; this pins that it and the type layer agree. A release `debug_assert!` in a const is
//! skipped as rustc's `if cfg!(debug_assertions)` is.

const CFG: &str = r#"
pub const WIDTH: usize = if cfg!(target_pointer_width = "64") { 64 } else { 32 };
const _: () = assert!(cfg!(target_endian = "little"));
pub struct Lanes<const N: usize>;
impl<const N: usize> Lanes<N> { pub fn n(&self) -> usize { N } }
pub fn values(out: &mut [usize; 9]) {
    out[0] = cfg!(target_endian = "little") as usize;
    out[1] = cfg!(target_pointer_width = "64") as usize;
    out[2] = if cfg!(target_arch = "x86_64") { 1 } else if cfg!(target_arch = "aarch64") { 2 } else { 0 };
    out[3] = WIDTH;
    out[4] = core::mem::size_of::<[u8; WIDTH]>();
    out[5] = Lanes::<{ if cfg!(target_endian = "little") { 4 } else { 8 } }>.n();
    out[6] = [0u8; { debug_assert!(1 == 2); 7 }].len();
    out[7] = Lanes::<WIDTH>.n();
    out[8] = match core::mem::size_of::<usize>() * 8 { WIDTH => 1, _ => 0 };
}
"#;

/// Runs `pub fn values(out: &mut [usize; N])` of the program `src` and returns `out`.
fn values<const N: usize>(src: &str, name: &str) -> [usize; N] {
    crate::jit::CHECK_FIRST.store(false, std::sync::atomic::Ordering::Relaxed);
    std::env::set_var("MAKEPAD_RUN_STD", concat!(env!("CARGO_MANIFEST_DIR"), "/std"));
    let dir = std::env::temp_dir().join(format!("relax-values-{name}-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join("lib.rs");
    std::fs::write(&path, src).unwrap();
    let (prog, core, krate) = crate::load_with_std(&std::sync::Arc::new(crate::Session::default()), path.to_str().unwrap(), name, false).unwrap();
    std::fs::remove_file(path).unwrap();
    std::fs::remove_dir(dir).unwrap();
    assert!(!prog.crates[krate as usize].cfg.holds("debug_assertions"), "the JIT's cfg is a release one");
    let mut tcx = crate::tcx::Tcx::new();
    tcx.collect(&prog);
    let mut u = crate::jit::Unit::new(prog, tcx, core);
    let up = &mut *u as *mut crate::jit::Unit;
    let def = (0..u.prog.defs.len()).map(|i| crate::program::DefId(i as u32)).find(|&d| u.prog.def(d).krate == krate && u.prog.name(d) == "values").unwrap();
    let entry = crate::owner::call(crate::owner::Class::Program, || { let f = u.fn_id(crate::jit::FnKey::Inst(def, vec![])); u.entry(f) });
    let mut out = [0usize; N];
    unsafe { crate::jit::call_jit(up, entry, &mut out as *mut [usize; N] as u64) }.map_err(|p| p.message).unwrap();
    out
}

#[test]
fn cfg_macro_is_the_crates_cfg_at_run_time_and_in_consts() {
    isolated_test!(cfg_macro_is_the_crates_cfg_at_run_time_and_in_consts);
    let out: [usize; 9] = values(CFG, "cfg_values");
    let width = if cfg!(target_pointer_width = "64") { 64 } else { 32 };
    let arch = if cfg!(target_arch = "x86_64") { 1 } else if cfg!(target_arch = "aarch64") { 2 } else { 0 };
    assert_eq!(out, [cfg!(target_endian = "little") as usize, cfg!(target_pointer_width = "64") as usize, arch, width, width, 4, 7, width, 1]);
}

/// `IoSlice` / `IoSliceMut` (now real std's `iovec`-shaped wrappers, WARNZERO class 8): the
/// slices they borrow, `advance_slices` across them, a vectored write, writes through a mutable
/// one, and the `iovec` layout (base, then length) FFI code relies on.
const IO_SLICES: &str = r#"
use std::io::{IoSlice, IoSliceMut, Write};
pub fn values(out: &mut [usize; 8]) {
    let (a, b) = ([1u8, 2, 3], [4u8, 5]);
    let mut bufs = [IoSlice::new(&a), IoSlice::new(&b)];
    out[0] = bufs[0].len() + bufs[1].len() * 10;
    let mut rest = &mut bufs[..];
    IoSlice::advance_slices(&mut rest, 4);
    out[1] = rest.len() * 10 + rest[0][0] as usize;
    let mut v = Vec::new();
    out[2] = v.write_vectored(&[IoSlice::new(&a), IoSlice::new(&b)]).unwrap();
    out[3] = v.iter().map(|&x| x as usize).sum();
    let mut m = [0u8; 4];
    {
        let mut s = IoSliceMut::new(&mut m);
        s.advance(1);
        s[0] = 9;
        out[4] = s.len();
    }
    out[5] = m[1] as usize;
    let words: [usize; 2] = unsafe { core::mem::transmute(IoSlice::new(&b)) };
    out[6] = (words[0] == b.as_ptr() as usize) as usize;
    out[7] = words[1];
}
"#;

#[test]
fn io_slices_borrow_their_buffers_as_an_iovec() {
    isolated_test!(io_slices_borrow_their_buffers_as_an_iovec);
    let out: [usize; 8] = values(IO_SLICES, "io_slices");
    assert_eq!(out, [23, 15, 5, 15, 3, 9, 1, 2]);
}
