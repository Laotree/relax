//! Domain-local statics (local/agent_state/fast-rust/android/DESIGN-domains.md §2).
//!
//! Several apps ("domains") may run in one process on the same compiled code, so each needs its
//! own copy of every static. A domain symbol (`SymClass::Domain`: a static, a writable block
//! lowering placed) therefore has an OFFSET in the domain static block, not an address, and
//! code computes `domain base + offset`: the base is slot 0 of the running thread's
//! thread-local block (jit.rs `tls_alloc`), read by the back ends' `dom_addr` next to the block
//! pointer itself.
//!
//! - The compile domain (domain 0) is the unit's own writable region: statics are laid out in
//!   it as they are first named, initializers and constant evaluation run in it, and a
//!   thread that is in no other domain uses it. Nothing about a single-domain run differs from
//!   absolute addresses but the base load.
//! - Another domain's block is a same-sized range of its own, reserved once and never moved.
//!   Its bytes are the INITIAL images (`Syms::initial_data`, the snapshot taken right after the
//!   initializer, never the running state) at the same offsets as in domain 0; the pointer words
//!   in them that point into the block (statics naming statics, cycles, promoted writable
//!   data) are rebased, words that point into shared read-only data stay. The attribution of
//!   words and the image bytes are the sandbox's (`sandbox::provenance_words`, `initial_bytes`):
//!   the same "one data image, pointers relocated per copy" machinery, a second client.
//! - A static laid out after a domain exists is copied into every live block (`materialize`).
//! - Threads: a thread JIT code starts inherits its parent's base (std's thread start calls
//!   `relax_domain_base` / `relax_domain_enter`); `call_jit` runs in the unit's domain 0; a
//!   thread that native code starts gets the runtime unit's compile domain from `rt_tls_block`.
//!
//! A constant's value is shared read-only data, but one that points at a static (`const C:
//! &AtomicU32 = &S`), or at other per-domain data, directly or through data it points to, would
//! hand every domain the compile domain's copy. `rehome_const` moves such a value (and each data
//! object on the way that reaches the block) into a writable per-domain object: every domain then
//! has its own copy with its pointers rebased, and code reaches it through its symbol like a
//! static. A scalar pointer constant needs nothing: lowering emits its target's symbol.

use crate::jit::Unit;
use crate::rir::Sym;
use crate::sandbox::{initial_bytes, provenance_words};
use crate::syms::SymKind;
use std::collections::HashSet;
use std::sync::Mutex;

/// The address of constant data object `addr` as every domain must see it: unchanged when its
/// image (and the data it points to) holds no address inside the compile domain's block; else a
/// writable per-domain block (`Unit::rw_sym`: SymClass::Domain, never folded, so code reads it
/// through its symbol), its pointer words patched to the re-homed children, registered as initial data so
/// live and later domains get it rebased (`materialize`, `create`). Bottom-up; `seen` keeps shared
/// children (and cycles) to one copy.
pub(crate) fn rehome_const(u: &Unit, addr: u64) -> u64 {
    let mut seen = std::collections::HashMap::new();
    rehome(u, addr, &mut seen)
}

/// Gives anonymous mutable block `id` (made by constant evaluation: a promoted temporary) and
/// every such block its image points into an initial image, and copies them into the live
/// domains: they have none until something names them.
fn capture_rw(u: &Unit, id: u32, seen: &mut HashSet<u32>) {
    if !seen.insert(id) {
        return;
    }
    let sym = Sym::new(id);
    crate::sandbox::capture_initial_data(u, sym);
    if let Ok(bytes) = initial_bytes(u, id) {
        for w in bytes.chunks_exact(8).map(|w| u64::from_le_bytes(w.try_into().unwrap())) {
            if let Some(rw) = u.syms.rw_sym_at(w) {
                capture_rw(u, rw.id, seen);
            }
        }
    }
    materialize(u, sym);
}

fn rehome(u: &Unit, addr: u64, seen: &mut std::collections::HashMap<u64, u64>) -> u64 {
    if let Some(&a) = seen.get(&addr) {
        return a;
    }
    let (lo, hi) = (u.syms.dom0(), u.syms.dom0() + BLOCK_SIZE as u64);
    let Some((start, len, align, mutable)) = u.syms.object_of(addr) else { return addr };
    if mutable || start != addr || (lo..hi).contains(&start) {
        return addr;
    }
    // a cycle back to this object keeps the shared address until the copy exists (patched below)
    seen.insert(addr, addr);
    let mut bytes = unsafe { std::slice::from_raw_parts(start as *const u8, len as usize).to_vec() };
    let mut reaches = false;
    for k in (0..bytes.len() / 8).map(|i| i * 8) {
        let w = u64::from_le_bytes(bytes[k..k + 8].try_into().unwrap());
        if (lo..hi).contains(&w) {
            // a static (materialized when laid out) or an anonymous mutable block: one constant
            // evaluation made (a promoted temporary) has no initial image yet -- every domain needs it
            if let Some(rw) = u.syms.rw_sym_at(w) {
                capture_rw(u, rw.id, &mut HashSet::new());
            }
            reaches = true;
            continue;
        }
        let Some((cs, _, _, cmut)) = u.syms.object_of(w) else { continue };
        if cmut || cs == start {
            continue;
        }
        let moved = rehome(u, cs, seen);
        if moved != cs {
            bytes[k..k + 8].copy_from_slice(&(moved + (w - cs)).to_le_bytes());
            reaches = true;
        }
    }
    if !reaches {
        seen.insert(addr, addr);
        return addr;
    }
    // an anonymous mutable block: per domain (SymClass::Domain), never folded
    let sym = u.rw_sym(len.max(1), align.max(1), match u.syms.kind_at(start) { crate::syms::DataKind::Typed(t) => Some(t), _ => None });
    let new = u.syms.addr(sym);
    unsafe { std::ptr::copy_nonoverlapping(bytes.as_ptr(), new as *mut u8, bytes.len()) };
    // a word pointing into the object itself (a self-referential constant) points at the copy
    for k in (0..bytes.len() / 8).map(|i| i * 8) {
        let w = u64::from_le_bytes(bytes[k..k + 8].try_into().unwrap());
        if (start..start + len).contains(&w) {
            unsafe { *((new + k as u64) as *mut u64) = new + (w - start) };
        }
    }
    seen.insert(addr, new);
    crate::sandbox::capture_initial_data(u, sym);
    materialize(u, sym);
    new
}

/// Blocks of the domains other than the compile domain, by base.
static BLOCKS: Mutex<Vec<u64>> = Mutex::new(Vec::new());

/// Bytes of a domain block (the unit's writable region; a block is address space until touched).
pub const BLOCK_SIZE: usize = crate::jit::UNIT_RW_SIZE as usize;

/// The domain a thread nothing assigned one to starts in (one native code started and calls
/// into JIT code, e.g. a platform callback): the compile domain of the runtime's unit (the
/// program's, `call_jit` / `set_runtime_unit`; a process can hold other units: the macro world's,
/// test units). 0 before any unit ran code.
pub fn default_base() -> u64 {
    let u = unsafe { crate::jit::UNIT };
    if u.is_null() { 0 } else { unsafe { (&*u).syms.dom0() } }
}

/// The calling thread's domain block (slot 0 of its thread-local block).
pub fn current() -> u64 {
    unsafe { *(crate::jit::tls_block() as *const u64) }
}

/// Puts the calling thread in the domain whose block is `base`; returns the one it was in.
pub fn enter(base: u64) -> u64 {
    let slot = crate::jit::tls_block() as *mut u64;
    unsafe { std::mem::replace(&mut *slot, base) }
}

/// For Relax std (`__relax_domain_base`): the base a thread it starts inherits.
pub extern "C" fn relax_domain_base() -> u64 {
    current()
}

/// For Relax std (`__relax_domain_enter`): the first thing a started thread does.
pub extern "C" fn relax_domain_enter(base: u64) {
    enter(base);
}

/// The offset in a domain block of what `s` names, when its storage is per domain: a static, a
/// writable block, a writable data object (promoted inside an initializer).
fn offset_of(u: &Unit, s: Sym) -> Option<u64> {
    match u.syms.kind(s.id)? {
        SymKind::Static(_) | SymKind::Rw(_) => Some(u.syms.value(s)),
        SymKind::Data(i) => {
            let (start, _, _, mutable) = u.syms.obj_info(i)?;
            mutable.then(|| (start - u.syms.dom0()).wrapping_add(s.off as u64))
        }
        _ => None,
    }
}

/// Writes the initial image of `sym` (and of the writable data it points to) into the block at
/// `base`, its in-block pointers rebased. `seen`: what this call already did.
fn materialize_in(u: &Unit, base: u64, sym: u32, seen: &mut HashSet<u32>) {
    if !seen.insert(sym) {
        return;
    }
    let Some(own) = offset_of(u, Sym::new(sym)) else { return };
    // no declared initializer: a block lowering fills by code when it runs stays zero
    let Ok(bytes) = initial_bytes(u, sym) else { return };
    let at = base + own;
    unsafe { std::ptr::copy_nonoverlapping(bytes.as_ptr(), at as *mut u8, bytes.len()) };
    for (o, t) in provenance_words(u, &bytes) {
        if let Some(to) = offset_of(u, t) {
            unsafe { *((at + o as u64) as *mut u64) = base + to };
            if !matches!(u.syms.kind(t.id), Some(SymKind::Static(_) | SymKind::Rw(_))) {
                materialize_in(u, base, t.id, seen);
            }
        }
    }
}

/// Makes a new domain's block: reserved once (it never moves), holding the initial image of
/// every static laid out so far. Returns its base.
pub fn create(u: &Unit) -> u64 {
    let base = crate::os::mem::alloc_rw(BLOCK_SIZE);
    let ids: Vec<u32> = u.syms.initial_data.lock().unwrap_or_else(|e| e.into_inner()).keys().copied().collect();
    let mut seen = HashSet::new();
    for id in ids {
        materialize_in(u, base, id, &mut seen);
    }
    BLOCKS.lock().unwrap_or_else(|e| e.into_inner()).push(base);
    base
}

/// Gives a domain's block back (every thread of the domain is gone).
pub fn destroy(base: u64) {
    BLOCKS.lock().unwrap_or_else(|e| e.into_inner()).retain(|b| *b != base);
    crate::os::mem::free(base, BLOCK_SIZE);
}

/// A static was just laid out (jit.rs `static_addr`, after its initial image was captured): copy
/// it into the live blocks. No other domain: nothing to do.
pub(crate) fn materialize(u: &Unit, sym: Sym) {
    let blocks = BLOCKS.lock().unwrap_or_else(|e| e.into_inner());
    for &base in blocks.iter() {
        materialize_in(u, base, sym.id, &mut HashSet::new());
    }
}

/// The live blocks other than domain 0 (tests, inspect).
pub fn blocks() -> Vec<u64> {
    BLOCKS.lock().unwrap_or_else(|e| e.into_inner()).clone()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::jit::FnKey;
    use crate::program::DefId;

    /// Two domains on the same compiled code: each has its own statics, a pointer inside a static
    /// image points into its own block, a static laid out after a domain exists is copied into it.
    #[test]
    fn domains_have_their_own_statics() {
        let sess = &std::sync::Arc::new(crate::Session::default());
        let root = std::env::temp_dir().join(format!("relax-domains-{}", std::process::id()));
        std::fs::create_dir_all(&root).unwrap();
        let source = root.join("fixture.rs");
        std::fs::write(&source, r#"
            static mut COUNTER: u64 = 5;
            static mut CELL: u64 = 1;
            static PCELL: *mut u64 = unsafe { &CELL as *const u64 as *mut u64 };
            static mut LATE: u64 = 40;
            fn bump(out: *mut u64) { unsafe { COUNTER += 1; *out = COUNTER; } }
            fn through(out: *mut u64) { unsafe { *PCELL += 10; *out = CELL; } }
            fn late(out: *mut u64) { unsafe { LATE += 1; *out = LATE; } }
        "#).unwrap();
        let mut prog = crate::program::Program::new(sess);
        prog.load_crate("fixture", source.to_str().unwrap(), 2021, crate::cfg::CfgSet::host(sess, &[]), Vec::new()).unwrap();
        let mut tcx = crate::tcx::Tcx::new();
        tcx.collect(&prog);
        let mut u = Unit::new(prog, tcx, 0);
        let def = |u: &Unit, name: &str| DefId(u.prog.defs.iter().position(|d| u.prog.syms.str(d.name) == name).unwrap() as u32);
        let (bump, through, late) = (def(&u, "bump"), def(&u, "through"), def(&u, "late"));
        let (counter, cell, pcell, late_static) = (def(&u, "COUNTER"), def(&u, "CELL"), def(&u, "PCELL"), def(&u, "LATE"));
        let up = &mut *u as *mut Unit;
        let entry = |u: &mut Unit, d: DefId| { let id = u.fn_id(FnKey::Inst(d, Vec::new())); u.entry(id) };
        let call = |base: u64, entry: u64| -> u64 {
            let mut out = 0u64;
            unsafe { crate::jit::call_jit_in(up, base, entry, &mut out as *mut u64 as u64) }.unwrap_or_else(|p| panic!("{}", p.message));
            out
        };
        let dom0 = u.syms.dom0();
        // the statics exist (and have offsets) before the second domain is made
        for d in [counter, cell, pcell] {
            let s = u.static_sym(d);
            assert!(u.syms.value(s) > 0 && u.syms.value(s) < BLOCK_SIZE as u64, "an offset, not an address");
            assert_eq!(u.syms.addr(s), dom0 + u.syms.value(s));
        }
        let (e_bump, e_through) = (entry(&mut u, bump), entry(&mut u, through));
        assert_eq!(call(dom0, e_bump), 6);
        let b = create(&u);
        assert_ne!(b, dom0);
        // the new domain starts from the INITIAL image (5), not the running state (6)
        assert_eq!(call(b, e_bump), 6);
        assert_eq!(call(b, e_bump), 7);
        assert_eq!(call(dom0, e_bump), 7);
        assert_eq!(call(dom0, e_bump), 8);
        assert_eq!(call(b, e_bump), 8);
        // PCELL holds the address of CELL: in the domain's own block
        assert_eq!(call(dom0, e_through), 11);
        assert_eq!(call(b, e_through), 11);
        assert_eq!(call(b, e_through), 21);
        assert_eq!(call(dom0, e_through), 21);
        let ps = u.static_sym(pcell);
        let cs = u.static_sym(cell);
        let (pcell_off, cell_off) = (u.syms.value(ps), u.syms.value(cs));
        unsafe {
            assert_eq!(*((dom0 + pcell_off) as *const u64), dom0 + cell_off);
            assert_eq!(*((b + pcell_off) as *const u64), b + cell_off);
        }
        // a static first named after the domain exists is copied into it
        let e_late = entry(&mut u, late);
        assert!(u.statics.get(&late_static).is_none());
        assert_eq!(call(dom0, e_late), 41);
        assert_eq!(call(b, e_late), 41);
        assert_eq!(call(b, e_late), 42);
        assert_eq!(call(dom0, e_late), 42);
        // the thread is back in the domain it was in
        assert_eq!(current(), dom0);
        assert_eq!(enter(b), dom0);
        assert_eq!(enter(dom0), b);
        destroy(b);
        assert!(!blocks().contains(&b));
        std::fs::remove_dir_all(root).unwrap();
    }

    /// A constant pointing at a static (directly or through data it points to) is per domain:
    /// each domain's copy points at its own static; a constant that reaches no static stays shared.
    #[test]
    fn const_pointing_at_static_is_per_domain() {
        let sess = &std::sync::Arc::new(crate::Session::default());
        let root = std::env::temp_dir().join(format!("relax-domains-const-{}", std::process::id()));
        std::fs::create_dir_all(&root).unwrap();
        let source = root.join("fixture.rs");
        std::fs::write(&source, r#"
            static mut S: u64 = 3;
            const DIRECT: &[*mut u64; 1] = &[unsafe { &raw mut S }];
            const NESTED: &[&[*mut u64; 1]; 1] = &[&[unsafe { &raw mut S }]];
            const PLAIN: &[u64; 2] = &[4, 5];
            fn direct(out: *mut u64) { unsafe { *DIRECT[0] += 1; *out = *DIRECT[0]; } }
            fn nested(out: *mut u64) { unsafe { *NESTED[0][0] += 10; *out = *NESTED[0][0]; } }
            fn plain(out: *mut u64) { unsafe { *out = PLAIN[1]; } }
        "#).unwrap();
        let mut prog = crate::program::Program::new(sess);
        prog.load_crate("fixture", source.to_str().unwrap(), 2021, crate::cfg::CfgSet::host(sess, &[]), Vec::new()).unwrap();
        let mut tcx = crate::tcx::Tcx::new();
        tcx.collect(&prog);
        let mut u = Unit::new(prog, tcx, 0);
        let def = |u: &Unit, name: &str| DefId(u.prog.defs.iter().position(|d| u.prog.syms.str(d.name) == name).unwrap() as u32);
        let (direct, nested, plain) = (def(&u, "direct"), def(&u, "nested"), def(&u, "plain"));
        let up = &mut *u as *mut Unit;
        let entry = |u: &mut Unit, d: DefId| { let id = u.fn_id(FnKey::Inst(d, Vec::new())); u.entry(id) };
        let call = |base: u64, entry: u64| -> u64 {
            let mut out = 0u64;
            unsafe { crate::jit::call_jit_in(up, base, entry, &mut out as *mut u64 as u64) }.unwrap_or_else(|p| panic!("{}", p.message));
            out
        };
        let dom0 = u.syms.dom0();
        let (e_direct, e_nested, e_plain) = (entry(&mut u, direct), entry(&mut u, nested), entry(&mut u, plain));
        let b = create(&u);
        assert_eq!(call(dom0, e_direct), 4);
        assert_eq!(call(b, e_direct), 4);
        assert_eq!(call(b, e_nested), 14);
        assert_eq!(call(dom0, e_nested), 14);
        assert_eq!(call(dom0, e_direct), 15);
        assert_eq!(call(b, e_plain), 5);
        assert!(u.errors.is_empty(), "{:?}", u.errors);
        destroy(b);
        std::fs::remove_dir_all(root).unwrap();
    }
}
