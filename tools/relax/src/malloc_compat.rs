//! Linux: glibc's legacy `mallinfo()` for the libraries this process loads.
//!
//! `mallinfo` reports in `int` fields, which wrap negative once the process's malloc heap passes
//! 2 GiB (a Relax run of a large app holds 3 GB). Chromium (libcef) reads it in its memory-dump
//! provider (`MallocDumpProvider::OnMemoryDump`) and `checked_cast`s `arena + hblkhd` and
//! `uordblks` to `size_t`; a negative value hits its CHECK (`ud2`), so the host dies of SIGILL on
//! the MemoryInfra thread whenever a memory dump request lands after the heap crossed 2 GiB.
//! This definition is exported from the executable (build.rs: `--export-dynamic-symbol`), so the
//! dynamic linker resolves libcef's `mallinfo` import here before libc. It reports glibc's
//! `mallinfo2` (64-bit) values clamped to `int`, with `arena + hblkhd` clamped as a sum, so no
//! sum a caller forms can wrap.

#[repr(C)]
pub struct Mallinfo {
    arena: i32,
    ordblks: i32,
    smblks: i32,
    hblks: i32,
    hblkhd: i32,
    usmblks: i32,
    fsmblks: i32,
    uordblks: i32,
    fordblks: i32,
    keepcost: i32,
}

#[repr(C)]
pub struct Mallinfo2 {
    pub arena: usize,
    pub ordblks: usize,
    pub smblks: usize,
    pub hblks: usize,
    pub hblkhd: usize,
    pub usmblks: usize,
    pub fsmblks: usize,
    pub uordblks: usize,
    pub fordblks: usize,
    pub keepcost: usize,
}

extern "C" {
    fn mallinfo2() -> Mallinfo2;
}

fn clamp(v: usize) -> i32 {
    v.min(i32::MAX as usize) as i32
}

/// `m` as the `int` struct: every field saturates at `i32::MAX`, and `arena` is cut so that
/// `arena + hblkhd` (what Chromium adds) also stays within it.
pub fn saturate(m: &Mallinfo2) -> Mallinfo {
    let hblkhd = clamp(m.hblkhd);
    Mallinfo {
        arena: clamp(m.arena).min(i32::MAX - hblkhd),
        ordblks: clamp(m.ordblks),
        smblks: clamp(m.smblks),
        hblks: clamp(m.hblks),
        hblkhd,
        usmblks: clamp(m.usmblks),
        fsmblks: clamp(m.fsmblks),
        uordblks: clamp(m.uordblks),
        fordblks: clamp(m.fordblks),
        keepcost: clamp(m.keepcost),
    }
}

#[no_mangle]
pub extern "C" fn mallinfo() -> Mallinfo {
    saturate(&unsafe { mallinfo2() })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn nonneg_sums(m: &Mallinfo) {
        assert!(m.arena >= 0 && m.hblkhd >= 0 && m.uordblks >= 0 && m.fordblks >= 0);
        assert!(m.arena.checked_add(m.hblkhd).is_some_and(|s| s >= 0), "arena + hblkhd wraps");
    }

    #[test]
    fn values_past_two_gib_saturate() {
        let gib = 1usize << 30;
        let m = saturate(&Mallinfo2 { arena: 3 * gib, ordblks: 5, smblks: 0, hblks: 2, hblkhd: gib, usmblks: 0, fsmblks: 0, uordblks: 5 * gib, fordblks: 4 * gib, keepcost: 7 });
        nonneg_sums(&m);
        assert_eq!(m.hblkhd, gib as i32);
        assert_eq!(m.arena, i32::MAX - gib as i32);
        assert_eq!(m.uordblks, i32::MAX);
        assert_eq!((m.ordblks, m.keepcost), (5, 7));
        // a mapped total past 2 GiB on its own
        let m = saturate(&Mallinfo2 { arena: 0, ordblks: 0, smblks: 0, hblks: 0, hblkhd: 3 * gib, usmblks: 0, fsmblks: 0, uordblks: 0, fordblks: 0, keepcost: 0 });
        nonneg_sums(&m);
        assert_eq!((m.hblkhd, m.arena), (i32::MAX, 0));
    }

    /// The live heap past 2 GiB: glibc's own `mallinfo` returns wrapped (negative) fields here,
    /// which is what killed Chromium's memory dump; ours must not. The 3 GiB block is mmap'd and
    /// never touched.
    #[test]
    fn real_heap_past_two_gib_does_not_wrap() {
        extern "C" {
            fn malloc(n: usize) -> *mut u8;
            fn free(p: *mut u8);
        }
        let big = unsafe { malloc(3usize << 30) };
        if big.is_null() {
            return; // address space limited (ulimit -v): nothing to measure
        }
        // one touched page, so the allocation cannot be optimized away
        unsafe { std::ptr::write_volatile(std::hint::black_box(big), 1) };
        let m = mallinfo();
        unsafe { free(big) };
        nonneg_sums(&m);
        assert!(m.hblkhd as i64 + m.arena as i64 > 1 << 30, "the 3 GiB block is not in the figures: arena {} hblkhd {} uordblks {}", m.arena, m.hblkhd, m.uordblks);
    }
}
