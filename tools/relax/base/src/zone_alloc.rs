//! The heap under the loader's `#[global_allocator]` (memstat::Counting): the system allocator
//! until the program swaps the process's malloc zone, then (macOS) a private malloc zone of Relax's own.
//!
//! Why: a program that loads CEF installs Chromium's malloc shim as the default zone (it tells
//! Relax first: jit.rs `allocator_swap`). After that every compile on every thread allocated
//! through the shim, and with speculative workers running, the main thread's back end took ~3x
//! the CPU for the same functions (Stage cold: codegen 3.9 us per RIR instruction with one
//! worker vs 1.2 us compiling alone, 0.76 us without CEF): speculation made Stage's first frame
//! several times slower than compiling on the caller. A zone of our own is untouched by the
//! swap. Before the swap the default zone stays in use (its small-allocation path is faster
//! than a created zone's: Amp/counter/runner +5% first present when everything used the zone).
//!
//! Frees after the swap: a pointer our zone owns (its `size` callback says so) goes back to it;
//! anything older goes through `free()`, which finds the owning zone (the shim forwards frees of
//! pre-swap pointers to their original zone). C code freeing our pointers uses `free()` too,
//! which searches the registered zones. Other targets: the system allocator.
//!
//! `scratch()` routes Rust compile working sets through a reserved-address burst arena.
//! Arena pointers must come back through this allocator, never directly through C `free`.

mod burst;
pub use burst::{scratch, stats as burst_stats, trim as burst_trim, ScratchGuard};

use std::alloc::{GlobalAlloc, Layout, System};
#[cfg(target_os = "macos")]
use std::sync::atomic::{AtomicBool, Ordering};

pub struct RelaxAlloc;

/// Set when the program announces a malloc-zone swap (before it happens).
#[cfg(target_os = "macos")]
static OWN_ZONE: AtomicBool = AtomicBool::new(false);

/// From now on allocate from Relax's own zone (jit.rs allocator_swap, phase 0).
pub fn use_own_zone() {
    #[cfg(target_os = "macos")]
    {
        zone::get();
        OWN_ZONE.store(true, Ordering::Release);
    }
}

/// Returns the free pages of Relax's own malloc zone to the system (macOS; nothing elsewhere).
pub fn zone_relief() {
    #[cfg(target_os = "macos")]
    if OWN_ZONE.load(Ordering::Relaxed) {
        extern "C" { fn malloc_zone_pressure_relief(zone: *const u8, goal: usize) -> usize; }
        unsafe { malloc_zone_pressure_relief(zone::get(), 0) };
    }
}

#[cfg(target_os = "macos")]
mod zone {
    use std::sync::atomic::{AtomicPtr, Ordering};

    extern "C" {
        fn malloc_create_zone(start_size: usize, flags: u32) -> *mut u8;
        fn malloc_set_zone_name(zone: *mut u8, name: *const u8);
        fn malloc_zone_malloc(zone: *mut u8, size: usize) -> *mut u8;
        fn malloc_zone_calloc(zone: *mut u8, n: usize, size: usize) -> *mut u8;
        fn malloc_zone_realloc(zone: *mut u8, p: *mut u8, size: usize) -> *mut u8;
        fn malloc_zone_memalign(zone: *mut u8, align: usize, size: usize) -> *mut u8;
        fn malloc_zone_free(zone: *mut u8, p: *mut u8);
        fn free(p: *mut u8);
    }

    /// The head of libmalloc's `malloc_zone_t` (stable ABI): `size` answers 0 for a pointer the
    /// zone does not own.
    #[repr(C)]
    struct ZoneHead {
        reserved1: *mut u8,
        reserved2: *mut u8,
        size: unsafe extern "C" fn(*mut u8, *const u8) -> usize,
    }

    static ZONE: AtomicPtr<u8> = AtomicPtr::new(std::ptr::null_mut());

    pub fn get() -> *mut u8 {
        let z = ZONE.load(Ordering::Acquire);
        if !z.is_null() {
            return z;
        }
        let z = unsafe { malloc_create_zone(0, 0) };
        unsafe { malloc_set_zone_name(z, b"relax\0".as_ptr()) };
        match ZONE.compare_exchange(std::ptr::null_mut(), z, Ordering::AcqRel, Ordering::Acquire) {
            Ok(_) => z,
            Err(w) => w,
        }
    }

    #[inline]
    unsafe fn owns(p: *mut u8) -> bool {
        let z = get();
        ((*(z as *const ZoneHead)).size)(z, p) != 0
    }

    pub unsafe fn alloc(size: usize, align: usize) -> *mut u8 {
        if align <= 16 { malloc_zone_malloc(get(), size) } else { malloc_zone_memalign(get(), align, size) }
    }

    pub unsafe fn alloc_zeroed(size: usize, align: usize) -> *mut u8 {
        if align <= 16 {
            return malloc_zone_calloc(get(), 1, size);
        }
        let p = malloc_zone_memalign(get(), align, size);
        if !p.is_null() {
            std::ptr::write_bytes(p, 0, size);
        }
        p
    }

    pub unsafe fn dealloc(p: *mut u8) {
        if owns(p) {
            malloc_zone_free(get(), p)
        } else {
            free(p)
        }
    }

    pub unsafe fn realloc(p: *mut u8, old: usize, align: usize, size: usize) -> *mut u8 {
        if align <= 16 && owns(p) {
            return malloc_zone_realloc(get(), p, size);
        }
        // a pre-swap pointer (or an over-aligned one): move it into the zone
        let n = alloc(size, align);
        if !n.is_null() {
            std::ptr::copy_nonoverlapping(p, n, old.min(size));
            dealloc(p);
        }
        n
    }
}

unsafe impl GlobalAlloc for RelaxAlloc {
    #[inline]
    unsafe fn alloc(&self, l: Layout) -> *mut u8 {
        if burst::active() {
            let p = burst::alloc(l);
            if !p.is_null() {
                return p;
            }
        }
        #[cfg(target_os = "macos")]
        if OWN_ZONE.load(Ordering::Relaxed) {
            return zone::alloc(l.size(), l.align());
        }
        System.alloc(l)
    }
    #[inline]
    unsafe fn alloc_zeroed(&self, l: Layout) -> *mut u8 {
        if burst::active() {
            let p = burst::alloc(l);
            if !p.is_null() {
                std::ptr::write_bytes(p, 0, l.size());
                return p;
            }
        }
        #[cfg(target_os = "macos")]
        if OWN_ZONE.load(Ordering::Relaxed) {
            return zone::alloc_zeroed(l.size(), l.align());
        }
        System.alloc_zeroed(l)
    }
    #[inline]
    unsafe fn dealloc(&self, p: *mut u8, l: Layout) {
        if burst::owns(p) {
            return burst::dealloc(p, l);
        }
        #[cfg(target_os = "macos")]
        if OWN_ZONE.load(Ordering::Relaxed) {
            return zone::dealloc(p);
        }
        System.dealloc(p, l)
    }
    #[inline]
    unsafe fn realloc(&self, p: *mut u8, l: Layout, size: usize) -> *mut u8 {
        if burst::owns(p) || burst::active() {
            // The destination follows the current scope. On failure the old block stays valid.
            let n = self.alloc(Layout::from_size_align_unchecked(size, l.align()));
            if !n.is_null() {
                std::ptr::copy_nonoverlapping(p, n, l.size().min(size));
                self.dealloc(p, l);
            }
            return n;
        }
        #[cfg(target_os = "macos")]
        if OWN_ZONE.load(Ordering::Relaxed) {
            return zone::realloc(p, l.size(), l.align(), size);
        }
        System.realloc(p, l, size)
    }
}
