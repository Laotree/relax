//! Code reclamation: unlink -> prove quiescence -> free (MEMRECLAIM.DESIGN.md, JITREFMEM L5).
//!
//! Reclaimable machine code (the sandbox's twin spaces) is reachable only through one guarded
//! host entry (`sandbox::enter_raw`). Each thread that passes it keeps a record here: the epoch
//! of its outermost entry, or 0 while it is outside. A space is unlinked (its slot words point
//! elsewhere), then stamped with a fresh epoch (`advance`); it may be reused only once every
//! record is 0 or at least that epoch (`quiescent_since`). A thread still inside since before
//! the stamp -- running, blocked in a host call, never returning -- blocks the reuse; it is never
//! skipped and there is no timeout.
//!
//! Ordering (store buffering): a thread stores its entry epoch, then a SeqCst fence, before it
//! loads any slot word. The reclaimer stores the slot words, then bumps EPOCH, then loads the
//! records (all SeqCst). So either the reclaimer sees the record, or the thread sees the new slot
//! words.

use std::sync::atomic::{fence, AtomicBool, AtomicPtr, AtomicU64, Ordering};

/// The current epoch (starts at 1; 0 in a record means "outside").
static EPOCH: AtomicU64 = AtomicU64::new(1);

/// One thread's record (leaked; reused by a later thread once its thread exits).
struct Rec {
    /// the epoch of the outermost entry, 0 while outside
    entered: AtomicU64,
    /// owned by a live thread
    taken: AtomicBool,
    next: *const Rec,
}

/// Every record ever made (push-only list: records are never unlinked, so a walk needs no lock).
static HEAD: AtomicPtr<Rec> = AtomicPtr::new(std::ptr::null_mut());

thread_local! {
    /// this thread's record (const, no destructor: readable during thread exit)
    static MINE: std::cell::Cell<*const Rec> = const { std::cell::Cell::new(std::ptr::null()) };
    /// gives the record back when the thread exits
    static OWNER: Owner = const { Owner };
}

struct Owner;

impl Drop for Owner {
    fn drop(&mut self) {
        let r = MINE.with(|m| m.replace(std::ptr::null()));
        if !r.is_null() {
            // only an exiting thread gets here: it holds no frame of reclaimable code
            unsafe {
                (*r).entered.store(0, Ordering::SeqCst);
                (*r).taken.store(false, Ordering::Release);
            }
        }
    }
}

fn mine() -> &'static Rec {
    let r = MINE.with(|m| m.get());
    if !r.is_null() {
        return unsafe { &*r };
    }
    // a record a finished thread gave back, or a new one
    let mut p = HEAD.load(Ordering::Acquire) as *const Rec;
    let r = loop {
        if p.is_null() {
            let _k = crate::zone_alloc::kept();
            let n = Box::into_raw(Box::new(Rec { entered: AtomicU64::new(0), taken: AtomicBool::new(true), next: std::ptr::null() }));
            let mut head = HEAD.load(Ordering::Acquire);
            loop {
                unsafe { (*n).next = head };
                match HEAD.compare_exchange_weak(head, n, Ordering::AcqRel, Ordering::Acquire) {
                    Ok(_) => break,
                    Err(h) => head = h,
                }
            }
            break n as *const Rec;
        }
        let rec = unsafe { &*p };
        if rec.taken.compare_exchange(false, true, Ordering::AcqRel, Ordering::Relaxed).is_ok() {
            break p;
        }
        p = rec.next;
    };
    MINE.with(|m| m.set(r));
    // registers the give-back (a thread already past its TLS destructors keeps the record: it
    // reads 0 once the thread leaves, so it blocks nothing)
    let _ = OWNER.try_with(|_| ());
    unsafe { &*r }
}

/// This thread enters reclaimable code from outside (its depth went 0 -> 1). Must run before
/// any slot word of that code is loaded.
#[inline]
pub fn enter_outermost() {
    let r = mine();
    r.entered.store(EPOCH.load(Ordering::SeqCst), Ordering::SeqCst);
    fence(Ordering::SeqCst);
}

/// This thread holds no frame of reclaimable code any more (depth back to 0: a return, an
/// unwind, or a guard's recovery after a contained fault).
#[inline]
pub fn left() {
    let r = MINE.with(|m| m.get());
    if !r.is_null() {
        unsafe { (*r).entered.store(0, Ordering::Release) };
    }
}

/// After an unlink (the code's slot words already point elsewhere): a fresh epoch that stamps
/// the unlinked code. Threads entering from now on cannot reach it.
pub fn advance() -> u64 {
    EPOCH.fetch_add(1, Ordering::SeqCst) + 1
}

/// Is code unlinked at epoch `stamp` unreachable from every thread? (0: never ran -- always.)
pub fn quiescent_since(stamp: u64) -> bool {
    blockers(stamp) == 0
}

/// Threads still inside since before `stamp`.
pub fn blockers(stamp: u64) -> usize {
    let mut n = 0;
    let mut p = HEAD.load(Ordering::SeqCst) as *const Rec;
    while !p.is_null() {
        let r = unsafe { &*p };
        let e = r.entered.load(Ordering::SeqCst);
        if e != 0 && e < stamp {
            n += 1;
        }
        p = r.next;
    }
    n
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_thread_inside_blocks_until_it_leaves() {
        let inside = std::sync::Arc::new(std::sync::Barrier::new(2));
        let go = std::sync::Arc::new(std::sync::Barrier::new(2));
        let (i2, g2) = (inside.clone(), go.clone());
        let t = std::thread::spawn(move || {
            enter_outermost();
            i2.wait();
            g2.wait();
            left();
        });
        inside.wait();
        let stamp = advance();
        assert!(!quiescent_since(stamp), "a thread inside since before the stamp must block");
        // a thread entering after the stamp does not block it
        enter_outermost();
        assert_eq!(blockers(stamp), 1);
        left();
        go.wait();
        t.join().unwrap();
        assert!(quiescent_since(stamp));
    }

    #[test]
    fn records_are_reused_after_thread_exit() {
        let count = || {
            let mut n = 0;
            let mut p = HEAD.load(Ordering::SeqCst) as *const Rec;
            while !p.is_null() { n += 1; p = unsafe { (*p).next }; }
            n
        };
        std::thread::spawn(|| { enter_outermost(); left(); }).join().unwrap();
        let n0 = count();
        for _ in 0..64 {
            std::thread::spawn(|| { enter_outermost(); left(); }).join().unwrap();
        }
        // other tests may run threads at once: growth stays bounded by them, not by the 64 joins
        assert!(count() <= n0 + 8, "records leak per thread: {} -> {}", n0, count());
    }
}
