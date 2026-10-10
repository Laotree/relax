//! Burst allocations occupy a permanently reserved address range. The range compare is the
//! only ownership check on ordinary frees. Empty chunks are returned immediately, including
//! the current thread's chunk: TLS caches hold generation numbers, not ownership references.
//! A small-class chunk that empties with little of it touched goes to a bounded WARM list
//! instead of being decommitted (its touched pages stay resident): the next chunk any thread
//! needs is taken from there without an OS call or page faults. Every compile scope empties its
//! chunks, so decommitting them cost each O1 compile ~10 madvise/mprotect pairs plus the
//! page faults of re-touching them (~45 us per function on node). `trim` decommits the list.
//!
//! Headers live outside the payload mappings so a stale TLS cache can safely lock/check a
//! decommitted chunk. A per-chunk mutex protects its free list, bump cursor and lifecycle;
//! the atomic live count counts blocks only (no hidden TLS pin). Allocation is by one thread
//! per generation; any thread may free. The pool lock is never taken with a chunk lock held.
//! Nothing here allocates through Rust's global allocator, including initialization.

#[cfg(any(target_os = "macos", target_os = "linux", windows))]
mod arena {
    use std::alloc::Layout;
    use std::cell::{Cell, UnsafeCell};
    use std::marker::PhantomData;
    use std::ptr::null_mut;
    use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};

    pub(super) const CHUNK: usize = 2 << 20;
    const MIN_SHIFT: usize = 4;
    const MAX_SHIFT: usize = 18; // 16 B .. 256 KB; >256 KB gets an exclusive mapping
    const CLASSES: usize = MAX_SHIFT - MIN_SHIFT + 1;
    #[cfg(target_pointer_width = "64")]
    const MAX_ORDER: usize = 15; // 64 GB of virtual address space, not resident memory
    #[cfg(not(target_pointer_width = "64"))]
    const MAX_ORDER: usize = 7; // 256 MB on 32-bit; exhaustion falls back to the heap
    const N: usize = 1 << MAX_ORDER;
    const RESERVE: usize = N * CHUNK;
    const NONE: usize = usize::MAX;
    // Compatible with 4/16/64 KB OS pages and Windows allocation granularity.
    const PAGE: usize = 64 << 10;

    static BASE: AtomicUsize = AtomicUsize::new(0);
    static INIT: Mutex<bool> = Mutex::new(false);
    static COMMITTED: AtomicUsize = AtomicUsize::new(0);
    static CHUNKS: AtomicUsize = AtomicUsize::new(0);
    /// Warm chunks: emptied small-class chunks kept committed for reuse (see the module doc).
    /// At most WARM_MAX of them, touched bytes summed at most WARM_BYTES_MAX; a chunk that had
    /// more than WARM_TOUCHED_MAX touched is decommitted as before.
    const WARM_MAX: usize = 256;
    const WARM_TOUCHED_MAX: usize = 256 << 10;
    const WARM_BYTES_MAX: usize = 32 << 20;
    struct Warm {
        runs: [(usize, usize); WARM_MAX], // (chunk index, touched bytes)
        len: usize,
        bytes: usize,
    }
    static WARM: Mutex<Warm> = Mutex::new(Warm { runs: [(0, 0); WARM_MAX], len: 0, bytes: 0 });

    #[derive(Clone, Copy)]
    struct Current {
        index: usize,
        generation: u64,
    }
    const NO_CURRENT: Current = Current {
        index: NONE,
        generation: 0,
    };
    thread_local! {
        static DEPTH: Cell<usize> = const { Cell::new(0) };
        static CURRENT: Cell<[Current; CLASSES]> = const { Cell::new([NO_CURRENT; CLASSES]) };
    }

    /// Keeps routing active on the entering thread. Nested scopes and unwinding are safe.
    /// Deliberately !Send and !Sync: dropping it on another thread would alter the wrong TLS.
    pub struct ScratchGuard(bool, PhantomData<*mut ()>);
    impl Drop for ScratchGuard {
        fn drop(&mut self) {
            if self.0 {
                let _ = DEPTH.try_with(|d| d.set(d.get() - 1));
            }
        }
    }

    // std::sync::Mutex can allocate on first lock (notably Darwin's pthread backend).
    // That recurses when used under a global allocator. These locks never allocate or park.
    struct Mutex<T> {
        held: AtomicBool,
        value: UnsafeCell<T>,
    }
    unsafe impl<T: Send> Sync for Mutex<T> {}
    impl<T> Mutex<T> {
        const fn new(value: T) -> Self {
            Self {
                held: AtomicBool::new(false),
                value: UnsafeCell::new(value),
            }
        }
    }
    struct MutexGuard<'a, T>(&'a Mutex<T>, PhantomData<*mut ()>);
    impl<T> std::ops::Deref for MutexGuard<'_, T> {
        type Target = T;
        fn deref(&self) -> &T {
            unsafe { &*self.0.value.get() }
        }
    }
    impl<T> std::ops::DerefMut for MutexGuard<'_, T> {
        fn deref_mut(&mut self) -> &mut T {
            unsafe { &mut *self.0.value.get() }
        }
    }
    impl<T> Drop for MutexGuard<'_, T> {
        fn drop(&mut self) {
            self.0.held.store(false, Ordering::Release);
        }
    }
    fn lock<T>(m: &Mutex<T>) -> MutexGuard<'_, T> {
        let mut spins = 0;
        loop {
            if !m.held.load(Ordering::Relaxed)
                && m.held
                    .compare_exchange_weak(false, true, Ordering::Acquire, Ordering::Relaxed)
                    .is_ok()
            {
                return MutexGuard(m, PhantomData);
            }
            std::hint::spin_loop();
            spins += 1;
            if spins == 64 {
                std::thread::yield_now();
                spins = 0;
            }
        }
    }



    pub fn scratch(runtime: &crate::options::RuntimeOptions) -> ScratchGuard {
        if !runtime.burst_arena {
            return ScratchGuard(false, PhantomData);
        }
        if BASE.load(Ordering::Acquire) == 0 {
            let mut tried = lock(&INIT);
            if !*tried {
                *tried = true;
                BASE.store(unsafe { os::reserve(RESERVE, CHUNK) }, Ordering::Release);
            }
        }
        let entered =
            BASE.load(Ordering::Relaxed) != 0 && DEPTH.try_with(|d| d.set(d.get() + 1)).is_ok();
        ScratchGuard(entered, PhantomData)
    }

    #[inline]
    pub fn active() -> bool {
        BASE.load(Ordering::Relaxed) != 0 && DEPTH.try_with(|d| d.get() != 0).unwrap_or(false)
    }

    #[inline]
    pub fn owns(p: *mut u8) -> bool {
        let base = BASE.load(Ordering::Relaxed);
        base != 0 && (p as usize).wrapping_sub(base) < RESERVE
    }

    /// (committed payload bytes, requested live bytes, committed 2 MB chunk equivalents).
    /// Counters are independent snapshots. Headers/pool metadata are fixed static storage.
    pub fn stats() -> (usize, usize, usize) {
        (
            COMMITTED.load(Ordering::Relaxed),
            // live bytes are kept per chunk (under its lock): a process-wide counter was one
            // contended cache line written by every compile thread on every alloc and free
            HEADERS.iter().map(|h| lock(&h.state).bytes).sum(),
            CHUNKS.load(Ordering::Relaxed),
        )
    }

    struct Chunk {
        live: AtomicUsize,
        state: Mutex<State>,
    }
    struct State {
        generation: u64,
        free: usize, // intrusive list in freed slots, protected even for remote frees
        bump: usize,
        stride: usize, // zero for an exclusive large allocation
        committed: usize,
        run: usize,
        order: usize,
        bytes: usize, // requested bytes live in this chunk (stats only)
    }
    static HEADERS: [Chunk; N] = [const {
        Chunk {
            live: AtomicUsize::new(0),
            state: Mutex::new(State {
                generation: 0,
                free: 0,
                bump: 0,
                stride: 0,
                committed: 0,
                run: 0,
                order: 0,
                bytes: 0,
            }),
        }
    }; N];

    // A buddy free-chunk list supports both single chunks and contiguous large mappings.
    // Links and order markers stay outside mappings; splitting/merging never touches pages.
    struct Pool {
        heads: [usize; MAX_ORDER + 1],
        next: [usize; N],
        prev: [usize; N],
        order: [u8; N],
    }
    static POOL: Mutex<Pool> = Mutex::new(Pool::new());
    impl Pool {
        const fn new() -> Self {
            let mut heads = [NONE; MAX_ORDER + 1];
            heads[MAX_ORDER] = 0;
            let mut order = [u8::MAX; N];
            order[0] = MAX_ORDER as u8;
            Self {
                heads,
                next: [NONE; N],
                prev: [NONE; N],
                order,
            }
        }
        fn remove(&mut self, i: usize, order: usize) {
            let (prev, next) = (self.prev[i], self.next[i]);
            if prev == NONE {
                self.heads[order] = next;
            } else {
                self.next[prev] = next;
            }
            if next != NONE {
                self.prev[next] = prev;
            }
            self.order[i] = u8::MAX;
        }
        fn push(&mut self, i: usize, order: usize) {
            let next = self.heads[order];
            self.next[i] = next;
            self.prev[i] = NONE;
            if next != NONE {
                self.prev[next] = i;
            }
            self.heads[order] = i;
            self.order[i] = order as u8;
        }
        fn take(&mut self, order: usize) -> Option<usize> {
            let found = (order..=MAX_ORDER).find(|&o| self.heads[o] != NONE)?;
            let i = self.heads[found];
            self.remove(i, found);
            for o in (order..found).rev() {
                self.push(i + (1 << o), o);
            }
            Some(i)
        }
        fn release(&mut self, mut i: usize, mut order: usize) {
            while order < MAX_ORDER {
                let buddy = i ^ (1 << order);
                if self.order[buddy] != order as u8 {
                    break;
                }
                self.remove(buddy, order);
                i = i.min(buddy);
                order += 1;
            }
            self.push(i, order);
        }
    }

    unsafe fn from_current(c: Current, requested: usize) -> *mut u8 {
        if c.index == NONE {
            return null_mut();
        }
        let h = &HEADERS[c.index];
        let mut s = lock(&h.state);
        // Even if the address was freed/reassigned, this permanent header is safe to read.
        if s.generation != c.generation || h.live.load(Ordering::Relaxed) == 0 {
            return null_mut();
        }
        let p = if s.free != 0 {
            let p = s.free as *mut u8;
            s.free = *(p as *const usize);
            p
        } else if s.bump < CHUNK {
            let p = (BASE.load(Ordering::Relaxed) + c.index * CHUNK + s.bump) as *mut u8;
            s.bump += s.stride;
            p
        } else {
            return null_mut();
        };
        h.live.fetch_add(1, Ordering::Relaxed);
        s.bytes += requested;
        p
    }

    pub unsafe fn alloc(l: Layout) -> *mut u8 {
        let need = l.size().max(l.align()).max(16);
        let small = need <= 1 << MAX_SHIFT;
        let stride = if small { need.next_power_of_two() } else { 0 };
        let class = if small {
            stride.trailing_zeros() as usize - MIN_SHIFT
        } else {
            0
        };
        if small {
            let c = CURRENT.with(|c| c.get()[class]);
            let p = from_current(c, l.size());
            if !p.is_null() {
                return p;
            }
        }
        let committed = if small {
            CHUNK
        } else {
            match l.size().checked_add(PAGE - 1) {
                Some(n) => n & !(PAGE - 1),
                None => return null_mut(),
            }
        };
        // Extra virtual space allows alignments above 2 MB; only the payload is committed.
        let span = match committed.checked_add(l.align().saturating_sub(CHUNK)) {
            Some(n) if n <= RESERVE => n,
            _ => return null_mut(),
        };
        let units = (span + CHUNK - 1) / CHUNK;
        let order = units.next_power_of_two().trailing_zeros() as usize;
        // a warm chunk (committed, nothing live) serves a small class without an OS call
        let warm = if small { warm_take() } else { None };
        let run = match warm {
            Some(i) => i,
            None => match lock(&POOL).take(order) {
                Some(i) => i,
                None => return null_mut(),
            },
        };
        let start = BASE.load(Ordering::Relaxed) + run * CHUNK;
        let address = (start + l.align() - 1) & !(l.align() - 1);
        let index = (address - BASE.load(Ordering::Relaxed)) / CHUNK;
        let p = address as *mut u8;
        if warm.is_none() && !os::commit(p, committed) {
            lock(&POOL).release(run, order);
            return null_mut();
        }
        let h = &HEADERS[index];
        let generation;
        {
            let mut s = lock(&h.state);
            generation = s.generation.wrapping_add(1);
            *s = State {
                generation,
                free: 0,
                bump: stride,
                stride,
                committed,
                run,
                order,
                bytes: 0,
            };
            h.live.store(1, Ordering::Relaxed);
            if warm.is_none() {
                COMMITTED.fetch_add(committed, Ordering::Relaxed);
                CHUNKS.fetch_add((committed + CHUNK - 1) / CHUNK, Ordering::Relaxed);
            }
            s.bytes = l.size();
        }
        if small {
            CURRENT.with(|c| {
                let mut slots = c.get();
                slots[class] = Current { index, generation };
                c.set(slots);
            });
        }
        p
    }

    pub unsafe fn dealloc(p: *mut u8, l: Layout) {
        let address = (p as usize) & !(CHUNK - 1);
        let index = (address - BASE.load(Ordering::Relaxed)) / CHUNK;
        let h = &HEADERS[index];
        let mut s = lock(&h.state);
        s.bytes -= l.size();
        if h.live.fetch_sub(1, Ordering::Relaxed) != 1 {
            *(p as *mut usize) = s.free;
            s.free = p as usize;
            return;
        }
        // No live blocks: no allocation passes from_current (live == 0) until the chunk is taken
        // again under a new generation, so it can leave this lock for the warm list.
        if s.stride != 0 && s.committed == CHUNK && s.order == 0 && s.bump <= WARM_TOUCHED_MAX {
            let touched = s.bump;
            drop(s);
            if warm_put(index, touched) {
                return;
            }
            s = lock(&h.state);
        }
        // No live blocks and no allocation can pass this lock while decommitting. An old
        // TLS cache subsequently sees live == 0 or a different generation after reuse.
        if !os::decommit(address as *mut u8, s.committed) {
            // Quarantine an OS failure: do not claim reclaimed bytes or reuse this mapping.
            return;
        }
        COMMITTED.fetch_sub(s.committed, Ordering::Relaxed);
        CHUNKS.fetch_sub((s.committed + CHUNK - 1) / CHUNK, Ordering::Relaxed);
        s.committed = 0;
        let (run, order) = (s.run, s.order);
        drop(s);
        lock(&POOL).release(run, order);
    }

    fn warm_take() -> Option<usize> {
        let mut w = lock(&WARM);
        if w.len == 0 {
            return None;
        }
        w.len -= 1;
        let (i, touched) = w.runs[w.len];
        w.bytes -= touched;
        Some(i)
    }

    fn warm_put(index: usize, touched: usize) -> bool {
        let mut w = lock(&WARM);
        if w.len == WARM_MAX || w.bytes + touched > WARM_BYTES_MAX {
            return false;
        }
        let n = w.len;
        w.runs[n] = (index, touched);
        w.len += 1;
        w.bytes += touched;
        true
    }

    /// Decommits the warm chunks and returns them to the pool (settle's heap trim, tests).
    pub fn trim() {
        while let Some(index) = warm_take() {
            let h = &HEADERS[index];
            let mut s = lock(&h.state);
            let address = BASE.load(Ordering::Relaxed) + index * CHUNK;
            // nothing live and not reachable from any TLS cache (live == 0): safe to drop pages
            if !unsafe { os::decommit(address as *mut u8, s.committed) } {
                continue; // quarantined, as in dealloc
            }
            COMMITTED.fetch_sub(s.committed, Ordering::Relaxed);
            CHUNKS.fetch_sub((s.committed + CHUNK - 1) / CHUNK, Ordering::Relaxed);
            s.committed = 0;
            let (run, order) = (s.run, s.order);
            drop(s);
            lock(&POOL).release(run, order);
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;
        use crate::zone_alloc::RelaxAlloc;
        use std::alloc::GlobalAlloc;
        use std::sync::{Arc, Barrier};

        static TEST_LOCK: Mutex<()> = Mutex::new(());

        unsafe fn checked(size: usize, align: usize) -> (*mut u8, Layout) {
            let l = Layout::from_size_align(size, align).unwrap();
            let p = RelaxAlloc.alloc(l);
            assert!(!p.is_null());
            assert!(owns(p));
            assert_eq!(p as usize % align, 0);
            std::ptr::write_bytes(p, 0x5a, size);
            (p, l)
        }

        #[test]
        fn sizes_alignment_zeroing_and_escape() {
            let _serial = lock(&TEST_LOCK);
            trim();
            let before = stats();
            let mut blocks = Vec::new();
            {
                let _scope = scratch(&crate::options::RuntimeOptions::default());
                assert!(active());
                for size in [
                    1,
                    15,
                    16,
                    17,
                    31,
                    255,
                    1024,
                    2048,
                    2049,
                    8193,
                    65536,
                    262144,
                    262145,
                    CHUNK - 1,
                    CHUNK,
                    CHUNK + 1,
                    3 * CHUNK,
                ] {
                    for align in [1, 16, 64, 4096, CHUNK, 4 * CHUNK] {
                        unsafe {
                            blocks.push(checked(size, align));
                        }
                    }
                }
            }
            assert!(!active());
            for (p, l) in blocks {
                unsafe {
                    assert!(std::slice::from_raw_parts(p, l.size())
                        .iter()
                        .all(|&b| b == 0x5a));
                    RelaxAlloc.dealloc(p, l);
                }
            }
            trim();
            assert_eq!(stats(), before);
            let _scope = scratch(&crate::options::RuntimeOptions::default());
            unsafe {
                for size in [16, 2048, 262145, CHUNK + 1] {
                    let l = Layout::from_size_align(size, 64).unwrap();
                    let p = RelaxAlloc.alloc_zeroed(l);
                    assert!(!p.is_null() && owns(p));
                    assert!(std::slice::from_raw_parts(p, size).iter().all(|&b| b == 0));
                    RelaxAlloc.dealloc(p, l);
                }
            }
            trim();
            assert_eq!(stats(), before);
        }

        #[test]
        fn nested_scopes_unwind_and_realloc_between_heaps() {
            let _serial = lock(&TEST_LOCK);
            trim();
            let before = stats();
            unsafe {
                let l = Layout::from_size_align(97, 64).unwrap();
                let heap = RelaxAlloc.alloc(l);
                assert!(!heap.is_null() && !owns(heap));
                std::ptr::write_bytes(heap, 0x3c, l.size());
                let outer = scratch(&crate::options::RuntimeOptions::default());
                let inner = scratch(&crate::options::RuntimeOptions::default());
                drop(outer); // depth also tolerates guards dropped out of order
                assert!(active());
                let arena = RelaxAlloc.realloc(heap, l, 3000);
                assert!(!arena.is_null() && owns(arena));
                assert!(std::slice::from_raw_parts(arena, 97)
                    .iter()
                    .all(|&b| b == 0x3c));
                let l2 = Layout::from_size_align(3000, 64).unwrap();
                std::ptr::write_bytes(arena, 0x6d, 3000);
                let big = RelaxAlloc.realloc(arena, l2, CHUNK + 7);
                assert!(!big.is_null() && owns(big));
                assert!(std::slice::from_raw_parts(big, 3000)
                    .iter()
                    .all(|&b| b == 0x6d));
                let l3 = Layout::from_size_align(CHUNK + 7, 64).unwrap();
                let small = RelaxAlloc.realloc(big, l3, 32);
                assert!(!small.is_null() && owns(small));
                drop(inner);
                let l4 = Layout::from_size_align(32, 64).unwrap();
                let heap = RelaxAlloc.realloc(small, l4, 200);
                assert!(!heap.is_null() && !owns(heap));
                assert!(std::slice::from_raw_parts(heap, 32)
                    .iter()
                    .all(|&b| b == 0x6d));
                RelaxAlloc.dealloc(heap, Layout::from_size_align(200, 64).unwrap());
            }
            let _ = std::panic::catch_unwind(|| {
                let _scope = scratch(&crate::options::RuntimeOptions::default());
                assert!(active());
                panic!("test scope unwind");
            });
            assert!(!active());
            trim();
            assert_eq!(stats(), before);
        }

        #[test]
        fn empty_current_chunk_decommits_and_stale_cache_is_safe() {
            let _serial = lock(&TEST_LOCK);
            trim();
            let before = stats();
            let _scope = scratch(&crate::options::RuntimeOptions::default());
            unsafe {
                let (p, l) = checked(64, 16);
                let index = (p as usize - BASE.load(Ordering::Relaxed)) / CHUNK;
                let generation = lock(&HEADERS[index].state).generation;
                assert_eq!(stats(), (before.0 + CHUNK, before.1 + 64, before.2 + 1));
                RelaxAlloc.dealloc(p, l);
                assert_eq!(HEADERS[index].live.load(Ordering::Relaxed), 0);
                // emptied with 64 bytes touched: kept warm (committed) until trim
                assert_eq!(lock(&HEADERS[index].state).committed, CHUNK);
                assert_eq!(stats(), (before.0 + CHUNK, before.1, before.2 + 1));
                trim();
                assert_eq!(lock(&HEADERS[index].state).committed, 0);
                assert_eq!(stats(), before); // scope still active; no TLS pin
                                             // A different thread reuses the exact chunk while our TLS still caches it.
                let barrier = Arc::new(Barrier::new(2));
                let remote_barrier = barrier.clone();
                let old_address = p as usize;
                let remote = std::thread::spawn(move || {
                    let _scope = scratch(&crate::options::RuntimeOptions::default());
                    let (other, layout) = checked(64, 16);
                    assert_eq!(other as usize, old_address);
                    remote_barrier.wait();
                    remote_barrier.wait();
                    assert_eq!(*other, 0x5a);
                    RelaxAlloc.dealloc(other, layout);
                });
                barrier.wait();
                assert_ne!(lock(&HEADERS[index].state).generation, generation);
                let (next, layout) = checked(64, 16);
                assert_ne!((next as usize) & !(CHUNK - 1), (p as usize) & !(CHUNK - 1));
                RelaxAlloc.dealloc(next, layout);
                barrier.wait();
                remote.join().unwrap();
                trim();
            assert_eq!(stats(), before);
            }
        }

        #[test]
        fn remote_frees_during_allocation_and_after_owner_exit() {
            let _serial = lock(&TEST_LOCK);
            trim();
            let before = stats();
            let mut workers = Vec::new();
            for _ in 0..4 {
                workers.push(std::thread::spawn(|| {
                    let (tx, rx) = std::sync::mpsc::sync_channel::<(usize, Layout)>(128);
                    let freer = std::thread::spawn(move || {
                        for (p, l) in rx {
                            unsafe {
                                assert_eq!(*(p as *const u8), 0x5a);
                                RelaxAlloc.dealloc(p as *mut u8, l);
                            }
                        }
                    });
                    let mut escaped = Vec::new();
                    {
                        let _scope = scratch(&crate::options::RuntimeOptions::default());
                        for i in 0..12000 {
                            unsafe {
                                let (p, l) = checked(16 << (i % 9), 16);
                                if i % 127 == 0 {
                                    escaped.push((p as usize, l));
                                } else {
                                    tx.send((p as usize, l)).unwrap();
                                }
                            }
                        }
                    }
                    drop(tx);
                    freer.join().unwrap();
                    escaped
                }));
            }
            for worker in workers {
                for (p, l) in worker.join().unwrap() {
                    unsafe {
                        assert!(std::slice::from_raw_parts(p as *const u8, l.size())
                            .iter()
                            .all(|&b| b == 0x5a));
                        RelaxAlloc.dealloc(p as *mut u8, l);
                    }
                }
            }
            trim();
            assert_eq!(stats(), before);
        }

        #[test]
        fn warm_chunks_are_reused_without_commit_and_bounded() {
            let _serial = lock(&TEST_LOCK);
            trim();
            let before = stats();
            let _scope = scratch(&crate::options::RuntimeOptions::default());
            unsafe {
                // a compile-like scope: a few classes, all freed at the end
                let mut blocks = Vec::new();
                for size in [16, 48, 200, 1000, 5000] {
                    blocks.push(checked(size, 16));
                }
                let chunks: Vec<usize> = blocks.iter().map(|(p, _)| (*p as usize) & !(CHUNK - 1)).collect();
                for (p, l) in blocks.drain(..) {
                    RelaxAlloc.dealloc(p, l);
                }
                let warm = stats();
                assert_eq!(warm.0, before.0 + 5 * CHUNK); // kept committed
                assert_eq!(warm.1, before.1);
                // the next scope's chunks come from the warm list: nothing newly committed
                for size in [16, 48, 200, 1000, 5000] {
                    blocks.push(checked(size, 16));
                }
                assert_eq!(stats().0, warm.0);
                for (p, _) in &blocks {
                    assert!(chunks.contains(&((*p as usize) & !(CHUNK - 1))));
                }
                for (p, l) in blocks.drain(..) {
                    RelaxAlloc.dealloc(p, l);
                }
                // a chunk touched beyond WARM_TOUCHED_MAX is decommitted when it empties
                let n = WARM_TOUCHED_MAX / 4096 + 2;
                for _ in 0..n {
                    blocks.push(checked(4096, 16));
                }
                let big = (blocks[0].0 as usize) & !(CHUNK - 1);
                for (p, l) in blocks.drain(..) {
                    RelaxAlloc.dealloc(p, l);
                }
                let index = (big - BASE.load(Ordering::Relaxed)) / CHUNK;
                assert_eq!(lock(&HEADERS[index].state).committed, 0);
            }
            trim();
            assert_eq!(stats(), before);
        }

        #[test]
        fn free_slots_reused_and_full_chunks_survive_escape() {
            let _serial = lock(&TEST_LOCK);
            trim();
            let before = stats();
            let mut blocks = Vec::new();
            {
                let _scope = scratch(&crate::options::RuntimeOptions::default());
                unsafe {
                    for _ in 0..(CHUNK / 2048 + 17) {
                        blocks.push(checked(2048, 16));
                    }
                    assert_eq!(stats().0, before.0 + 2 * CHUNK);
                    let (p, l) = blocks.pop().unwrap();
                    RelaxAlloc.dealloc(p, l);
                    let (reuse, layout) = checked(2048, 16);
                    assert_eq!(reuse, p);
                    blocks.push((reuse, layout));
                }
            }
            for (p, l) in blocks {
                unsafe {
                    RelaxAlloc.dealloc(p, l);
                }
            }
            trim();
            assert_eq!(stats(), before);
        }

        #[test]
        fn exhausted_reservation_falls_back_and_counting_wrapper_works() {
            let _serial = lock(&TEST_LOCK);
            trim();
            let before = stats();
            let _scope = scratch(&crate::options::RuntimeOptions::default());
            // Requesting more than the reservation must fail without altering pool state.
            let huge = Layout::from_size_align(RESERVE + CHUNK, 16).unwrap();
            assert!(unsafe { alloc(huge) }.is_null());
            // Temporarily occupy the virtual free list without committing payload pages.
            let run = lock(&POOL).take(MAX_ORDER).unwrap();
            unsafe {
                let l = Layout::from_size_align(123, 16).unwrap();
                let p = RelaxAlloc.alloc(l);
                assert!(!p.is_null() && !owns(p));
                RelaxAlloc.dealloc(p, l);
            }
            lock(&POOL).release(run, MAX_ORDER);
            unsafe {
                use crate::memstat::Counting;
                for align in [16, 4096] {
                    let l = Layout::from_size_align(123, align).unwrap();
                    let p = Counting.alloc_zeroed(l);
                    assert!(!p.is_null() && owns(p));
                    assert!(std::slice::from_raw_parts(p, 123).iter().all(|&b| b == 0));
                    std::ptr::write_bytes(p, 0x71, 123);
                    let q = Counting.realloc(p, l, 262145);
                    assert!(!q.is_null() && owns(q));
                    assert!(std::slice::from_raw_parts(q, 123)
                        .iter()
                        .all(|&b| b == 0x71));
                    Counting.dealloc(q, Layout::from_size_align(262145, align).unwrap());
                }
            }
            trim();
            assert_eq!(stats(), before);
        }
    }

    #[cfg(any(target_os = "macos", target_os = "linux"))]
    mod os {
        use std::ffi::c_void;
        #[cfg(target_os = "macos")]
        const ANON: i32 = 0x1000;
        #[cfg(target_os = "linux")]
        const ANON: i32 = 0x20;
        extern "C" {
            // mmap64 keeps the offset ABI identical on 32-bit Linux.
            #[cfg_attr(
                all(target_os = "linux", target_pointer_width = "32"),
                link_name = "mmap64"
            )]
            fn mmap(
                addr: *mut c_void,
                len: usize,
                prot: i32,
                flags: i32,
                fd: i32,
                off: i64,
            ) -> *mut c_void;
            fn munmap(addr: *mut c_void, len: usize) -> i32;
            fn mprotect(addr: *mut c_void, len: usize, prot: i32) -> i32;
            fn madvise(addr: *mut c_void, len: usize, advice: i32) -> i32;
        }
        pub unsafe fn reserve(size: usize, align: usize) -> usize {
            let p = mmap(std::ptr::null_mut(), size + align, 0, 2 | ANON, -1, 0);
            if p as isize == -1 {
                return 0;
            }
            let raw = p as usize;
            let base = (raw + align - 1) & !(align - 1);
            if base != raw {
                munmap(p, base - raw);
            }
            let tail = raw + size + align - (base + size);
            if tail != 0 {
                munmap((base + size) as *mut c_void, tail);
            }
            crate::memstat::name_mapping(base, size, c"relax-burst");
            base
        }
        pub unsafe fn commit(p: *mut u8, size: usize) -> bool {
            if mprotect(p.cast(), size, 1 | 2) != 0 {
                return false;
            }
            #[cfg(target_os = "macos")]
            {
                madvise(p.cast(), size, 8);
            } // MADV_FREE_REUSE, balances FREE_REUSABLE
            true
        }
        pub unsafe fn decommit(p: *mut u8, size: usize) -> bool {
            #[cfg(target_os = "macos")]
            const ADVICE: i32 = 7; // MADV_FREE_REUSABLE: removed from task footprint now
            #[cfg(target_os = "linux")]
            const ADVICE: i32 = 4; // MADV_DONTNEED
            if madvise(p.cast(), size, ADVICE) != 0 {
                return false;
            }
            // Keep the address reservation, and make stale payload access fault.
            mprotect(p.cast(), size, 0);
            true
        }
    }

    #[cfg(windows)]
    mod os {
        use std::ffi::c_void;
        #[link(name = "kernel32")]
        extern "system" {
            fn VirtualAlloc(addr: *mut c_void, size: usize, kind: u32, protect: u32)
                -> *mut c_void;
            fn VirtualFree(addr: *mut c_void, size: usize, kind: u32) -> i32;
        }
        pub unsafe fn reserve(size: usize, align: usize) -> usize {
            let raw = VirtualAlloc(std::ptr::null_mut(), size + align, 0x2000, 1) as usize;
            if raw == 0 {
                return 0;
            }
            // Windows cannot release reservation prefixes; retain the <=2 MB slop.
            (raw + align - 1) & !(align - 1)
        }
        pub unsafe fn commit(p: *mut u8, size: usize) -> bool {
            !VirtualAlloc(p.cast(), size, 0x1000, 4).is_null()
        }
        pub unsafe fn decommit(p: *mut u8, size: usize) -> bool {
            VirtualFree(p.cast(), size, 0x4000) != 0
        }
    }
}

#[cfg(any(target_os = "macos", target_os = "linux", windows))]
pub use arena::*;

// No TLS, reservation, environment read, or routing on wasm/unsupported targets.
#[cfg(not(any(target_os = "macos", target_os = "linux", windows)))]
mod disabled {
    use std::alloc::Layout;
    pub struct ScratchGuard;
    #[inline]
    pub fn scratch() -> ScratchGuard {
        ScratchGuard
    }
    #[inline]
    pub fn active() -> bool {
        false
    }
    #[inline]
    pub fn owns(_: *mut u8) -> bool {
        false
    }
    pub fn stats() -> (usize, usize, usize) {
        (0, 0, 0)
    }
    pub fn trim() {}
    pub unsafe fn alloc(_: Layout) -> *mut u8 {
        std::ptr::null_mut()
    }
    pub unsafe fn dealloc(_: *mut u8, _: Layout) {
        unreachable!()
    }
}
#[cfg(not(any(target_os = "macos", target_os = "linux", windows)))]
pub use disabled::*;
