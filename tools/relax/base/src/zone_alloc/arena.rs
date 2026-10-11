use std::alloc::Layout;
use std::cell::{Cell, UnsafeCell};
use std::marker::PhantomData;
use std::ptr::null_mut;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};

pub const CHUNK: usize = 2 << 20;
const MAX_SHIFT: usize = 18; // 16 B .. 256 KB; >256 KB gets an exclusive mapping
// Size classes. The burst arena keeps powers of two. The compiler arena holds its blocks for a
// long time, so rounding every one up to a power of two would waste a quarter of its pages:
// it has 16-byte steps up to 128 B, then four steps per doubling (at most 25% above the
// request, 12% on average). Strides that are not powers of two only guarantee 16-byte alignment,
// so a request aligned wider than that takes the power-of-two class.
const CLASSES: usize = 8 + 4 * (MAX_SHIFT - 7);
const fn class_size(c: usize) -> usize {
    if c < 8 {
        (c + 1) * 16
    } else {
        let b = 7 + (c - 8) / 4;
        (1 << b) + ((c - 8) % 4 + 1) * ((1 << b) / 4)
    }
}
/// The smallest class whose size is at least `need` (16 <= need <= 256 KB).
fn class_for(need: usize) -> usize {
    if need <= 128 {
        (need.max(16) + 15) / 16 - 1
    } else {
        let b = (usize::BITS - 1 - (need - 1).leading_zeros()) as usize;
        let p = 1usize << b;
        let step = p / 4;
        8 + (b - 7) * 4 + (need - p + step - 1) / step - 1
    }
}
/// (class, stride) of a small request.
fn class_of(size: usize, align: usize) -> (usize, usize) {
    let need = size.max(align).max(16);
    let n = if COMPILER && align <= 16 { need } else { need.next_power_of_two() };
    let c = class_for(n);
    (c, class_size(c))
}
#[cfg(target_pointer_width = "64")]
const MAX_ORDER: usize = 15; // 64 GB of virtual address space, not resident memory
#[cfg(not(target_pointer_width = "64"))]
const MAX_ORDER: usize = 7; // 256 MB on 32-bit; exhaustion falls back to the heap
const N: usize = 1 << MAX_ORDER;
const RESERVE: usize = N * CHUNK;
const NONE: usize = usize::MAX;
// Compatible with 4/16/64 KB OS pages and Windows allocation granularity.
const PAGE: usize = 64 << 10;

/// Slow-path event counts (relaxed; the fast paths count nothing): contended lock acquisitions,
/// scheduler yields while waiting, commits, decommits, partial-list pushes and pops.
static EVENTS: [AtomicUsize; 9] = [const { AtomicUsize::new(0) }; 9];
// contended acquisitions by lock: 0 chunk state, 1 pool, 2 warm list, 3 partial list
const E_YIELD: usize = 4;
const E_COMMIT: usize = 5;
const E_DECOMMIT: usize = 6;
const E_PUSH: usize = 7;
const E_POP: usize = 8;
pub fn events() -> [usize; 9] {
    std::array::from_fn(|i| EVENTS[i].load(Ordering::Relaxed))
}
#[inline]
fn event(i: usize) {
    EVENTS[i].fetch_add(1, Ordering::Relaxed);
}

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
static WARM: Mutex<Warm> = Mutex::with_id(Warm { runs: [(0, 0); WARM_MAX], len: 0, bytes: 0 }, 2);

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
    id: usize,
    value: UnsafeCell<T>,
}
unsafe impl<T: Send> Sync for Mutex<T> {}
impl<T> Mutex<T> {
    const fn new(value: T) -> Self {
        Self::with_id(value, 0)
    }
    const fn with_id(value: T, id: usize) -> Self {
        Self {
            held: AtomicBool::new(false),
            id,
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
        if spins == 0 {
            event(m.id);
        }
        std::hint::spin_loop();
        spins += 1;
        if spins == 64 {
            event(E_YIELD);
            std::thread::yield_now();
            spins = 0;
        }
    }
}



/// Reserves the address range on first use. False when the OS refused (callers then fall back
/// to the system heap).
pub fn init() -> bool {
    if BASE.load(Ordering::Acquire) == 0 {
        let mut tried = lock(&INIT);
        if !*tried {
            *tried = true;
            BASE.store(unsafe { os::reserve(RESERVE, CHUNK) }, Ordering::Release);
        }
    }
    BASE.load(Ordering::Relaxed) != 0
}

pub fn scratch(runtime: &crate::options::RuntimeOptions) -> ScratchGuard {
    if !runtime.burst_arena {
        return ScratchGuard(false, PhantomData);
    }
    let entered = init() && DEPTH.try_with(|d| d.set(d.get() + 1)).is_ok();
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

/// (bytes touched, bytes in live slots, bytes in large blocks, chunks in the partial list):
/// touched - live slots = what small chunks hold free; slots - requested = rounding up to the class.
pub fn detail() -> (usize, usize, usize, usize) {
    let (mut touched, mut slots, mut large, mut listed) = (0, 0, 0, 0);
    for h in HEADERS.iter() {
        let s = lock(&h.state);
        if s.committed == 0 {
            continue;
        }
        if s.stride == 0 {
            large += s.committed;
        } else {
            touched += s.bump.min(CHUNK);
            slots += h.live.load(Ordering::Relaxed) * s.stride;
        }
        if h.in_part.load(Ordering::Relaxed) {
            listed += 1;
        }
    }
    (touched, slots, large, listed)
}

struct Chunk {
    live: AtomicUsize,
    /// Mirrors membership of the PARTIAL list (compiler arena); written under the PARTIAL lock.
    in_part: AtomicBool,
    state: Mutex<State>,
}
struct State {
    generation: u64,
    free: usize, // intrusive list in freed slots, protected even for remote frees
    bump: usize,
    stride: usize, // zero for an exclusive large allocation
    class: usize,
    /// A thread allocates from this chunk (it is that thread's current chunk for its class). Only
    /// detached chunks go to the partial list, so two threads never share one (compiler arena).
    attached: bool,
    committed: usize,
    run: usize,
    order: usize,
    bytes: usize, // requested bytes live in this chunk (stats only)
}
static HEADERS: [Chunk; N] = [const {
    Chunk {
        live: AtomicUsize::new(0),
        in_part: AtomicBool::new(false),
        state: Mutex::new(State {
            generation: 0,
            free: 0,
            bump: 0,
            stride: 0,
            class: 0,
            attached: false,
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
static POOL: Mutex<Pool> = Mutex::with_id(Pool::new(), 1);
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

// Compiler arena only: chunks that have free slots but are nobody's current chunk. The compiler
// holds most blocks for a long time, so a chunk rarely empties; without this list the slots
// freed in a chunk a thread has moved on from would never be reused. Membership, the links and
// the class live under the PARTIAL lock (a chunk lock may be held when taking it, never the
// other way round); `Chunk::in_part` is a lock-free filter for the common "already listed" case.
// Entries are index + 1 (0 = none) so the tables are zero-initialised.
struct Partial {
    heads: [u32; CLASSES],
    next: [u32; N],
    prev: [u32; N],
    class: [u8; N], // class + 1 while listed
}
static PARTIAL: Mutex<Partial> = Mutex::with_id(
    Partial {
        heads: [0; CLASSES],
        next: [0; N],
        prev: [0; N],
        class: [0; N],
    },
    3,
);
impl Partial {
    fn unlink(&mut self, i: usize) {
        let c = self.class[i];
        if c == 0 {
            return;
        }
        let (p, n) = (self.prev[i], self.next[i]);
        if p == 0 {
            self.heads[c as usize - 1] = n;
        } else {
            self.next[p as usize - 1] = n;
        }
        if n != 0 {
            self.prev[n as usize - 1] = p;
        }
        self.next[i] = 0;
        self.prev[i] = 0;
        self.class[i] = 0;
        HEADERS[i].in_part.store(false, Ordering::Relaxed);
    }
}

fn partial_push(i: usize, class: usize) {
    let mut p = lock(&PARTIAL);
    // a chunk that emptied meanwhile is on its way to the pool: never list it
    if p.class[i] != 0 || HEADERS[i].live.load(Ordering::Relaxed) == 0 {
        return;
    }
    event(E_PUSH);
    let h = p.heads[class];
    p.next[i] = h;
    p.prev[i] = 0;
    if h != 0 {
        p.prev[h as usize - 1] = i as u32 + 1;
    }
    p.heads[class] = i as u32 + 1;
    p.class[i] = class as u8 + 1;
    HEADERS[i].in_part.store(true, Ordering::Relaxed);
}

fn partial_pop(class: usize) -> Option<usize> {
    let mut p = lock(&PARTIAL);
    let h = p.heads[class];
    if h == 0 {
        return None;
    }
    let i = h as usize - 1;
    p.unlink(i);
    event(E_POP);
    Some(i)
}

/// Takes a slot from a listed chunk of `stride` and makes that chunk the thread's current one.
unsafe fn from_partial(i: usize, stride: usize, class: usize, requested: usize) -> *mut u8 {
    let h = &HEADERS[i];
    let mut s = lock(&h.state);
    if s.stride != stride || s.committed != CHUNK || h.live.load(Ordering::Relaxed) == 0 {
        return null_mut(); // reused for something else since it was listed
    }
    let p = if s.free != 0 {
        let p = s.free as *mut u8;
        s.free = *(p as *const usize);
        p
    } else if s.bump + s.stride <= CHUNK {
        let p = (BASE.load(Ordering::Relaxed) + i * CHUNK + s.bump) as *mut u8;
        s.bump += s.stride;
        p
    } else {
        return null_mut();
    };
    h.live.fetch_add(1, Ordering::Relaxed);
    s.bytes += requested;
    s.attached = true;
    let generation = s.generation;
    drop(s);
    CURRENT.with(|c| {
        let mut slots = c.get();
        slots[class] = Current { index: i, generation };
        c.set(slots);
    });
    p
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
    } else if s.bump + s.stride <= CHUNK {
        let p = (BASE.load(Ordering::Relaxed) + c.index * CHUNK + s.bump) as *mut u8;
        s.bump += s.stride;
        p
    } else {
        // full: the thread moves on, later frees into this chunk make it listable
        s.attached = false;
        return null_mut();
    };
    h.live.fetch_add(1, Ordering::Relaxed);
    s.bytes += requested;
    p
}

pub unsafe fn alloc(l: Layout) -> *mut u8 {
    let need = l.size().max(l.align()).max(16);
    let small = need <= 1 << MAX_SHIFT;
    let (class, stride) = if small { class_of(l.size(), l.align()) } else { (0, 0) };
    if small {
        let c = CURRENT.with(|c| c.get()[class]);
        let p = from_current(c, l.size());
        if !p.is_null() {
            return p;
        }
        if COMPILER {
            while let Some(i) = partial_pop(class) {
                let p = from_partial(i, stride, class, l.size());
                if !p.is_null() {
                    return p;
                }
            }
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
    if warm.is_none() {
        event(E_COMMIT);
    }
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
            class,
            attached: true,
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

/// A thread is ending: its current chunks go back to the partial list, so what it left free in
/// them is reused (compiler arena; a chunk is otherwise attached to its thread until it fills).
pub fn detach_thread() {
    if !COMPILER {
        return;
    }
    let Ok(mut slots) = CURRENT.try_with(|c| c.replace([NO_CURRENT; CLASSES])) else { return };
    for (class, c) in slots.iter_mut().enumerate() {
        if c.index == NONE {
            continue;
        }
        let h = &HEADERS[c.index];
        let mut s = lock(&h.state);
        if s.generation == c.generation && s.stride != 0 && s.attached && h.live.load(Ordering::Relaxed) != 0 {
            s.attached = false;
            if (s.free != 0 || s.bump + s.stride <= CHUNK) && !h.in_part.load(Ordering::Relaxed) {
                partial_push(c.index, class);
            }
        }
    }
}

/// Like `alloc`, zeroed. A large block of the compiler arena is zero when it comes out of the
/// pool (never committed, or decommitted with `zero`), so its pages stay untouched until used.
pub unsafe fn alloc_zeroed(l: Layout) -> *mut u8 {
    let p = alloc(l);
    if !p.is_null() && !(COMPILER && l.size().max(l.align()).max(16) > 1 << MAX_SHIFT) {
        std::ptr::write_bytes(p, 0, l.size());
    }
    p
}

/// Changes a block's size without moving it when the new size needs the same slot size (small
/// blocks) or the same mapping size (large ones). `old` is the layout it was allocated with.
pub unsafe fn resize_in_place(p: *mut u8, old: Layout, new_size: usize) -> bool {
    let address = (p as usize) & !(CHUNK - 1);
    let index = (address - BASE.load(Ordering::Relaxed)) / CHUNK;
    let mut s = lock(&HEADERS[index].state);
    let need = new_size.max(old.align()).max(16);
    let same = if s.stride != 0 {
        need <= 1 << MAX_SHIFT && class_of(new_size, old.align()).1 == s.stride
    } else if need <= 1 << MAX_SHIFT {
        false
    } else {
        // a large block owns a power-of-two run of chunks and commits only what it uses: it
        // grows and shrinks inside that run without moving
        let start = BASE.load(Ordering::Relaxed) + s.run * CHUNK;
        let span = (CHUNK << s.order) - (p as usize - start);
        match new_size.checked_add(PAGE - 1).map(|n| n & !(PAGE - 1)) {
            Some(nc) if nc == s.committed => true,
            Some(nc) if COMPILER && nc <= span => {
                let ok = if nc > s.committed {
                    os::commit((p as usize + s.committed) as *mut u8, nc - s.committed)
                } else {
                    os::decommit((p as usize + nc) as *mut u8, s.committed - nc, true)
                };
                if ok {
                    if nc > s.committed {
                        COMMITTED.fetch_add(nc - s.committed, Ordering::Relaxed);
                    } else {
                        COMMITTED.fetch_sub(s.committed - nc, Ordering::Relaxed);
                    }
                    let (was, now) = ((s.committed + CHUNK - 1) / CHUNK, (nc + CHUNK - 1) / CHUNK);
                    CHUNKS.fetch_add(now, Ordering::Relaxed);
                    CHUNKS.fetch_sub(was, Ordering::Relaxed);
                    s.committed = nc;
                }
                ok
            }
            _ => false,
        }
    };
    if same {
        s.bytes = s.bytes.wrapping_sub(old.size()).wrapping_add(new_size);
    }
    same
}

/// macOS: counts the pthread mutexes and condition variables std boxed in this arena (its
/// Mutex/Condvar allocate the pthread object on first lock). Returns (mutexes, condvars);
/// zero where std uses futexes. A chunk of 64-byte slots is scanned for the initialised
/// signatures, so it is an estimate (a stale freed slot can keep its old signature).
pub fn pthread_boxes() -> (usize, usize) {
    #[allow(unused_mut)]
    let (mut m, mut c) = (0, 0);
    #[cfg(target_os = "macos")]
    {
        let base = BASE.load(Ordering::Relaxed);
        if base == 0 {
            return (0, 0);
        }
        for (i, h) in HEADERS.iter().enumerate() {
            let s = lock(&h.state);
            if s.stride != 64 || h.live.load(Ordering::Relaxed) == 0 || s.committed != CHUNK {
                continue;
            }
            let mut off = 0;
            while off < s.bump.min(CHUNK) {
                let sig = unsafe { *((base + i * CHUNK + off) as *const usize) };
                match sig {
                    0x4D555458 => m += 1,
                    0x434F4E44 => c += 1,
                    _ => {}
                }
                off += 64;
            }
        }
    }
    (m, c)
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
        if COMPILER && s.stride != 0 && !s.attached && !h.in_part.load(Ordering::Relaxed) {
            partial_push(index, s.class);
        }
        return;
    }
    if COMPILER && h.in_part.load(Ordering::Relaxed) {
        lock(&PARTIAL).unlink(index);
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
    // A chunk of any kind goes back to the shared pool, where a later large block expects zeros
    // (alloc_zeroed skips the write): on macOS only the `zero` form guarantees that.
    // No live blocks and no allocation can pass this lock while decommitting. An old
    // TLS cache subsequently sees live == 0 or a different generation after reuse.
    event(E_DECOMMIT);
    if !os::decommit(address as *mut u8, s.committed, COMPILER) {
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
        event(E_DECOMMIT);
        if !unsafe { os::decommit(address as *mut u8, s.committed, COMPILER) } {
            continue; // quarantined, as in dealloc
        }
        COMMITTED.fetch_sub(s.committed, Ordering::Relaxed);
        CHUNKS.fetch_sub((s.committed + CHUNK - 1) / CHUNK, Ordering::Relaxed);
        s.committed = 0;
        let (run, order) = (s.run, s.order);
        drop(s);
        lock(&POOL).release(run, order);
    }
    if COMPILER {
        release_free_pages();
    }
}

/// Granule of the page release: a multiple of every OS page size in use (4 KB, 16 KB).
const GRANULE: usize = 16 << 10;

/// Compiler arena: gives the OS every granule of a small chunk whose slots are all free. Such a
/// granule's slots leave the free list for good (the chunk stays attached to its live blocks and
/// is released whole when they are gone); the rest of the free list is relinked. What malloc_trim
/// does for the system heap.
fn release_free_pages() {
    let base = BASE.load(Ordering::Relaxed);
    if base == 0 {
        return;
    }
    let mut free = [0u64; (CHUNK / 16) / 64];
    for index in 0..N {
        let h = &HEADERS[index];
        let mut s = lock(&h.state);
        if s.stride == 0 || s.committed != CHUNK || h.live.load(Ordering::Relaxed) == 0 || s.free == 0 {
            continue;
        }
        let (stride, chunk) = (s.stride, base + index * CHUNK);
        let nslots = s.bump / stride;
        free[..(nslots + 63) / 64].fill(0);
        let mut p = s.free;
        while p != 0 {
            let k = (p - chunk) / stride;
            free[k / 64] |= 1 << (k % 64);
            p = unsafe { *(p as *const usize) };
        }
        let is_free = |k: usize| free[k / 64] >> (k % 64) & 1 == 1;
        // granules whose overlapping slots are all free (a granule past the carved end only counts its carved part)
        let carved = s.bump;
        let mut run: Option<(usize, usize)> = None;
        let mut released = 0usize;
        let mut newhead = 0usize;
        // pass 1: find the dropped byte ranges and release them; remember them as a bitmap over granules
        let ngr = (carved + GRANULE - 1) / GRANULE;
        let mut gone_gr = [0u64; (CHUNK / GRANULE + 63) / 64];
        for g in 0..ngr {
            let (lo, hi) = (g * GRANULE, ((g + 1) * GRANULE).min(carved));
            let (k0, k1) = (lo / stride, (hi - 1) / stride);
            if (k0..=k1).all(|k| is_free(k)) {
                gone_gr[g / 64] |= 1 << (g % 64);
                run = match run {
                    Some((a, b)) if b == lo => Some((a, g * GRANULE + GRANULE)),
                    Some((a, b)) => {
                        released += b - a;
                        unsafe { os::release((chunk + a) as *mut u8, b - a) };
                        Some((lo, lo + GRANULE))
                    }
                    None => Some((lo, lo + GRANULE)),
                };
            }
        }
        if let Some((a, b)) = run {
            released += b - a;
            unsafe { os::release((chunk + a) as *mut u8, b - a) };
        }
        if released == 0 {
            continue;
        }
        // pass 2: relink the free slots that do not touch a dropped granule
        let dropped = |k: usize| {
            let (g0, g1) = (k * stride / GRANULE, ((k + 1) * stride - 1) / GRANULE);
            (g0..=g1).any(|g| gone_gr[g / 64] >> (g % 64) & 1 == 1)
        };
        for k in (0..nslots).rev() {
            if is_free(k) && !dropped(k) {
                let slot = chunk + k * stride;
                unsafe { *(slot as *mut usize) = newhead };
                newhead = slot;
            }
        }
        s.free = newhead;
    }
}


#[cfg(any(target_os = "macos", target_os = "linux", target_os = "android"))]
mod os {
    use std::ffi::c_void;
    #[cfg(target_os = "macos")]
    const ANON: i32 = 0x1000;
    #[cfg(any(target_os = "linux", target_os = "android"))]
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
        crate::memstat::name_mapping(base, size, super::LABEL);
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
    /// `zero`: the next commit of this range must read as zeros (macOS only needs work for it:
    /// MADV_FREE_REUSABLE keeps the old bytes until the kernel reclaims them, so the range is
    /// replaced by a fresh PROT_NONE mapping, which also drops its pages at once).
    /// Returns the pages to the OS and keeps the mapping readable and writable.
    pub unsafe fn release(p: *mut u8, size: usize) -> bool {
        #[cfg(target_os = "macos")]
        const ADVICE: i32 = 7; // MADV_FREE_REUSABLE
        #[cfg(any(target_os = "linux", target_os = "android"))]
        const ADVICE: i32 = 4; // MADV_DONTNEED
        madvise(p.cast(), size, ADVICE) == 0
    }
    pub unsafe fn decommit(p: *mut u8, size: usize, zero: bool) -> bool {
        #[cfg(target_os = "macos")]
        const ADVICE: i32 = 7; // MADV_FREE_REUSABLE: removed from task footprint now
        #[cfg(any(target_os = "linux", target_os = "android"))]
        const ADVICE: i32 = 4; // MADV_DONTNEED
        #[cfg(target_os = "macos")]
        if zero {
            // MAP_PRIVATE | MAP_ANON | MAP_FIXED
            return mmap(p.cast(), size, 0, 2 | ANON | 0x10, -1, 0) as usize == p as usize;
        }
        let _ = zero;
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
    pub unsafe fn release(p: *mut u8, size: usize) -> bool {
        !VirtualAlloc(p.cast(), size, 0x80000, 4).is_null() // MEM_RESET
    }
    pub unsafe fn decommit(p: *mut u8, size: usize, _zero: bool) -> bool {
        VirtualFree(p.cast(), size, 0x4000) != 0
    }
}
