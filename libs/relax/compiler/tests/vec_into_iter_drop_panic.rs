// vec::IntoIter's drop drops the items left as one slice and frees its buffer from a guard (alloc
// vec/into_iter.rs), so a panicking item drop neither leaks the items after it nor the buffer.
// Relax's dropped them one by one in a loop and freed the buffer after it: the unwind out of the
// loop skipped both (relax issue 162).

use std::alloc::{GlobalAlloc, Layout, System};
use std::cell::Cell;
use std::sync::atomic::{AtomicUsize, Ordering};

/// Counts the bytes live, all threads together; the test looks only at the difference across a
/// drop.
struct Counting;
static LIVE: AtomicUsize = AtomicUsize::new(0);

unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        LIVE.fetch_add(layout.size(), Ordering::SeqCst);
        unsafe { System.alloc(layout) }
    }
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        LIVE.fetch_sub(layout.size(), Ordering::SeqCst);
        unsafe { System.dealloc(ptr, layout) }
    }
}

#[global_allocator]
static GLOBAL: Counting = Counting;

thread_local!(static DROPS: Cell<u32> = Cell::new(0));

/// Counts its drops; the one numbered 0 panics in its drop.
struct Bomb(u32);
impl Drop for Bomb {
    fn drop(&mut self) {
        DROPS.with(|d| d.set(d.get() + 1));
        if self.0 == 0 {
            panic!("bomb");
        }
    }
}

#[test]
fn drop_drops_every_item_left_and_frees_the_buffer_even_past_a_panic() {
    let mut v: Vec<Bomb> = Vec::with_capacity(4096);
    v.extend([Bomb(1), Bomb(0), Bomb(2), Bomb(3), Bomb(4)]);
    let mut it = v.into_iter();
    assert_eq!(it.next().map(|b| b.0), Some(1));
    assert_eq!(DROPS.with(|d| d.replace(0)), 1);
    let before = LIVE.load(Ordering::SeqCst);
    assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| drop(it))).is_err());
    // the panicking item and the three after it
    assert_eq!(DROPS.with(|d| d.get()), 4);
    // the 4096-item buffer (16 KiB) went back; the panic keeps a few hundred bytes of its own
    // (rustc: 16025 bytes freed in all), so half the buffer tells a freed one from a leaked one
    let freed = before.saturating_sub(LIVE.load(Ordering::SeqCst));
    assert!(freed >= 4096 * std::mem::size_of::<Bomb>() / 2, "freed {freed} bytes");

    // (one test: a test on another thread would allocate across the byte count above)
    // without a panic, every item left is dropped
    DROPS.with(|d| d.set(0));
    let mut it = vec![Bomb(5), Bomb(6), Bomb(7), Bomb(8)].into_iter();
    assert_eq!(it.next_back().map(|b| b.0), Some(8));
    drop(it);
    assert_eq!(DROPS.with(|d| d.get()), 4);
    // zero-sized items and an empty iterator
    let it = vec![(); 10].into_iter();
    drop(it);
    let it: std::vec::IntoIter<String> = Vec::new().into_iter();
    drop(it);
}
