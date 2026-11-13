// The iterators that core gives an `nth` (or `advance_by`) of its own hand the skip to the inner
// iterator in one call: `Fuse`, `Chain`, `Peekable` and `StepBy` (iter/adapters), slice and
// VecDeque iterators (advance_by in O(1)) and array::IntoIter (drops the skipped items). Relax's
// std lacked these, so the default `nth` stepped `n` times through `next`: a `step_by` over any of
// them cost O(step) per element instead of O(1), the shape that made `Skip` (skip_nth.rs) quadratic.

use std::cell::Cell;
use std::collections::VecDeque;
use std::rc::Rc;

/// Counts 0..end and the `next` and `nth` calls made into it.
struct Counting {
    at: u32,
    end: u32,
    nexts: Rc<Cell<u32>>,
    nths: Rc<Cell<u32>>,
}

fn counting(end: u32) -> (Counting, Rc<Cell<u32>>, Rc<Cell<u32>>) {
    let (nexts, nths) = (Rc::new(Cell::new(0)), Rc::new(Cell::new(0)));
    (Counting { at: 0, end, nexts: nexts.clone(), nths: nths.clone() }, nexts, nths)
}

impl Iterator for Counting {
    type Item = u32;
    fn next(&mut self) -> Option<u32> {
        self.nexts.set(self.nexts.get() + 1);
        if self.at < self.end {
            self.at += 1;
            Some(self.at - 1)
        } else {
            None
        }
    }
    fn nth(&mut self, n: usize) -> Option<u32> {
        self.nths.set(self.nths.get() + 1);
        let target = (self.at as usize).saturating_add(n);
        if target < self.end as usize {
            self.at = target as u32 + 1;
            Some(target as u32)
        } else {
            self.at = self.end;
            None
        }
    }
}

#[test]
fn fuse_nth_is_one_inner_nth() {
    let (inner, nexts, nths) = counting(100);
    let mut it = inner.fuse();
    assert_eq!(it.nth(40), Some(40));
    assert_eq!(it.nth(100), None);
    assert_eq!(it.nth(0), None);
    // fused: the exhausted inner iterator is not asked again
    assert_eq!((nexts.get(), nths.get()), (0, 2));
    let got: Vec<u32> = counting(50).0.fuse().step_by(7).collect();
    assert_eq!(got, [0, 7, 14, 21, 28, 35, 42, 49]);
}

#[test]
fn peekable_nth_counts_the_peeked_item() {
    let (inner, nexts, nths) = counting(100);
    let mut it = inner.peekable();
    assert_eq!(it.peek(), Some(&0));
    assert_eq!(it.nth(0), Some(0));
    assert_eq!(it.peek(), Some(&1));
    assert_eq!(it.nth(5), Some(6));
    assert_eq!(it.nth(3), Some(10));
    // two peeks, then two inner nths
    assert_eq!((nexts.get(), nths.get()), (2, 2));
    let mut it = [1, 2].iter().peekable();
    assert_eq!(it.nth(5), None);
    assert_eq!(it.peek(), None);
}

#[test]
fn step_by_nth_is_one_inner_nth() {
    let (inner, nexts, nths) = counting(1000);
    let mut it = inner.step_by(10);
    assert_eq!(it.nth(3), Some(30));
    assert_eq!((nexts.get(), nths.get()), (1, 1));
    assert_eq!(it.nth(2), Some(60));
    assert_eq!((nexts.get(), nths.get()), (1, 2));
    assert_eq!(it.next(), Some(70));
    assert_eq!(it.nth(100), None);
    let v: Vec<u32> = (0..100).collect();
    assert_eq!(v.iter().step_by(9).nth(0), Some(&0));
    assert_eq!(v.iter().step_by(9).nth(11), Some(&99));
    assert_eq!(v.iter().step_by(9).nth(12), None);
    assert_eq!(v.iter().step_by(usize::MAX).nth(1), None);
    assert_eq!(v.iter().step_by(2).nth(usize::MAX), None);
    let mut it = v.iter().step_by(3);
    it.next();
    assert_eq!(it.nth(usize::MAX), None);
}

#[test]
fn chain_nth_goes_to_the_second_in_one_nth() {
    let (b, nexts, nths) = counting(100);
    let a = [100u32, 101, 102];
    let mut it = a.iter().copied().chain(b);
    assert_eq!(it.nth(1), Some(101));
    assert_eq!(it.nth(3), Some(2));
    assert_eq!(it.nth(4), Some(7));
    assert_eq!((nexts.get(), nths.get()), (0, 2));
    let x: Vec<u32> = (0..10).collect();
    let y: Vec<u32> = (10..25).collect();
    for n in 0..30 {
        let want = if n < 25 { Some(n as u32) } else { None };
        assert_eq!(x.iter().chain(y.iter()).nth(n).copied(), want);
    }
    let got: Vec<u32> = x.iter().chain(y.iter()).step_by(4).copied().collect();
    assert_eq!(got, [0, 4, 8, 12, 16, 20, 24]);
    let mut it = x.iter().chain(y.iter());
    assert_eq!(it.nth(12), Some(&12));
    assert_eq!(it.next(), Some(&13));
}

#[test]
fn vec_deque_nth_across_both_halves() {
    let mut d: VecDeque<u32> = VecDeque::with_capacity(8);
    for i in 0..6 {
        d.push_back(i);
    }
    for _ in 0..4 {
        d.pop_front();
    }
    for i in 6..12 {
        d.push_back(i);
    }
    // the deque wraps: 4..12 lies in two slices
    assert!(!d.as_slices().1.is_empty());
    for n in 0..10 {
        let want = if n < 8 { Some(4 + n as u32) } else { None };
        assert_eq!(d.iter().nth(n).copied(), want);
    }
    let got: Vec<u32> = d.iter().step_by(3).copied().collect();
    assert_eq!(got, [4, 7, 10]);
    let mut it = d.iter_mut();
    *it.nth(5).unwrap() += 100;
    assert_eq!(it.next(), Some(&mut 10));
    assert_eq!(d[5], 109);
}

#[test]
fn array_into_iter_nth_drops_the_skipped() {
    let drops = Rc::new(Cell::new(0));
    struct D(u32, Rc<Cell<u32>>);
    impl Drop for D {
        fn drop(&mut self) {
            self.1.set(self.1.get() + 1);
        }
    }
    let arr = [0, 1, 2, 3, 4, 5].map(|i| D(i, drops.clone()));
    let mut it = arr.into_iter();
    let third = it.nth(2).unwrap();
    assert_eq!(third.0, 2);
    assert_eq!(drops.get(), 2);
    drop(third);
    assert_eq!(drops.get(), 3);
    assert!(it.nth(5).is_none());
    assert_eq!(drops.get(), 6);
    let got: Vec<u32> = [0u32, 1, 2, 3, 4, 5, 6].into_iter().step_by(3).collect();
    assert_eq!(got, [0, 3, 6]);
}
