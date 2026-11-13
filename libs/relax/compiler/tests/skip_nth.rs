// `Skip::nth` hands the skip and `n` to the inner iterator as one `nth` (core iter/adapters/skip.rs),
// which a slice iterator answers in O(1). Without it the default `Iterator::nth` stepped `n` times
// through `next`, and `step_by` over a `skip` of a slice cost O(len) per element.

use std::cell::Cell;
use std::rc::Rc;

/// Counts the calls a `Skip` makes into it.
struct Counting {
    at: u32,
    end: u32,
    nexts: Rc<Cell<u32>>,
    nths: Rc<Cell<u32>>,
}

impl Counting {
    /// Counts 0..end; the counters of its `next` and `nth` calls.
    fn new(end: u32) -> (Counting, Rc<Cell<u32>>, Rc<Cell<u32>>) {
        let (nexts, nths) = (Rc::new(Cell::new(0)), Rc::new(Cell::new(0)));
        (Counting { at: 0, end, nexts: nexts.clone(), nths: nths.clone() }, nexts, nths)
    }
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
fn skip_and_nth_are_one_inner_nth() {
    let (inner, nexts, nths) = Counting::new(1000);
    let mut it = inner.skip(100);
    assert_eq!(it.nth(5), Some(105));
    assert_eq!((nexts.get(), nths.get()), (0, 1));
    // the skip is spent: the next nth is the inner one alone
    assert_eq!(it.nth(2), Some(108));
    assert_eq!((nexts.get(), nths.get()), (0, 2));
    assert_eq!(it.next(), Some(109));
}

#[test]
fn step_by_over_skip_never_steps_one_by_one() {
    let (inner, nexts, _) = Counting::new(1000);
    let got: Vec<u32> = inner.skip(3).step_by(10).take(5).collect();
    assert_eq!(got, [3, 13, 23, 33, 43]);
    assert_eq!(nexts.get(), 0);
}

#[test]
fn skip_nth_past_the_end() {
    let v = [1, 2, 3];
    assert_eq!(v.iter().skip(1).nth(1), Some(&3));
    assert_eq!(v.iter().skip(1).nth(2), None);
    assert_eq!(v.iter().skip(5).nth(0), None);
    // the sum of the skip and n overflows usize
    assert_eq!(v.iter().skip(usize::MAX).nth(usize::MAX), None);
    assert_eq!(v.iter().skip(2).nth(usize::MAX), None);
    let mut it = v.iter().skip(2);
    assert_eq!(it.nth(0), Some(&3));
    assert_eq!(it.next(), None);
}

#[test]
fn step_by_over_skip_of_a_slice() {
    let v: Vec<u32> = (0..20).collect();
    for skip in 0..22 {
        for step in 1..22 {
            let got: Vec<u32> = v.iter().skip(skip).step_by(step).copied().collect();
            let want: Vec<u32> = (skip as u32..20).step_by(step).collect();
            assert_eq!(got, want, "skip({skip}).step_by({step})");
        }
    }
}
