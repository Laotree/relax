// `<[T]>::array_windows::<N>()` (core slice/iter.rs ArrayWindows): overlapping `&[T; N]` windows from
// both ends, with exact lengths. epaint 0.37's `dashes_from_line` walks a path this way.
#[test] fn t() {
    let v = [1, 2, 3, 4, 5];
    let w: Vec<[i32; 2]> = v.array_windows::<2>().copied().collect();
    assert_eq!(w, [[1, 2], [2, 3], [3, 4], [4, 5]]);
    let mut it = v.array_windows::<3>();
    assert_eq!(it.len(), 3);
    assert_eq!(it.next_back(), Some(&[3, 4, 5]));
    assert_eq!(it.nth(1), Some(&[2, 3, 4]));
    assert_eq!(it.next(), None);
    assert_eq!(v.array_windows::<6>().count(), 0);
    assert_eq!(v.array_windows::<5>().last(), Some(&[1, 2, 3, 4, 5]));
    assert_eq!(v.array_windows::<2>().nth_back(1), Some(&[3, 4]));
    assert_eq!([0u8; 0].array_windows::<1>().len(), 0);
    let s: i32 = v.array_windows().map(|[a, b]| b - a).sum();
    assert_eq!(s, 4);
}
