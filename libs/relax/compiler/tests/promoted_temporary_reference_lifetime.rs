//! References to projections of promotable temporaries must remain valid after the
//! function that creates them returns. In particular, the backing array for
//! `&[4, 8, 16][..]` must not reside in that function's stack frame.

use std::num::NonZeroUsize;

#[inline(never)]
fn full_array_slice() -> &'static [usize] {
    &[4, 8, 16][..]
}

#[inline(never)]
fn array_subslice(start: usize, end: usize) -> &'static [usize] {
    &[10, 20, 30, 40][start..end]
}

#[inline(never)]
fn array_element(index: usize) -> &'static usize {
    &[10, 20, 30, 40][index]
}

#[inline(never)]
fn repeated_array_slice() -> &'static [usize] {
    &[4; 3][..]
}

#[allow(dead_code)]
struct Pair {
    first: usize,
    second: usize,
}

#[inline(never)]
fn struct_field() -> &'static usize {
    &Pair {
        first: 23,
        second: 42,
    }
    .second
}

// Reuse stack space after the reference-producing function returns. Calls through
// black_box below keep rustc from folding the returned references into the tests.
#[inline(never)]
fn overwrite_stack() {
    let mut values = [0usize; 1024];
    for i in 0..values.len() {
        values[i] = i + 1000;
    }
    std::hint::black_box(&values);
}

#[test]
fn array_literal_slice_outlives_its_function() {
    let make_slice = std::hint::black_box(full_array_slice as fn() -> &'static [usize]);
    let slice = make_slice();
    overwrite_stack();
    assert_eq!(slice, &[4, 8, 16]);

    // The original report cloned this slice before checking each lane.
    let lanes = slice.to_vec();
    assert_eq!(lanes, [4, 8, 16]);
    for lane in lanes {
        NonZeroUsize::new(lane).expect("validated vector lane count is non-zero");
    }
}

#[test]
fn dynamically_indexed_array_projections_outlive_their_function() {
    let make_slice = std::hint::black_box(array_subslice as fn(usize, usize) -> &'static [usize]);
    let make_element = std::hint::black_box(array_element as fn(usize) -> &'static usize);
    let slice = make_slice(1, 3);
    let element = make_element(2);
    overwrite_stack();
    assert_eq!(slice, &[20, 30]);
    assert_eq!(*element, 30);
}

#[test]
fn repeated_array_slice_outlives_its_function() {
    let make_slice = std::hint::black_box(repeated_array_slice as fn() -> &'static [usize]);
    let slice = make_slice();
    overwrite_stack();
    assert_eq!(slice, &[4, 4, 4]);
}

#[test]
fn struct_literal_field_outlives_its_function() {
    let make_field = std::hint::black_box(struct_field as fn() -> &'static usize);
    let field = make_field();
    overwrite_stack();
    assert_eq!(*field, 42);
}

#[test]
fn mutable_temporary_ranges_are_independent() {
    let one = &mut [1, 2, 3][..];
    one[0] = 99;
    let two = &mut [1, 2, 3][..];
    assert_eq!(one, &[99, 2, 3]);
    assert_eq!(two, &[1, 2, 3]);
}

#[test]
fn nonconstant_array_elements_are_evaluated_each_time() {
    let mut calls = 0;
    for expected in 1..=3 {
        let values = &[
            {
                calls += 1;
                calls
            },
            5,
        ][..];
        assert_eq!(values, &[expected, 5]);
    }
    assert_eq!(calls, 3);

    let repeated = &[{
        calls += 1;
        calls
    }; 3][..];
    assert_eq!(repeated, &[4, 4, 4]);
    assert_eq!(calls, 4);
}
