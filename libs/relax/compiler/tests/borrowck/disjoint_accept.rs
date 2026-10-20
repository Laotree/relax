// Disjoint indices (relaxed Rust D3): two borrows of elements of one array / slice / Vec that NLL
// rejects (stable rustc: E0499 / E0502). Relaxed crates accept them when the indices are proven
// distinct, and otherwise compare them when the code runs (an overlap panics as
// `get_disjoint_mut(..).unwrap()` does). main() runs every case without an overlap.

// i vs i + 1 through Vec's IndexMut
fn add_next(v: &mut Vec<u32>, i: usize) {
    let a = &mut v[i];
    let b = &mut v[i + 1]; //~ PROVEN
    *a += *b;
}

// constant indices of an array
fn swap01(a: &mut [u32; 4]) {
    let x = &mut a[0];
    let y = &mut a[1]; //~ PROVEN
    std::mem::swap(x, y);
}

// unknown indices of a slice: checked when this runs
fn swap_any(s: &mut [u32], i: usize, j: usize) {
    let x = &mut s[i];
    let y = &mut s[j]; //~ CHECKED
    std::mem::swap(x, y);
}

// an index computed into a local first
fn add_prev(v: &mut Vec<u32>, i: usize) {
    let j = i - 1;
    let a = &mut v[j];
    let b = &mut v[i]; //~ PROVEN
    *b += *a;
}

// a shared and a mutable borrow
fn copy_two_on(v: &mut [u32], i: usize) -> u32 {
    let a = &v[i];
    let b = &mut v[i + 2]; //~ PROVEN
    *b = *a;
    *b
}

// in a loop, i vs i + 1 in each iteration
fn prefix_sums(v: &mut Vec<u32>) {
    for i in 0..v.len() - 1 {
        let a = &mut v[i];
        let b = &mut v[i + 1]; //~ PROVEN
        *b += *a;
    }
}

// the outer indices of a nested array differ
fn cross(m: &mut [[u32; 2]; 2]) {
    let a = &mut m[0][1];
    let b = &mut m[1][0]; //~ PROVEN
    *a += *b;
}

// loop-carried: j > i from the range i + 1..n
fn pairs_above(v: &mut Vec<u32>) {
    for i in 0..v.len() {
        for j in i + 1..v.len() {
            let a = &mut v[i];
            let b = &mut v[j]; //~ PROVEN
            *a += *b;
        }
    }
}

// loop-carried: j < i from the range 0..i
fn pairs_below(v: &mut [u32]) {
    for i in 0..v.len() {
        for j in 0..i {
            let a = &mut v[j];
            let b = &mut v[i]; //~ PROVEN
            *b += *a;
        }
    }
}

// j >= i only: checked when this runs
fn pairs_from(v: &mut [u32]) {
    for i in 0..v.len() {
        for j in i + 1..v.len() {
            let a = &mut v[j - 1];
            let b = &mut v[j]; //~ PROVEN
            *b += *a;
        }
        for j in i..i {
            let a = &mut v[i];
            let b = &mut v[j]; //~ CHECKED
            *b += *a;
        }
    }
}

fn main() {
    let mut v = vec![1, 2, 3];
    add_next(&mut v, 0);
    assert_eq!(v, [3, 2, 3]);
    let mut a = [1, 2, 3, 4];
    swap01(&mut a);
    assert_eq!(a, [2, 1, 3, 4]);
    swap_any(&mut a, 0, 3);
    assert_eq!(a, [4, 1, 3, 2]);
    add_prev(&mut v, 2);
    assert_eq!(v, [3, 2, 5]);
    let mut s = [7, 0, 0];
    assert_eq!(copy_two_on(&mut s, 0), 7);
    let mut p = vec![1, 1, 1, 1];
    prefix_sums(&mut p);
    assert_eq!(p, [1, 2, 3, 4]);
    let mut m = [[1, 2], [3, 4]];
    cross(&mut m);
    assert_eq!(m, [[1, 5], [3, 4]]);
    let mut t = vec![1, 2, 3];
    pairs_above(&mut t);
    assert_eq!(t, [6, 5, 3]);
    let mut u = [1, 1, 1];
    pairs_below(&mut u);
    assert_eq!(u, [1, 2, 4]);
    let mut w = [1, 1, 1];
    pairs_from(&mut w);
    assert_eq!(w, [1, 2, 5]);
    println!("disjoint_accept ok");
}
