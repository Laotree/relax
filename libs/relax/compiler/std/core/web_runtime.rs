//! Program implementations of lowering helpers for the web target. No host ABI.

pub unsafe fn str_eq(a: *const u8, an: usize, b: *const u8, bn: usize) -> bool {
    if an != bn { return false; }
    let mut i = 0;
    while i < an {
        if *a.add(i) != *b.add(i) { return false; }
        i += 1;
    }
    true
}

/// Binary long division without recursively using the u128 division operator.
/// Lowering checks division by zero and signed MIN / -1 before calling this.
pub fn divrem128(mode: u64, alo: u64, ahi: u64, blo: u64, bhi: u64) -> u128 {
    let mut a = ((ahi as u128) << 64) | alo as u128;
    let mut b = ((bhi as u128) << 64) | blo as u128;
    let aneg = mode & 2 != 0 && ahi >> 63 != 0;
    let bneg = mode & 2 != 0 && bhi >> 63 != 0;
    if aneg { a = (!a).wrapping_add(1); }
    if bneg { b = (!b).wrapping_add(1); }
    let mut q = 0u128;
    let mut r = 0u128;
    let mut i = 128u32;
    while i != 0 {
        i -= 1;
        let carry = r >> 127 != 0;
        r = (r << 1) | ((a >> i) & 1);
        if carry || r >= b {
            r = r.wrapping_sub(b);
            q |= 1u128 << i;
        }
    }
    let rem = mode & 1 != 0;
    let result = if rem { r } else { q };
    if if rem { aneg } else { aneg != bneg } { (!result).wrapping_add(1) } else { result }
}

#[relax(keep_reachable)]
pub unsafe fn panic_site(msg: *const u8, len: usize, file: *const u8, file_len: usize, line: u32, col: u32) -> ! {
    let msg = crate::str::from_utf8_unchecked(crate::slice::from_raw_parts(msg, len));
    let loc = crate::panic::Location::internal_constructor(crate::slice::from_raw_parts(file, file_len), line, col);
    crate::panicking::panic_at(format_args!("{}", msg), &loc)
}

#[relax(keep_reachable)]
pub unsafe fn panic_bounds(index: usize, len: usize, file: *const u8, file_len: usize, line: u32, col: u32) -> ! {
    let loc = crate::panic::Location::internal_constructor(crate::slice::from_raw_parts(file, file_len), line, col);
    crate::panicking::panic_at(format_args!("index out of bounds: the len is {} but the index is {}", len, index), &loc)
}
