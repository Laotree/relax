//! `isolate_lowest_one` and `isolate_highest_one` on the unsigned integers and NonZero.
use std::num::{NonZeroU32, NonZeroU8};

#[test]
fn isolate_one_bit() {
    assert_eq!(12usize.isolate_lowest_one(), 4);
    assert_eq!(12usize.isolate_highest_one(), 8);
    assert_eq!(40u32.isolate_lowest_one(), 8);
    assert_eq!(40u32.isolate_highest_one(), 32);
    assert_eq!(0x80u8.isolate_lowest_one(), 0x80);
    assert_eq!(0x80u8.isolate_highest_one(), 0x80);
    assert_eq!(0u64.isolate_lowest_one(), 0);
    assert_eq!(0u64.isolate_highest_one(), 0);
    assert_eq!(u128::MAX.isolate_highest_one(), 1 << 127);
    assert_eq!(u128::MAX.isolate_lowest_one(), 1);
    let n = NonZeroU32::new(40).unwrap();
    assert_eq!(n.isolate_lowest_one().get(), 8);
    assert_eq!(n.isolate_highest_one().get(), 32);
    let b = NonZeroU8::new(0x80).unwrap();
    assert_eq!(b.isolate_lowest_one().get(), 0x80);
    assert_eq!(b.isolate_highest_one().get(), 0x80);
}
