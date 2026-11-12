// core/slice: `as_array` / `as_mut_array` — the whole slice as an array reference (gpui's
// `TypeIdHasher` slices a hash to eight bytes and reads them as `[u8; 8]`).
#[test]
fn a01_as_array() {
    let s: &[u8] = &[1, 2, 3, 4];
    assert_eq!(s.as_array::<4>(), Some(&[1, 2, 3, 4]));
    assert_eq!(s.as_array::<3>(), None);
    assert_eq!(s.as_array::<5>(), None);
    let empty: &[u8] = &[];
    assert_eq!(empty.as_array::<0>(), Some(&[]));
}

#[test]
fn a02_as_mut_array() {
    let mut v = [1u8, 2, 3, 4];
    {
        let s: &mut [u8] = &mut v[..];
        let a = s.as_mut_array::<4>().unwrap();
        a[0] = 9;
    }
    assert_eq!(v, [9, 2, 3, 4]);
    let s: &mut [u8] = &mut v[..3];
    assert!(s.as_mut_array::<4>().is_none());
}
