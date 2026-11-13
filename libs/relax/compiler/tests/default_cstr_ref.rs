// `impl Default for &CStr` (core ffi/c_str.rs): the empty C string. clack-plugin 0.2's single-plug-in
// factory compares a plug-in id with `descriptor.id().unwrap_or_default()`.
use std::ffi::CStr;
#[test] fn t() {
    let none: Option<&CStr> = None;
    let id = none.unwrap_or_default();
    assert!(id.to_bytes().is_empty());
    assert_eq!(id.to_bytes_with_nul(), b"\0");
    let s: &mut str = Default::default();
    assert!(s.is_empty());
    let v: &mut [u8] = Default::default();
    assert!(v.is_empty());
    assert_eq!(<&CStr>::default(), c"");
}
