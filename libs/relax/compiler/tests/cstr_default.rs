use std::ffi::CStr;

#[test]
fn default_cstr_is_empty() {
    let c: &CStr = Default::default();
    assert_eq!(c.to_bytes(), b"");
    assert_eq!(c.to_bytes_with_nul(), b"\0");
}
