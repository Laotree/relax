//! Gaps a whole-function selftest found in the std surface: the golden ratio, two aarch64
//! NEON intrinsics, and the Cow<OsStr> comparisons zip uses.
use std::borrow::Cow;
use std::ffi::OsStr;

#[test]
fn golden_ratio() {
    assert_eq!(std::f64::consts::GOLDEN_RATIO, 1.618033988749895_f64);
    assert_eq!(std::f32::consts::GOLDEN_RATIO, 1.618033988749895_f32);
}

#[test]
fn cow_os_str_compares_with_references() {
    let c: Cow<'_, OsStr> = Cow::Borrowed(OsStr::new("."));
    assert!(c == OsStr::new("."));
    assert!(OsStr::new(".") == c);
    let owned: Cow<'_, OsStr> = Cow::Owned(std::ffi::OsString::from(".."));
    assert!(owned != OsStr::new("."));
    assert!(!c.is_empty());
}

#[cfg(target_arch = "aarch64")]
#[test]
fn neon_add_across_and_reciprocal_estimate() {
    use std::arch::aarch64::*;
    unsafe {
        assert_eq!(vaddlvq_u8(vdupq_n_u8(1)), 16);
        assert_eq!(vaddlvq_u8(vdupq_n_u8(255)), 4080);
        let r = vrecpeq_f32(vdupq_n_f32(0.5));
        assert!((vgetq_lane_f32(r, 0) - 2.0).abs() < 0.02);
        let step = vrecpsq_f32(vdupq_n_f32(0.5), vdupq_n_f32(2.0));
        assert_eq!(vgetq_lane_f32(step, 0), 1.0);
    }
}
