// The aarch64 NEON widening add across a vector: vaddlv_u8 (8 lanes) and vaddlvq_u8 (16 lanes).
// Each lane is widened to u16 before the add. The largest sum is 16 * 255 = 4080, which fits in
// u16, so the accumulator does not wrap. Of the aarch64 intrinsics str_indices 0.4.4 calls, this
// pair was the one Relax lacked; Red's buffer tests
// (https://github.com/codersauce/red) use that crate.
//
// Relax's std provides the scalar loops on every host, so `relax test` runs this here. rustc's
// std only has the intrinsics when the target is aarch64, and the two agree there.
#![cfg(any(relax, target_arch = "aarch64"))]
use std::arch::aarch64::*;

#[test]
fn widening_add_across_u8_matches_the_scalar_sum() {
    unsafe {
        assert_eq!(vaddlv_u8(vdup_n_u8(0)), 0);
        assert_eq!(vaddlvq_u8(vdupq_n_u8(0)), 0);
        assert_eq!(vaddlv_u8(vdup_n_u8(1)), 8);
        assert_eq!(vaddlvq_u8(vdupq_n_u8(1)), 16);
        assert_eq!(vaddlv_u8(vdup_n_u8(255)), 8 * 255);
        assert_eq!(vaddlvq_u8(vdupq_n_u8(255)), 16 * 255);
        assert_eq!(16 * 255, 4080);
        let wide: uint8x16_t = std::mem::transmute([
            0u8, 1, 2, 3, 250, 251, 252, 253, 254, 255, 7, 9, 128, 127, 64, 32,
        ]);
        let mut expect = 0u16;
        let lanes: [u8; 16] = std::mem::transmute(wide);
        for lane in lanes {
            expect += lane as u16;
        }
        assert_eq!(vaddlvq_u8(wide), expect);
        let narrow: uint8x8_t = std::mem::transmute([200u8, 100, 50, 25, 255, 0, 1, 2]);
        let mut expect8 = 0u16;
        let lanes8: [u8; 8] = std::mem::transmute(narrow);
        for lane in lanes8 {
            expect8 += lane as u16;
        }
        assert_eq!(vaddlv_u8(narrow), expect8);
        assert_eq!(expect8, 633);
    }
}
