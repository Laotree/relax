//! arm64 instruction decoder for [`super::dis`] (makepad inspect `asm`).

use super::dis::{Class, Insn};

/// Decodes `code` mapped at `addr`; see [`super::dis::decode`].
pub fn decode(code: &[u8], addr: u64) -> Vec<Insn> {
    let _ = addr;
    if code.is_empty() {
        return Vec::new();
    }
    vec![Insn { off: 0, len: code.len().min(255) as u8, mnem: ".byte".into(), ops: String::new(), class: Class::Unknown, target: None, pc_ref: None, mem: false, stack: false }]
}
