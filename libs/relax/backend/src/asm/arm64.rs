//! AArch64 instruction encoder for [`super`].

use super::{Ctx, Encoder, Tok};

#[derive(Default)]
pub struct Arm64 {}

impl Encoder for Arm64 {
    fn instruction(&mut self, _ctx: &mut Ctx, mnemonic: &str, _ops: &[Tok]) -> Result<(), String> {
        Err(format!("unsupported instruction `{}`", mnemonic))
    }
    fn directive(&mut self, _ctx: &mut Ctx, _name: &str, _args: &[Tok]) -> Result<bool, String> {
        Ok(false)
    }
    fn code_fill(&self, n: usize) -> Vec<u8> {
        let mut v = Vec::with_capacity(n);
        while v.len() + 4 <= n {
            v.extend_from_slice(&0xd503201fu32.to_le_bytes());
        }
        v.resize(n, 0);
        v
    }
}
