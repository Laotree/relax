//! x86-64 instruction encoder for [`super`] (Intel syntax, the asm! default; AT&T with
//! `options(att_syntax)` / `.att_syntax`).

use super::{Ctx, Encoder, Tok};

#[derive(Default)]
pub struct X64 {}

impl Encoder for X64 {
    fn instruction(&mut self, _ctx: &mut Ctx, mnemonic: &str, _ops: &[Tok]) -> Result<(), String> {
        Err(format!("unsupported instruction `{}`", mnemonic))
    }
    fn directive(&mut self, ctx: &mut Ctx, name: &str, _args: &[Tok]) -> Result<bool, String> {
        match name {
            ".intel_syntax" => ctx.att = false,
            ".att_syntax" => ctx.att = true,
            ".code64" => {}
            _ => return Ok(false),
        }
        Ok(true)
    }
    fn code_fill(&self, n: usize) -> Vec<u8> {
        vec![0x90; n]
    }
}
