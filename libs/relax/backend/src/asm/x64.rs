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

/// An x64 register name (`rax`, `eax`, `al`, `ah`, `r12d`, `xmm3`, `ymm1` ..): the register, its
/// width in bits and whether it is a high byte register (ah .. bh). Interim (ASMC-X64 replaces it).
pub fn parse_reg(name: &str) -> Option<(super::PReg, u8, bool)> {
    let n = name.to_ascii_lowercase();
    const Q: [&str; 16] = ["rax", "rcx", "rdx", "rbx", "rsp", "rbp", "rsi", "rdi", "r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15"];
    const D: [&str; 16] = ["eax", "ecx", "edx", "ebx", "esp", "ebp", "esi", "edi", "r8d", "r9d", "r10d", "r11d", "r12d", "r13d", "r14d", "r15d"];
    if let Some(i) = Q.iter().position(|x| *x == n) {
        return Some((super::PReg::int(i as u8), 64, false));
    }
    if let Some(i) = D.iter().position(|x| *x == n) {
        return Some((super::PReg::int(i as u8), 32, false));
    }
    if let Some(k) = n.strip_prefix("xmm").and_then(|k| k.parse::<u8>().ok()).filter(|k| *k < 32) {
        return Some((super::PReg::vec(k), 128, false));
    }
    None
}
