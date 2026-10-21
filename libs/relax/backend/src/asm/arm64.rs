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

/// An arm64 register name (`x0`, `w20`, `lr`, `v0`, `q1`, `d8`, `s2` ..): the register and its
/// width in bits. Interim (ASMC-A64 replaces it).
pub fn parse_reg(name: &str) -> Option<(super::PReg, u8)> {
    let n = name.to_ascii_lowercase();
    if n == "lr" {
        return Some((super::PReg::int(30), 64));
    }
    let (c, k) = n.split_at(1);
    let k: u8 = k.parse().ok()?;
    match c {
        "x" if k <= 30 => Some((super::PReg::int(k), 64)),
        "w" if k <= 30 => Some((super::PReg::int(k), 32)),
        "v" | "q" if k < 32 => Some((super::PReg::vec(k), 128)),
        "d" if k < 32 => Some((super::PReg::vec(k), 64)),
        "s" if k < 32 => Some((super::PReg::vec(k), 32)),
        "h" if k < 32 => Some((super::PReg::vec(k), 16)),
        "b" if k < 32 => Some((super::PReg::vec(k), 8)),
        _ => None,
    }
}
