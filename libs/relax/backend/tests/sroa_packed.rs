//! SROA integer widening: a slot cell accessed as integers of different widths and offsets inside
//! one 8-byte cell (a Result<u32, E> copied into a Result<&[T], E> slot on the `?` path: a 4-byte
//! payload store, 8-byte loads and whole-slot copies at the same offset) is one register; loads
//! shift and truncate, narrow stores merge their bytes in. The promoted code must compute what the
//! slot version computes.
#![cfg(any(all(target_arch = "x86_64", unix), all(target_arch = "aarch64", unix)))]
use relax_backend::{exec::Code, rir::*};

#[cfg(target_arch = "x86_64")]
fn compile(f: &Func) -> Vec<u8> {
    let env = relax_backend::x64::Env { slots: SlotsPtr::NONE, tls_key: 0, tls_slow: 0, resume: 0, opt_regs: true, syms: 0, sym_class: 0, near: false };
    let c = relax_backend::x64::compile(&relax_session::Options::default(), f, &env).unwrap();
    c.code[..c.text_len as usize].to_vec()
}

#[cfg(target_arch = "aarch64")]
fn compile(f: &Func) -> Vec<u8> {
    let env = relax_backend::arm64::Env { slots: SlotsPtr::NONE, tls_key: 0, tls_slow: 0, resume: 0, opt_regs: true, syms: 0, sym_class: 0, near: false };
    let c = relax_backend::arm64::compile(&relax_session::Options::default(), f, &env).unwrap();
    c.code[..c.text_len as usize].to_vec()
}

fn push(f: &mut Func, i: Inst) {
    f.blocks[0].insts.push(i);
    f.blocks[0].pos.push(0);
}

/// f(a, b, c) over slots A, B (24 bytes each):
/// A[0..8] = a; A[8..16] = c; A[8..12] = b (u32); B = copy of A; B[11] = a (byte);
/// returns B[8..16] ^ (B[12..14] as i16 as i64) << 1 ^ (B[8..12] as i32 as i64) << 7 ^ B[9] << 3 ^ B[0..8]
fn build() -> Func {
    let mut f = Func::new("sroa_packed".into(), 0);
    let (a, b, c) = (f.vreg(Cls::I), f.vreg(Cls::I), f.vreg(Cls::I));
    f.params = vec![a, b, c];
    f.rets = vec![Cls::I];
    f.block();
    let (sa, sb) = (f.slot(24, 8), f.slot(24, 8));
    let (pa, pb) = (f.vreg(Cls::I), f.vreg(Cls::I));
    push(&mut f, Inst::SlotAddr(pa, sa));
    push(&mut f, Inst::SlotAddr(pb, sb));
    push(&mut f, Inst::Store(Mem::Int(8, false), pa, 0, a));
    push(&mut f, Inst::Store(Mem::Int(8, false), pa, 8, c));
    push(&mut f, Inst::Store(Mem::Int(4, false), pa, 8, b));
    push(&mut f, Inst::Copy(pb, pa, 24));
    push(&mut f, Inst::Store(Mem::Int(1, false), pb, 11, a));
    let v: Vec<VReg> = (0..14).map(|_| f.vreg(Cls::I)).collect();
    let u = IntTy { bits: 64, signed: false };
    push(&mut f, Inst::Load(Mem::Int(8, false), v[0], pb, 8));
    push(&mut f, Inst::Load(Mem::Int(2, true), v[1], pb, 12));
    push(&mut f, Inst::Load(Mem::Int(4, true), v[2], pb, 8));
    push(&mut f, Inst::Load(Mem::Int(1, false), v[3], pb, 9));
    push(&mut f, Inst::Load(Mem::Int(8, false), v[4], pb, 0));
    push(&mut f, Inst::IBinI(IOp::Shl, u, v[5], v[1], 1));
    push(&mut f, Inst::IBinI(IOp::Shl, u, v[6], v[2], 7));
    push(&mut f, Inst::IBinI(IOp::Shl, u, v[7], v[3], 3));
    push(&mut f, Inst::IBin(IOp::Xor, u, v[8], v[0], v[5]));
    push(&mut f, Inst::IBin(IOp::Xor, u, v[9], v[8], v[6]));
    push(&mut f, Inst::IBin(IOp::Xor, u, v[10], v[9], v[7]));
    push(&mut f, Inst::IBin(IOp::Xor, u, v[11], v[10], v[4]));
    f.blocks[0].term = Term::Ret(vec![v[11]]);
    f.verify().unwrap();
    f
}

fn reference(a: u64, b: u64, c: u64) -> u64 {
    let mut m = [0u8; 24];
    m[0..8].copy_from_slice(&a.to_le_bytes());
    m[8..16].copy_from_slice(&c.to_le_bytes());
    m[8..12].copy_from_slice(&(b as u32).to_le_bytes());
    m[11] = a as u8;
    let w = u64::from_le_bytes(m[8..16].try_into().unwrap());
    let h = i16::from_le_bytes(m[12..14].try_into().unwrap()) as i64 as u64;
    let s = i32::from_le_bytes(m[8..12].try_into().unwrap()) as i64 as u64;
    w ^ (h << 1) ^ (s << 7) ^ ((m[9] as u64) << 3) ^ a
}

#[test]
fn mixed_width_integer_cells_promote() {
    let mut f = build();
    assert!(relax_backend::passes::sroa(&mut f), "sroa promoted nothing:\n{}", f.dump());
    relax_backend::passes::dce(&mut f);
    f.verify().unwrap();
    let slots = f.blocks.iter().flat_map(|b| b.insts.iter()).filter(|i| matches!(i, Inst::SlotAddr(..) | Inst::Load(..) | Inst::Store(..) | Inst::Copy(..))).count();
    assert_eq!(slots, 0, "slot accesses left:\n{}", f.dump());
}

#[test]
fn promoted_packed_cells_compute_the_same_values() {
    type Entry = extern "C" fn(u64, u64, u64) -> u64;
    let inputs = [
        (0u64, 0u64, 0u64),
        (0x0123_4567_89ab_cdef, 0xfedc_ba98_7654_3210, 0x8000_7fff_ffff_0001),
        (u64::MAX, 0x8000_0000, 0xffff_8000_0000_0000),
        (0x80, 0x7fff_ffff, 0x0000_ffff_8000_0000),
    ];
    for promote in [false, true] {
        let mut f = build();
        if promote {
            assert!(relax_backend::passes::sroa(&mut f));
            relax_backend::passes::dce(&mut f);
        }
        let code = Code::new(&compile(&f)).unwrap();
        let run: Entry = unsafe { std::mem::transmute(code.ptr()) };
        for &(a, b, c) in &inputs {
            assert_eq!(run(a, b, c), reference(a, b, c), "promote={} inputs {:x} {:x} {:x}", promote, a, b, c);
        }
    }
}
