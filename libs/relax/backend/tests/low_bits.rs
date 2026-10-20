//! Narrow results whose upper register bits nobody reads skip their re-extension
//! (passes::low_bits_only): a u8 subtract stored back as a byte, and a u8 cast used as a 64-bit
//! shift count. A narrow value that is also compared keeps its extension. Results must equal
//! Rust's.
#![cfg(any(all(target_arch = "x86_64", unix), all(target_arch = "aarch64", unix)))]
use relax_backend::{exec::Code, rir::*};

#[cfg(target_arch = "x86_64")]
fn compile(f: &Func) -> Vec<u8> {
    let env = relax_backend::x64::Env { slots: SlotsPtr::NONE, tls_key: 0, tls_slow: 0, resume: 0, opt_regs: true, syms: 0, sym_class: 0 };
    let c = relax_backend::x64::compile(&relax_session::Options::default(), f, &env).unwrap();
    c.code[..c.text_len as usize].to_vec()
}

#[cfg(target_arch = "aarch64")]
fn compile(f: &Func) -> Vec<u8> {
    let env = relax_backend::arm64::Env { slots: SlotsPtr::NONE, tls_key: 0, tls_slow: 0, resume: 0, opt_regs: true, syms: 0, sym_class: 0 };
    let c = relax_backend::arm64::compile(&relax_session::Options::default(), f, &env).unwrap();
    c.code[..c.text_len as usize].to_vec()
}

fn push(f: &mut Func, b: u32, i: Inst) {
    f.blocks[b as usize].insts.push(i);
    f.blocks[b as usize].pos.push(0);
}

/// f(p, x, n): p[0] = (p[0] as u8 - n as u8); s = x >> (n as u8) (64-bit shift); c = (x as u8 - n as u8);
/// returns s + (c < 16) + p[0] (the stored byte read back)
fn build() -> Func {
    let u8t = IntTy { bits: 8, signed: false };
    let w = IntTy { bits: 64, signed: false };
    let mut f = Func::new("low_bits".into(), 0);
    let (p, x, n) = (f.vreg(Cls::I), f.vreg(Cls::I), f.vreg(Cls::I));
    f.params = vec![p, x, n];
    f.rets = vec![Cls::I];
    let b = f.block();
    let v: Vec<VReg> = (0..12).map(|_| f.vreg(Cls::I)).collect();
    push(&mut f, b, Inst::Conv(Conv::IntToInt(u8t), v[0], n));
    push(&mut f, b, Inst::Load(Mem::Int(1, false), v[1], p, 0));
    push(&mut f, b, Inst::IBin(IOp::Sub, u8t, v[2], v[1], v[0]));
    push(&mut f, b, Inst::Store(Mem::Int(1, false), p, 0, v[2]));
    push(&mut f, b, Inst::IBin(IOp::Shr, w, v[3], x, v[0]));
    push(&mut f, b, Inst::Conv(Conv::IntToInt(u8t), v[4], x));
    push(&mut f, b, Inst::IBin(IOp::Sub, u8t, v[5], v[4], v[0]));
    push(&mut f, b, Inst::ICmpI(Cond::Lt, false, v[6], v[5], 16));
    push(&mut f, b, Inst::IBin(IOp::Add, w, v[7], v[3], v[6]));
    push(&mut f, b, Inst::Load(Mem::Int(1, false), v[8], p, 0));
    push(&mut f, b, Inst::IBin(IOp::Add, w, v[9], v[7], v[8]));
    f.blocks[b as usize].term = Term::Ret(vec![v[9]]);
    f.verify().unwrap();
    f
}

#[test]
fn narrow_results_read_only_low_bits() {
    let code = Code::new(&compile(&build())).unwrap();
    let run: extern "C" fn(*mut u8, u64, u64) -> u64 = unsafe { std::mem::transmute(code.ptr()) };
    let mut s = 0x9e3779b97f4a7c15u64;
    for _ in 0..4000 {
        s ^= s << 13;
        s ^= s >> 7;
        s ^= s << 17;
        let (x, n, b0) = (s.rotate_left(29), s & 0x3f | (s & 0xff00), (s >> 40) as u8);
        let mut byte = b0;
        let got = run(&mut byte, x, n);
        let stored = b0.wrapping_sub(n as u8);
        let want = (x >> ((n as u8) & 63)) + (((x as u8).wrapping_sub(n as u8) < 16) as u64) + stored as u64;
        assert_eq!(byte, stored);
        assert_eq!(got, want, "x {:#x} n {:#x}", x, n);
    }
}
