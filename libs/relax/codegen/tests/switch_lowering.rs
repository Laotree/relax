//! Switch lowering (`switch::lower_switches`, run by the back ends): random chains of compares of
//! one value against constants -- the shape a `match` on an integer, `char` or discriminant
//! lowers to: equality, inclusive ranges, or-patterns, signed and unsigned relations -- give the
//! same results compiled as the first-match-wins reference, whichever of jump table, bit tests or
//! binary search the lowering picks, with and without the thorough register allocation.
#![cfg(any(all(target_arch = "x86_64", unix), all(target_arch = "aarch64", unix)))]
use relax_codegen::{exec::Code, rir::*, switch};

#[cfg(target_arch = "x86_64")]
fn compile(options: &relax_session::Options, f: &Func, regs: bool) -> Vec<u8> {
    let env = relax_codegen::x64::Env { slots: SlotsPtr::NONE, tls_key: 0, tls_slow: 0, resume: 0, opt_regs: regs, syms: 0, sym_class: 0 };
    let c = relax_codegen::x64::compile(options, f, &env).unwrap();
    c.code[..c.text_len as usize].to_vec()
}

#[cfg(target_arch = "aarch64")]
fn compile(options: &relax_session::Options, f: &Func, regs: bool) -> Vec<u8> {
    let env = relax_codegen::arm64::Env { slots: SlotsPtr::NONE, tls_key: 0, tls_slow: 0, resume: 0, opt_regs: regs, syms: 0, sym_class: 0 };
    let c = relax_codegen::arm64::compile(options, f, &env).unwrap();
    c.code[..c.text_len as usize].to_vec()
}

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

#[derive(Clone, Copy)]
struct T {
    cond: Cond,
    signed: bool,
    k: i64,
}

fn holds(t: T, x: u64) -> bool {
    let (a, b) = (x as i64, t.k);
    let (ua, ub) = (x, t.k as u64);
    match (t.cond, t.signed) {
        (Cond::Eq, _) => a == b,
        (Cond::Ne, _) => a != b,
        (Cond::Lt, true) => a < b,
        (Cond::Le, true) => a <= b,
        (Cond::Gt, true) => a > b,
        (Cond::Ge, true) => a >= b,
        (Cond::Lt, false) => ua < ub,
        (Cond::Le, false) => ua <= ub,
        (Cond::Gt, false) => ua > ub,
        (Cond::Ge, false) => ua >= ub,
    }
}

/// arms[i] = alternatives (or-pattern); each alternative a conjunction of tests. Result of arm i is
/// 100 + i; no arm: 7.
fn reference(arms: &[Vec<Vec<T>>], x: u64) -> u64 {
    for (i, alts) in arms.iter().enumerate() {
        if alts.iter().any(|a| a.iter().all(|t| holds(*t, x))) {
            return 100 + i as u64;
        }
    }
    7
}

fn build(arms: &[Vec<Vec<T>>]) -> Func {
    let mut f = Func::new("sw".into(), 0);
    let x = f.vreg(Cls::I);
    f.params = vec![x];
    f.rets = vec![Cls::I];
    let entry = f.block();
    let ret_block = |f: &mut Func, v: i64| -> u32 {
        let b = f.block();
        let r = f.vreg(Cls::I);
        f.blocks[b as usize].insts.push(Inst::Iconst(r, v));
        f.blocks[b as usize].pos.push(0);
        f.blocks[b as usize].term = Term::Ret(vec![r]);
        b
    };
    let default = ret_block(&mut f, 7);
    let targets: Vec<u32> = (0..arms.len()).map(|i| ret_block(&mut f, 100 + i as i64)).collect();
    // tests in arm order; the first one is the entry block
    let mut flat: Vec<(T, usize, usize)> = Vec::new(); // (test, arm, alt)
    let mut firsts: Vec<Vec<usize>> = Vec::new();
    for (i, alts) in arms.iter().enumerate() {
        let mut fa = Vec::new();
        for (j, a) in alts.iter().enumerate() {
            fa.push(flat.len());
            for t in a {
                flat.push((*t, i, j));
            }
        }
        firsts.push(fa);
    }
    let blocks: Vec<u32> = (0..flat.len()).map(|i| if i == 0 { entry } else { f.block() }).collect();
    if flat.is_empty() {
        f.blocks[entry as usize].term = Term::Jump(default);
        return f;
    }
    // where a failing test of (arm, alt) goes: the arm's next alternative, else the next arm's first test
    let next_arm = |i: usize| -> u32 {
        let mut k = i + 1;
        while k < arms.len() {
            if let Some(&s) = firsts[k].first() {
                return blocks[s];
            }
            k += 1;
        }
        default
    };
    for (n, &(t, i, j)) in flat.iter().enumerate() {
        let last_of_alt = n + 1 == flat.len() || flat[n + 1].1 != i || flat[n + 1].2 != j;
        let on_true = if last_of_alt { targets[i] } else { blocks[n + 1] };
        let on_false = if j + 1 < arms[i].len() { blocks[firsts[i][j + 1]] } else { next_arm(i) };
        let d = f.vreg(Cls::I);
        let b = blocks[n] as usize;
        f.blocks[b].insts.push(Inst::ICmpI(t.cond, t.signed, d, x, t.k));
        f.blocks[b].pos.push(0);
        f.blocks[b].term = Term::Branch(d, on_true, on_false);
    }
    f.verify().unwrap();
    f
}

fn rand_arms(r: &mut Rng, span: u64, signed: bool) -> Vec<Vec<Vec<T>>> {
    let n = 2 + r.below(14) as usize;
    let base = if r.below(3) == 0 { -(span as i64) / 2 } else { r.below(300) as i64 };
    let mut arms = Vec::new();
    for _ in 0..n {
        let nalt = 1 + r.below(3) as usize;
        let mut alts = Vec::new();
        for _ in 0..nalt {
            let k = base + r.below(span) as i64;
            let alt = match r.below(8) {
                0..=3 => vec![T { cond: Cond::Eq, signed, k }],
                4..=5 => {
                    let w = r.below(span / 3 + 1) as i64;
                    vec![T { cond: Cond::Ge, signed, k }, T { cond: Cond::Le, signed, k: k + w }]
                }
                6 => vec![T { cond: if r.below(2) == 0 { Cond::Lt } else { Cond::Gt }, signed, k }],
                _ => vec![T { cond: Cond::Ne, signed, k }, T { cond: Cond::Lt, signed, k: k + 3 }],
            };
            alts.push(alt);
        }
        arms.push(alts);
    }
    arms
}

#[test]
fn switch_lowering_matches_the_compare_chain() {
    let options = relax_session::Options::default();
    let mut r = Rng(0x9e37_79b9_7f4a_7c15);
    let mut switched = 0;
    let mut tables = 0;
    let total = 3000;
    for case in 0..total {
        let span = [12, 40, 70, 300, 3000][case % 5];
        let signed = case % 3 != 0;
        let arms = rand_arms(&mut r, span, signed);
        let f = build(&arms);
        if let Some(g) = switch::lower_switches(&options, &f) {
            g.verify().unwrap();
            switched += 1;
            if g.blocks.iter().any(|b| matches!(b.term, Term::Switch(..))) {
                tables += 1;
            }
        }
        let mut xs: Vec<u64> = vec![0, 1, u64::MAX, u64::MAX - 1, i64::MAX as u64, i64::MIN as u64, (i64::MIN as u64) + 1, 1 << 32, (1 << 32) - 1];
        for v in -400i64..4200 {
            xs.push(v as u64);
        }
        for regs in [false, true] {
            let code = Code::new(&compile(&options, &f, regs)).unwrap();
            let run: extern "C" fn(u64) -> u64 = unsafe { std::mem::transmute(code.ptr()) };
            for &x in &xs {
                assert_eq!(run(x), reference(&arms, x), "case {case} regs {regs} x {}", x as i64);
            }
        }
    }
    // the generator must exercise the lowering, jump tables included
    assert!(switched > total / 4, "only {switched} of {total} chains were lowered");
    assert!(tables > 10, "only {tables} jump tables");
}
