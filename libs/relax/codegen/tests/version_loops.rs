//! version_bounds_loops: a counted loop's bounds checks proved by one guard in front of a
//! check-free clone, the original loop the fallback. Each case runs the RIR before and after the
//! pass through a small evaluator over the same inputs, including lengths that make the guard
//! fail and inputs that panic, and requires identical memory, results and panic (index, len,
//! number of stores done before it).
use relax_backend::regalloc::reachable;
use relax_backend::rir::*;
use relax_codegen::version;

const U64: IntTy = IntTy { bits: 64, signed: false };

fn push(f: &mut Func, b: u32, i: Inst) {
    f.blocks[b as usize].insts.push(i);
    f.blocks[b as usize].pos.push(1);
}
fn term(f: &mut Func, b: u32, t: Term) {
    f.blocks[b as usize].term = t;
}

#[derive(Debug, PartialEq)]
enum Out {
    Ret(Vec<u64>, Vec<u8>, usize),
    Panic(u64, u64, Vec<u8>, usize),
}

/// Integer-only evaluator: memory is one byte vector, pointers are offsets into it. A Host call
/// is the bounds panic (index, len). Returns the result, the memory and the number of stores.
fn eval(f: &Func, args: &[u64], mem0: &[u8]) -> Out {
    let mut mem = mem0.to_vec();
    let mut r = vec![0u64; f.vregs.len()];
    for (p, a) in f.params.iter().zip(args) {
        r[p.0 as usize] = *a;
    }
    let mut stores = 0usize;
    let mut b = 0usize;
    let mut steps = 0u64;
    loop {
        steps += 1;
        assert!(steps < 10_000_000, "runaway");
        for i in &f.blocks[b].insts {
            match *i {
                Inst::Iconst(d, k) => r[d.0 as usize] = k as u64,
                Inst::Mov(d, s) => r[d.0 as usize] = r[s.0 as usize],
                Inst::Sel(d, c, a, b2) => r[d.0 as usize] = if r[c.0 as usize] != 0 { r[a.0 as usize] } else { r[b2.0 as usize] },
                Inst::IBin(op, _, d, a, c) => r[d.0 as usize] = bin(op, r[a.0 as usize], r[c.0 as usize]),
                Inst::IBinI(op, _, d, a, k) => r[d.0 as usize] = bin(op, r[a.0 as usize], k as u64),
                Inst::ICmp(cc, s, d, a, c) => r[d.0 as usize] = cmp(cc, s, r[a.0 as usize], r[c.0 as usize]) as u64,
                Inst::ICmpI(cc, s, d, a, k) => r[d.0 as usize] = cmp(cc, s, r[a.0 as usize], k as u64) as u64,
                Inst::Load(Mem::Int(4, false), d, a, off) => {
                    let p = (r[a.0 as usize] as i64 + off as i64) as usize;
                    r[d.0 as usize] = u32::from_le_bytes(mem[p..p + 4].try_into().unwrap()) as u64;
                }
                Inst::Store(Mem::Int(4, _), a, off, s) => {
                    let p = (r[a.0 as usize] as i64 + off as i64) as usize;
                    mem[p..p + 4].copy_from_slice(&(r[s.0 as usize] as u32).to_le_bytes());
                    stores += 1;
                }
                Inst::Call(Callee::Host(_), ref a, _) => {
                    return Out::Panic(r[a[0].0 as usize], r[a[1].0 as usize], mem, stores);
                }
                ref other => panic!("eval: {other:?}"),
            }
        }
        match &f.blocks[b].term {
            Term::Jump(t) => b = *t as usize,
            Term::Branch(c, t, e) => b = if r[c.0 as usize] != 0 { *t as usize } else { *e as usize },
            Term::Ret(vs) => return Out::Ret(vs.iter().map(|v| r[v.0 as usize]).collect(), mem, stores),
            t => panic!("eval: {t:?}"),
        }
    }
}

fn bin(op: IOp, a: u64, b: u64) -> u64 {
    match op {
        IOp::Add => a.wrapping_add(b),
        IOp::Sub => a.wrapping_sub(b),
        IOp::Mul => a.wrapping_mul(b),
        IOp::And => a & b,
        IOp::Or => a | b,
        IOp::Xor => a ^ b,
        IOp::Shl => a << (b & 63),
        IOp::Shr => a >> (b & 63),
        _ => panic!("bin {op:?}"),
    }
}

fn cmp(c: Cond, s: bool, a: u64, b: u64) -> bool {
    if s {
        let (a, b) = (a as i64, b as i64);
        return match c {
            Cond::Lt => a < b,
            Cond::Le => a <= b,
            Cond::Gt => a > b,
            Cond::Ge => a >= b,
            Cond::Eq => a == b,
            Cond::Ne => a != b,
        };
    }
    match c {
        Cond::Lt => a < b,
        Cond::Le => a <= b,
        Cond::Gt => a > b,
        Cond::Ge => a >= b,
        Cond::Eq => a == b,
        Cond::Ne => a != b,
    }
}

/// `for i in start..n { y[i] = y[i] + x[i + k] * 3 }` with both checks (y: i < ylen, x: i + k < xlen),
/// in the shape fold_ranges leaves (`t = i; i = i + 1` after the header's test).
/// params: y, ylen, x, xlen, n, start
fn axpy(k: i64, check_y: bool) -> Func {
    axpy_sym(k, check_y, false)
}

/// as axpy; `sym`: the x index is `(t + m) - w + k` with m, w two more params (a 2D stencil's
/// `y * w + x - w`)
fn axpy_sym(k: i64, check_y: bool, sym: bool) -> Func {
    let mut f = Func::new("axpy".into(), 0);
    let v: Vec<VReg> = (0..8).map(|_| f.vreg(Cls::I)).collect();
    let (y, ylen, x, xlen, n, start) = (v[0], v[1], v[2], v[3], v[4], v[5]);
    f.params.extend([y, ylen, x, xlen, n, start, v[6], v[7]]);
    for _ in 0..8 {
        f.block();
    }
    let (i, c, t, i2, cy, xi, cx, off, offx, yv, xv, m, s, ya, xa) =
        (f.vreg(Cls::I), f.vreg(Cls::I), f.vreg(Cls::I), f.vreg(Cls::I), f.vreg(Cls::I), f.vreg(Cls::I), f.vreg(Cls::I), f.vreg(Cls::I), f.vreg(Cls::I), f.vreg(Cls::I), f.vreg(Cls::I), f.vreg(Cls::I), f.vreg(Cls::I), f.vreg(Cls::I), f.vreg(Cls::I));
    push(&mut f, 0, Inst::Mov(i, start));
    term(&mut f, 0, Term::Jump(1));
    // b1: header test
    push(&mut f, 1, Inst::ICmp(Cond::Lt, false, c, i, n));
    term(&mut f, 1, Term::Branch(c, 2, 5));
    // b2: t = i; i = i + 1; y check
    push(&mut f, 2, Inst::Mov(t, i));
    push(&mut f, 2, Inst::IBinI(IOp::Add, U64, i2, i, 1));
    push(&mut f, 2, Inst::Mov(i, i2));
    if check_y {
        push(&mut f, 2, Inst::ICmp(Cond::Lt, false, cy, t, ylen));
        term(&mut f, 2, Term::Branch(cy, 3, 6));
    } else {
        term(&mut f, 2, Term::Jump(3));
    }
    // b3: x check of t + k
    let tk = if sym {
        let (a1, a2) = (f.vreg(Cls::I), f.vreg(Cls::I));
        push(&mut f, 3, Inst::IBin(IOp::Add, U64, a1, v[6], t));
        push(&mut f, 3, Inst::IBin(IOp::Sub, U64, a2, a1, v[7]));
        a2
    } else {
        t
    };
    if k >= 0 {
        push(&mut f, 3, Inst::IBinI(IOp::Add, U64, xi, tk, k));
    } else {
        push(&mut f, 3, Inst::IBinI(IOp::Sub, U64, xi, tk, -k));
    }
    push(&mut f, 3, Inst::ICmp(Cond::Lt, false, cx, xi, xlen));
    term(&mut f, 3, Term::Branch(cx, 4, 7));
    // b4: body
    push(&mut f, 4, Inst::IBinI(IOp::Shl, U64, off, t, 2));
    push(&mut f, 4, Inst::IBinI(IOp::Shl, U64, offx, xi, 2));
    push(&mut f, 4, Inst::IBin(IOp::Add, U64, ya, y, off));
    push(&mut f, 4, Inst::IBin(IOp::Add, U64, xa, x, offx));
    push(&mut f, 4, Inst::Load(Mem::Int(4, false), yv, ya, 0));
    push(&mut f, 4, Inst::Load(Mem::Int(4, false), xv, xa, 0));
    push(&mut f, 4, Inst::IBinI(IOp::Mul, U64, m, xv, 3));
    push(&mut f, 4, Inst::IBin(IOp::Add, U64, s, yv, m));
    push(&mut f, 4, Inst::Store(Mem::Int(4, false), ya, 0, s));
    term(&mut f, 4, Term::Jump(1));
    // b5: exit, returns the counter (a value read after the loop)
    f.rets.push(Cls::I);
    term(&mut f, 5, Term::Ret(vec![i]));
    for (b, (a0, a1)) in [(6u32, (t, ylen)), (7u32, (xi, xlen))] {
        let sym = f.vreg(Cls::I);
        push(&mut f, b, Inst::Iconst(sym, 0));
        push(&mut f, b, Inst::Call(Callee::Host(Sym { id: 5, off: 0 }), vec![a0, a1, sym], Vec::new()));
        term(&mut f, b, Term::Unreachable);
    }
    f
}

fn run_cases(orig: &Func, new: &Func) -> usize {
    run_cases_mw(orig, new, &[(0, 0)])
}

fn run_cases_mw(orig: &Func, new: &Func, mws: &[(u64, u64)]) -> usize {
    // memory: y at 0 (64 u32), x at 256 (64 u32)
    let mut mem = vec![0u8; 512];
    for j in 0..128u32 {
        mem[j as usize * 4..j as usize * 4 + 4].copy_from_slice(&(j * 7 + 1).to_le_bytes());
    }
    let mut cases = 0;
    let mut panics = 0;
    for ylen in [0u64, 1, 5, 20, 40, 64] {
        for xlen in [0u64, 3, 19, 20, 21, 40, 64] {
            for n in [0u64, 1, 4, 19, 20, 21, 40, 64] {
                for start in [0u64, 1, 2, 3, 30] {
                    for &(m, w) in mws {
                        let args = [0, ylen, 256, xlen, n, start, m, w];
                        let a = eval(orig, &args, &mem);
                        let b = eval(new, &args, &mem);
                        assert_eq!(a, b, "ylen {ylen} xlen {xlen} n {n} start {start} m {m} w {w}");
                        if matches!(a, Out::Panic(..)) {
                            panics += 1;
                        }
                        cases += 1;
                    }
                }
            }
        }
    }
    assert!(panics > 0 && panics < cases, "the cases cover both panicking and clean runs");
    cases
}

fn clone_has_no_checks(f: &Func) -> bool {
    // some reachable loop runs without any branch to an Unreachable block
    let reach = reachable(f);
    let cold = |b: u32| matches!(f.blocks[b as usize].term, Term::Unreachable);
    let reach_loop_blocks: Vec<usize> = (0..f.blocks.len()).filter(|&b| reach[b]).collect();
    reach_loop_blocks.iter().any(|&b| matches!(f.blocks[b].term, Term::Jump(t) if !cold(t)))
        && f.blocks.len() > 8
}

fn versioned(mut f: Func) -> (Func, Func) {
    let orig = f.clone();
    let changed = version::version_bounds_loops(&relax_session::Options::default(), &mut f);
    assert!(changed, "versioned");
    (orig, f)
}

#[test]
fn axpy_two_checks_offset_zero() {
    let (orig, new) = versioned(axpy(0, true));
    assert!(clone_has_no_checks(&new));
    // the clone's two checks are gone: count Branch terms to cold blocks in appended blocks
    let cold = |b: u32| matches!(new.blocks[b as usize].term, Term::Unreachable);
    let clone_checks = new.blocks[8..].iter().filter(|b| matches!(b.term, Term::Branch(_, t, e) if cold(t) || cold(e))).count();
    assert_eq!(clone_checks, 0);
    run_cases(&orig, &new);
}

#[test]
fn stencil_positive_offset() {
    let (orig, new) = versioned(axpy(2, true));
    run_cases(&orig, &new);
}

#[test]
fn negative_offset_needs_start() {
    let (orig, new) = versioned(axpy(-1, false));
    run_cases(&orig, &new);
}

/// The clone renames the counter copy t although the original's panic block reads it (the clone
/// cannot reach that block): later single-def passes and the vectoriser see a loop-local t.
#[test]
fn clone_renames_values_only_cold_blocks_read() {
    let (_, new) = versioned(axpy(0, true));
    let t = match new.blocks[2].insts[0] {
        Inst::Mov(d, _) => d,
        _ => unreachable!(),
    };
    let clone_defines_t = new.blocks[8..].iter().any(|b| b.insts.iter().any(|i| matches!(i, Inst::Mov(d, _) if *d == t)));
    assert!(!clone_defines_t);
}

/// The index copy also defined after the loop (a storage-dead zero, as lowering emits): the check
/// is still proved, and the clone still renames it.
#[test]
fn outside_def_of_index_copy() {
    let mut f = axpy(0, true);
    let t = match f.blocks[2].insts[0] {
        Inst::Mov(d, _) => d,
        _ => unreachable!(),
    };
    f.blocks[5].insts.insert(0, Inst::Iconst(t, 0));
    f.blocks[5].pos.insert(0, 1);
    let (orig, new) = versioned(f);
    let cold = |b: u32| matches!(new.blocks[b as usize].term, Term::Unreachable);
    let clone_checks = new.blocks[8..].iter().filter(|b| matches!(b.term, Term::Branch(_, t, e) if cold(t) || cold(e))).count();
    assert_eq!(clone_checks, 0);
    run_cases(&orig, &new);
}

/// Offsets with loop-invariant vregs (2D stencil rows): positive, negative and wrapping offsets.
#[test]
fn symbolic_offsets() {
    for k in [0i64, 1, -1, 3] {
        let (orig, new) = versioned(axpy_sym(k, true, true));
        let mws: Vec<(u64, u64)> = vec![(0, 0), (5, 0), (0, 5), (5, 5), (8, 3), (3, 8), (0, 1), (1, 0), (40, 2), (u64::MAX, 0), (0, u64::MAX), (u64::MAX - 3, 0)];
        run_cases_mw(&orig, &new, &mws);
    }
}

#[test]
fn not_counted_left_alone() {
    // the bound redefined in the loop: no counted loop, nothing versioned
    let mut f = axpy(0, true);
    let n = f.params[4];
    push(&mut f, 4, Inst::IBinI(IOp::Add, U64, n, n, 0));
    let before = f.blocks.len();
    assert!(!version::version_bounds_loops(&relax_session::Options::default(), &mut f));
    assert_eq!(f.blocks.len(), before);
}

#[test]
fn stale_read_after_increment_not_proved() {
    // the x index reads i after the increment (i + 0 is the next value): it may equal n, so the
    // check stays in the clone; the y check (fresh t) is still versioned
    let mut f = axpy(0, true);
    let i = match f.blocks[0].insts[0] {
        Inst::Mov(d, _) => d,
        _ => unreachable!(),
    };
    let xi = match f.blocks[3].insts[0] {
        Inst::IBinI(_, _, d, _, _) => d,
        _ => unreachable!(),
    };
    f.blocks[3].insts[0] = Inst::IBinI(IOp::Add, U64, xi, i, 0);
    let (orig, new) = versioned(f);
    let cold = |b: u32| matches!(new.blocks[b as usize].term, Term::Unreachable);
    let clone_checks = new.blocks[8..].iter().filter(|b| matches!(b.term, Term::Branch(_, t, e) if cold(t) || cold(e))).count();
    assert_eq!(clone_checks, 1);
    // memory comparison: the x read at i reaches index n, inside the 128-word buffer
    run_cases(&orig, &new);
}

/// The clone of `y[i] += k * x[i]` after rotation (one block): the stream-map vectoriser must take it.
#[test]
fn clone_shape_vectorises() {
    let mut f = Func::new("axpy_clone".into(), 0);
    let p: Vec<VReg> = (0..4).map(|_| f.vreg(Cls::I)).collect();
    let k = f.vreg(Cls::F32);
    let (y, ylen, x, _xlen) = (p[0], p[1], p[2], p[3]);
    f.params.extend([p[0], p[1], p[2], p[3], k]);
    for _ in 0..4 {
        f.block();
    }
    let i = f.vreg(Cls::I);
    let (c0, t, i2, off, xa, xv, m, ya, yv, s, c1) = (f.vreg(Cls::I), f.vreg(Cls::I), f.vreg(Cls::I), f.vreg(Cls::I), f.vreg(Cls::I), f.vreg(Cls::F32), f.vreg(Cls::F32), f.vreg(Cls::I), f.vreg(Cls::F32), f.vreg(Cls::F32), f.vreg(Cls::I));
    push(&mut f, 0, Inst::Iconst(i, 0));
    push(&mut f, 0, Inst::ICmp(Cond::Lt, false, c0, i, ylen));
    term(&mut f, 0, Term::Branch(c0, 1, 2));
    push(&mut f, 1, Inst::Mov(t, i));
    push(&mut f, 1, Inst::IBinI(IOp::Add, U64, i2, i, 1));
    push(&mut f, 1, Inst::Mov(i, i2));
    push(&mut f, 1, Inst::IBinI(IOp::Shl, U64, off, t, 2));
    push(&mut f, 1, Inst::IBin(IOp::Add, U64, xa, x, off));
    push(&mut f, 1, Inst::Load(Mem::F32, xv, xa, 0));
    push(&mut f, 1, Inst::FBin(FOp::Mul, false, m, k, xv));
    push(&mut f, 1, Inst::IBin(IOp::Add, U64, ya, y, off));
    push(&mut f, 1, Inst::Load(Mem::F32, yv, ya, 0));
    push(&mut f, 1, Inst::FBin(FOp::Add, false, s, yv, m));
    push(&mut f, 1, Inst::Store(Mem::F32, ya, 0, s));
    push(&mut f, 1, Inst::ICmp(Cond::Lt, false, c1, i, ylen));
    term(&mut f, 1, Term::Branch(c1, 1, 2));
    term(&mut f, 2, Term::Ret(vec![]));
    let mut g = f.clone();
    let n0 = f.blocks.len();
    let ch = relax_codegen::loops::vectorize_reductions(&relax_session::Options::default(), &mut f);
    assert!(ch && f.blocks.len() > n0, "vectorised");
    // t read in an unreachable block outside the loop (an original loop's panic block)
    let b = g.block();
    push(&mut g, b, Inst::Call(Callee::Host(Sym { id: 5, off: 0 }), vec![t, ylen], Vec::new()));
    term(&mut g, b, Term::Unreachable);
    let n0 = g.blocks.len();
    let ch = relax_codegen::loops::vectorize_reductions(&relax_session::Options::default(), &mut g);
    eprintln!("with outside read of t: vectorised {}", ch && g.blocks.len() > n0);
}

/// `for i in 0..n { y[i] += if flag { 1 } else { x[i] } }` with flag a param: two loops, chosen once.
#[test]
fn unswitch_invariant_branch() {
    let mut f = Func::new("unsw".into(), 0);
    let p: Vec<VReg> = (0..5).map(|_| f.vreg(Cls::I)).collect();
    let (y, x, n, flag, _) = (p[0], p[1], p[2], p[3], p[4]);
    f.params.extend([p[0], p[1], p[2], p[3]]);
    for _ in 0..6 {
        f.block();
    }
    let (i, c, off, ya, yv, xa, xv, s, one, z) = (f.vreg(Cls::I), f.vreg(Cls::I), f.vreg(Cls::I), f.vreg(Cls::I), f.vreg(Cls::I), f.vreg(Cls::I), f.vreg(Cls::I), f.vreg(Cls::I), f.vreg(Cls::I), f.vreg(Cls::I));
    push(&mut f, 0, Inst::Iconst(i, 0));
    term(&mut f, 0, Term::Jump(1));
    push(&mut f, 1, Inst::ICmp(Cond::Lt, false, c, i, n));
    term(&mut f, 1, Term::Branch(c, 2, 5));
    push(&mut f, 2, Inst::IBinI(IOp::Shl, U64, off, i, 2));
    push(&mut f, 2, Inst::IBin(IOp::Add, U64, ya, y, off));
    push(&mut f, 2, Inst::Load(Mem::Int(4, false), yv, ya, 0));
    term(&mut f, 2, Term::Branch(flag, 3, 4));
    push(&mut f, 3, Inst::Iconst(one, 1));
    push(&mut f, 3, Inst::IBin(IOp::Add, U64, s, yv, one));
    push(&mut f, 3, Inst::Store(Mem::Int(4, false), ya, 0, s));
    push(&mut f, 3, Inst::IBinI(IOp::Add, U64, i, i, 1));
    term(&mut f, 3, Term::Jump(1));
    push(&mut f, 4, Inst::IBin(IOp::Add, U64, xa, x, off));
    push(&mut f, 4, Inst::Load(Mem::Int(4, false), xv, xa, 0));
    push(&mut f, 4, Inst::IBin(IOp::Add, U64, z, yv, xv));
    push(&mut f, 4, Inst::Store(Mem::Int(4, false), ya, 0, z));
    push(&mut f, 4, Inst::IBinI(IOp::Add, U64, i, i, 1));
    term(&mut f, 4, Term::Jump(1));
    f.rets.push(Cls::I);
    term(&mut f, 5, Term::Ret(vec![i]));
    let orig = f.clone();
    assert!(version::unswitch_loops(&relax_session::Options::default(), &mut f));
    // neither copy branches on flag any more
    let reach = reachable(&f);
    assert!(!f.blocks.iter().enumerate().any(|(b, bl)| reach[b] && matches!(bl.term, Term::Branch(c, _, _) if c == flag)));
    let mut mem = vec![0u8; 512];
    for j in 0..128u32 {
        mem[j as usize * 4..j as usize * 4 + 4].copy_from_slice(&(j * 3 + 2).to_le_bytes());
    }
    for n in [0u64, 1, 7, 64] {
        for fl in [0u64, 1, 2] {
            let args = [0, 256, n, fl];
            assert_eq!(eval(&orig, &args, &mem), eval(&f, &args, &mem), "n {n} flag {fl}");
        }
    }
}
