//! Loop versioning (O3): one mechanism, several clients. A loop gets a clone that runs under
//! assumptions a guard in front of the loop has checked; when the guard fails the original loop
//! runs, unchanged. Clients: bounds checks a counted loop's range implies (`version_bounds_loops`,
//! C2 loop predication / .NET loop cloning); later loop-invariant branches (unswitching) and
//! hoisted dyn-call guards.
//!
//! RIR is not SSA, so the clone keeps the names of every vreg that is read outside the loop: the
//! values leaving the loop come out of whichever copy ran, under the same names, and nothing is
//! merged at the exits. Single-def vregs that only the loop reads get fresh names in the clone, so
//! single-def patterns (unroll_loops' increment, address modes) still match both copies.
//!
//! The original loop is the fallback: a check the clone drops is one the guard proved, and when
//! the guard does not hold, the original runs every check at the iteration it always did, with the
//! same panic message and payload. Nothing is speculated about panics.
use relax_backend::regalloc::{for_defs, for_uses, reachable, term_uses};
use relax_backend::rir::*;

const U64_TY: IntTy = IntTy { bits: 64, signed: false };

/// Largest loop versioned (instructions over its blocks, blocks): bounds the code size it adds.
const MAX_INSTS: usize = 96;
const MAX_BLOCKS: usize = 10;
/// Versioned loops per function.
const MAX_LOOPS: usize = 4;

fn version_on(options: &relax_session::Options) -> bool {
    !relax_backend::stats::opt_off(options, "-version")
}

fn trace() -> bool {
    static E: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *E.get_or_init(|| std::env::var("MAKEPAD_RUN_VERSION_TRACE").is_ok())
}

/// A natural loop: its header, member flags and member list.
pub struct Loop {
    pub header: u32,
    pub member: Vec<bool>,
    pub blocks: Vec<u32>,
}

/// What a clone may assume: the branch ending `block` always goes to `to`.
#[derive(Clone, Copy, Debug)]
pub struct Taken {
    pub block: u32,
    pub to: u32,
}

/// Clones loop `l`: a new guard block takes every entry into the loop's header and runs `guard`
/// (instructions defining `g`), then `Branch(g, clone header, original header)`. In the clone,
/// every `Taken` branch becomes a jump. Returns the map original block -> clone block.
pub fn version_loop(f: &mut Func, l: &Loop, guard: Vec<Inst>, g: VReg, facts: &[Taken]) -> Vec<(u32, u32)> {
    let nv = f.vregs.len();
    let mut ndef = vec![0u32; nv];
    let mut used_outside = vec![false; nv];
    let mut defined_inside = vec![false; nv];
    for (bi, b) in f.blocks.iter().enumerate() {
        let inside = l.member.get(bi).copied().unwrap_or(false);
        for i in &b.insts {
            for_defs(i, |d| {
                ndef[d.0 as usize] += 1;
                if inside {
                    defined_inside[d.0 as usize] = true;
                }
            });
            if !inside {
                for_uses(i, |u| used_outside[u.0 as usize] = true);
            }
        }
        if !inside {
            let mut tu = Vec::new();
            term_uses(&b.term, &mut tu);
            for u in tu {
                used_outside[u.0 as usize] = true;
            }
        }
    }
    for p in &f.params {
        ndef[p.0 as usize] += 1;
    }
    // fresh names: single-def vregs the loop defines and only the loop reads
    let mut rename: std::collections::HashMap<u32, VReg> = std::collections::HashMap::new();
    for v in 0..nv {
        if defined_inside[v] && ndef[v] == 1 && !used_outside[v] && !f.params.contains(&VReg(v as u32)) {
            let nvr = f.vreg(f.vregs[v]);
            rename.insert(v as u32, nvr);
        }
    }
    let base = f.blocks.len() as u32;
    let map: Vec<(u32, u32)> = l.blocks.iter().enumerate().map(|(k, &b)| (b, base + k as u32)).collect();
    let to_clone = |b: u32| -> u32 { map.iter().find(|(o, _)| *o == b).map(|(_, c)| *c).unwrap_or(b) };
    for &(orig, _) in &map {
        let mut nb = f.blocks[orig as usize].clone();
        for i in nb.insts.iter_mut() {
            i.vregs_mut(|r| {
                if let Some(n) = rename.get(&r.0) {
                    *r = *n;
                }
            });
        }
        if let Some(t) = facts.iter().find(|t| t.block == orig) {
            nb.term = Term::Jump(t.to);
        }
        match &mut nb.term {
            Term::Branch(c, _, _) | Term::Switch(c, _) => {
                if let Some(n) = rename.get(&c.0) {
                    *c = *n;
                }
            }
            Term::Ret(vs) => {
                for v in vs.iter_mut() {
                    if let Some(n) = rename.get(&v.0) {
                        *v = *n;
                    }
                }
            }
            _ => {}
        }
        nb.term.map_succs(|s| to_clone(s));
        f.blocks.push(nb);
    }
    // the guard block takes the outside entries into the header
    let gb = f.blocks.len() as u32;
    let hc = to_clone(l.header);
    let pos = f.blocks[l.header as usize].term_pos;
    let n = guard.len();
    f.blocks.push(Block { insts: guard, pos: vec![pos; n], term: Term::Branch(g, hc, l.header), term_pos: pos });
    for bi in 0..base as usize {
        if !l.member.get(bi).copied().unwrap_or(false) {
            f.blocks[bi].term.map_succs(|s| if s == l.header { gb } else { s });
        }
    }
    map
}

/// Natural loops of `f` (innermost first) that version_loop can clone: header not the entry
/// block, not entered through an unwind edge, no member that is another loop's header (innermost).
fn candidate_loops(f: &Func) -> Vec<Loop> {
    let reach = reachable(f);
    let preds = relax_backend::regalloc::preds_of(f, &reach);
    let loops = relax_backend::regalloc::natural_loops(f, &reach, &preds, false);
    let headers: Vec<u32> = loops.iter().map(|(h, _)| *h).collect();
    let mut out = Vec::new();
    for (h, m) in loops {
        if h == 0 {
            continue;
        }
        let blocks: Vec<u32> = (0..f.blocks.len() as u32).filter(|&b| m[b as usize]).collect();
        if headers.iter().any(|&h2| h2 != h && m[h2 as usize]) {
            continue;
        }
        out.push(Loop { header: h, member: m, blocks });
    }
    out
}

/// The counted-loop facts of `l`: (iv, bound n, step s, increment (block, index)) when the header
/// ends in `c = i < n; Branch(c, in, out)` (or `i >= n` exiting on true), n is defined outside the
/// loop and i's only definition inside is the increment `i = i + s` / `t = i + s; i = t` (s >= 1).
struct Counted {
    iv: VReg,
    n: VReg,
    step: i64,
    inc: (u32, usize),
}

fn defs_in(f: &Func, l: &Loop, v: VReg) -> Vec<(u32, usize)> {
    let mut out = Vec::new();
    for &b in &l.blocks {
        for (k, i) in f.blocks[b as usize].insts.iter().enumerate() {
            for_defs(i, |d| {
                if d == v {
                    out.push((b, k));
                }
            });
        }
    }
    out
}

fn counted(f: &Func, l: &Loop) -> Option<Counted> {
    let hb = &f.blocks[l.header as usize];
    let (c, t, e) = match hb.term {
        Term::Branch(c, t, e) => (c, t, e),
        _ => return None,
    };
    let last = hb.insts.last()?;
    let (cond, signed, iv, n) = match *last {
        Inst::ICmp(cc, s, d, a, b) if d == c => (cc, s, a, b),
        _ => return None,
    };
    if signed {
        return None;
    }
    // stay in the loop while i < n
    let ok = match cond {
        Cond::Lt => l.member[t as usize] && !l.member[e as usize],
        Cond::Ge => l.member[e as usize] && !l.member[t as usize],
        _ => false,
    };
    if !ok || iv == n || !defs_in(f, l, n).is_empty() {
        return None;
    }
    let d = defs_in(f, l, iv);
    if d.len() != 1 {
        return None;
    }
    let (b, k) = d[0];
    let insts = &f.blocks[b as usize].insts;
    let step = match insts[k] {
        Inst::IBinI(IOp::Add, it, dd, a, s) if dd == iv && a == iv && s >= 1 && it.bits == 64 => s,
        Inst::Mov(dd, tmp) if dd == iv => {
            // t = i + s just before, t defined once in the loop
            let td = defs_in(f, l, tmp);
            if td.len() != 1 || td[0].0 != b || td[0].1 >= k {
                return None;
            }
            match insts[td[0].1] {
                Inst::IBinI(IOp::Add, it, _, a, s) if a == iv && s >= 1 && it.bits == 64 => {
                    // i not redefined between t's def and the Mov (it is not: one def)
                    s
                }
                _ => return None,
            }
        }
        _ => return None,
    };
    // the compare is the header's last instruction and the increment is not in the header
    // before it ... an increment in the header would make the tested value the new one, which is
    // fine for the upper bound, but keep the canonical shape only
    if b == l.header {
        return None;
    }
    Some(Counted { iv, n, step, inc: (b, k) })
}

/// Blocks of the loop reachable from just after the increment without passing the header (the
/// rest of the iteration that runs after i changed): reads of i there are not "fresh".
fn after_increment(f: &Func, l: &Loop, inc: (u32, usize)) -> Option<Vec<bool>> {
    let nb = f.blocks.len();
    let mut seen = vec![false; nb];
    let mut work: Vec<u32> = f.blocks[inc.0 as usize].term.succs().filter(|&s| l.member[s as usize] && s != l.header).collect();
    while let Some(b) = work.pop() {
        if seen[b as usize] {
            continue;
        }
        seen[b as usize] = true;
        for s in f.blocks[b as usize].term.succs() {
            if l.member[s as usize] && s != l.header {
                work.push(s);
            }
        }
    }
    // the increment's block reached again without the header: an inner cycle, give up
    if seen[inc.0 as usize] {
        return None;
    }
    Some(seen)
}

/// `x` as `t + k` where every value t takes was just tested `< n`: t = i read at a fresh point
/// (after the header's test, before the increment in the iteration), t single-def in f.
/// Returns k (0 for t itself).
fn fresh_offset(f: &Func, l: &Loop, cnt: &Counted, stale: &[bool], ndef: &[u32], x: VReg, depth: u32) -> Option<i64> {
    if depth > 4 || ndef[x.0 as usize] != 1 {
        return None;
    }
    let d = defs_in(f, l, x);
    if d.len() != 1 {
        return None;
    }
    let (b, k) = d[0];
    let src_off = |src: VReg| -> Option<i64> {
        if src == cnt.iv {
            fresh_at(l, cnt, stale, b, k).then_some(0)
        } else {
            fresh_offset(f, l, cnt, stale, ndef, src, depth + 1)
        }
    };
    match f.blocks[b as usize].insts[k] {
        Inst::Mov(_, src) => src_off(src),
        Inst::IBinI(IOp::Add, it, _, src, c) if it.bits == 64 && c.abs() <= 1 << 20 => Some(src_off(src)? + c),
        Inst::IBinI(IOp::Sub, it, _, src, c) if it.bits == 64 && c.abs() <= 1 << 20 => Some(src_off(src)? - c),
        _ => None,
    }
}

/// A read of the counter at instruction k of block b sees a value the header just tested: not in
/// the header (before its test), not after the increment within the iteration.
fn fresh_at(l: &Loop, cnt: &Counted, stale: &[bool], b: u32, k: usize) -> bool {
    !(b == l.header || stale[b as usize] || (b == cnt.inc.0 && k > cnt.inc.1))
}

/// Bounds-check versioning: in each innermost counted loop, the bounds checks
/// `Branch(x < len, ok, cold)` (cold ends in `Unreachable`; `len` loop-invariant; x = i + k with i
/// the counter read fresh) are proved for the whole loop by one guard in front of it,
/// `len >= k && n <= len - k` per check (k < 0: `n <= len && i >= -k` with step 1), and the clone
/// runs without them. Returns whether anything changed.
pub fn version_bounds_loops(options: &relax_session::Options, f: &mut Func) -> bool {
    if !version_on(options) || f.blocks.len() < 3 {
        return false;
    }
    let mut changed = 0;
    // one loop at a time: block numbers stay valid for the loops found before (clones append)
    let loops = candidate_loops(f);
    for l in loops {
        if changed >= MAX_LOOPS {
            break;
        }
        if l.blocks.len() > MAX_BLOCKS {
            continue;
        }
        let size: usize = l.blocks.iter().map(|&b| f.blocks[b as usize].insts.len()).sum();
        if size > MAX_INSTS {
            continue;
        }
        // calls in the loop: not a kernel; Invoke edges, switches: leave
        if l.blocks.iter().any(|&b| {
            let bl = &f.blocks[b as usize];
            bl.insts.iter().any(|i| matches!(i, Inst::Call(..))) || matches!(bl.term, Term::Invoke(..) | Term::Switch(..) | Term::Resume)
        }) {
            continue;
        }
        let Some(cnt) = counted(f, &l) else { continue };
        let Some(stale) = after_increment(f, &l, cnt.inc) else { continue };
        let nv = f.vregs.len();
        let mut ndef = vec![0u32; nv];
        for b in &f.blocks {
            for i in &b.insts {
                for_defs(i, |d| ndef[d.0 as usize] += 1);
            }
        }
        for p in &f.params {
            ndef[p.0 as usize] += 1;
        }
        // the checks
        let mut facts: Vec<Taken> = Vec::new();
        let mut conds: Vec<(VReg, i64)> = Vec::new(); // (len, k)
        for &b in &l.blocks {
            let bl = &f.blocks[b as usize];
            let Term::Branch(c, t, e) = bl.term else { continue };
            if b == l.header {
                continue;
            }
            let cold = |x: u32| matches!(f.blocks[x as usize].term, Term::Unreachable) && !l.member[x as usize];
            // c defined by the block's last compare
            let Some(Inst::ICmp(cc, false, d, x, len)) = bl.insts.iter().rev().find(|i| {
                let mut dd = false;
                for_defs(i, |v| dd |= v == c);
                dd
            }).cloned() else { continue };
            if d != c {
                continue;
            }
            let ok_to = match cc {
                Cond::Lt if cold(e) && !cold(t) => t,
                Cond::Ge if cold(t) && !cold(e) => e,
                _ => continue,
            };
            if !defs_in(f, &l, len).is_empty() || len == x {
                continue;
            }
            let k = if x == cnt.iv {
                // the compare itself reads the counter
                let at = bl.insts.iter().rposition(|i| matches!(i, Inst::ICmp(_, _, dd, _, _) if *dd == c)).unwrap();
                if !fresh_at(&l, &cnt, &stale, b, at) {
                    continue;
                }
                0
            } else {
                let Some(k) = fresh_offset(f, &l, &cnt, &stale, &ndef, x, 0) else { continue };
                k
            };
            if k < 0 && cnt.step != 1 {
                continue;
            }
            facts.push(Taken { block: b, to: ok_to });
            if !conds.contains(&(len, k)) {
                conds.push((len, k));
            }
        }
        if facts.is_empty() {
            continue;
        }
        // the guard: every condition, and-ed
        let mut guard: Vec<Inst> = Vec::new();
        let mut acc: Option<VReg> = None;
        fn and_in(guard: &mut Vec<Inst>, f: &mut Func, acc: &mut Option<VReg>, v: VReg) {
            *acc = Some(match *acc {
                None => v,
                Some(a) => {
                    let r = f.vreg(Cls::I);
                    guard.push(Inst::IBin(IOp::And, U64_TY, r, a, v));
                    r
                }
            });
        }
        for &(len, k) in &conds {
            if k >= 0 {
                // len >= k && n <= len - k
                let g2 = f.vreg(Cls::I);
                if k == 0 {
                    guard.push(Inst::ICmp(Cond::Le, false, g2, cnt.n, len));
                } else {
                    let g1 = f.vreg(Cls::I);
                    let lim = f.vreg(Cls::I);
                    guard.push(Inst::ICmpI(Cond::Ge, false, g1, len, k));
                    guard.push(Inst::IBinI(IOp::Sub, U64_TY, lim, len, k));
                    guard.push(Inst::ICmp(Cond::Le, false, g2, cnt.n, lim));
                    and_in(&mut guard, f, &mut acc, g1);
                }
                and_in(&mut guard, f, &mut acc, g2);
            } else {
                // n <= len && i >= -k (the counter's entry value; step 1, so no wrap)
                let g1 = f.vreg(Cls::I);
                let g2 = f.vreg(Cls::I);
                guard.push(Inst::ICmp(Cond::Le, false, g1, cnt.n, len));
                guard.push(Inst::ICmpI(Cond::Ge, false, g2, cnt.iv, -k));
                and_in(&mut guard, f, &mut acc, g1);
                and_in(&mut guard, f, &mut acc, g2);
            }
        }
        let g = acc.unwrap();
        if trace() {
            eprintln!("version: {} loop b{} ({} blocks, {} insts): {} checks, {} guard conds", f.name, l.header, l.blocks.len(), size, facts.len(), conds.len());
        }
        version_loop(f, &l, guard, g, &facts);
        changed += 1;
    }
    changed > 0
}
