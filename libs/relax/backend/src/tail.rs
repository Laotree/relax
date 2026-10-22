//! Sibling calls: a call in tail position becomes a jump, as LLVM's sibcall lowering does for a
//! call rustc emits right before the return (X86ISelLowering IsEligibleForTailCallOptimization,
//! AArch64ISelLowering isEligibleForTailCallOptimization; the `tail` marking of TailCallElim).
//!
//! A call is in tail position when only moves of its results lead from it to the function's
//! return of exactly those results (`returns_results`): no drop, no copy and no other code runs
//! after it. An invoked call (`Term::Invoke`) is never one -- its unwind edge runs this function's
//! cleanup -- so the order of drops and unwinding stays rustc's: a panic in the callee unwinds
//! straight into the caller's caller, which is where it went before (the plain call had no pad
//! here).
//!
//! The jump reuses the caller's frame position, so it is only made when the callee can find
//! everything where a call would put it and nothing it reaches lives in the caller's frame:
//! - every argument goes in a register of the callee's convention (no stack arguments), and the
//!   result comes back where the caller's own return puts it (the same registers, no aggregate
//!   result buffer, no narrow C result the caller's caller would read extended);
//! - both sides keep the same callee-saved registers: Relax's convention and the host C
//!   convention agree on x86-64 SysV and AAPCS64; Win64 C bodies and calls are left alone;
//! - no address in this function's frame escapes (LLVM: no alloca reaches the call), checked
//!   for the whole function: a slot address that is stored, returned, passed to any call or to
//!   inline assembly could be read by the callee. A result buffer passed to an `sret` callee
//!   does not escape (the callee only writes it, rustc marks it nocapture), but is never an
//!   argument of the tail call itself; a C body with aggregate parameters rebuilt in its frame
//!   makes none.
//!
//! MAKEPAD_RUN_OPT=-tailcall: every call stays a call.

use crate::cabi::{self, ArgPlan, PLoc, RetPlan};
use crate::rir::*;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Arch {
    X64,
    Arm64,
}

impl Arch {
    /// argument registers of Relax's own convention (integer, float)
    fn regs(self) -> (usize, usize) {
        match self {
            Arch::X64 => (6, 8),
            Arch::Arm64 => (8, 8),
        }
    }

    /// C conventions whose callee-saved registers and scalar argument / result registers are
    /// Relax's own on this architecture
    fn c_compatible(self, t: cabi::Target) -> bool {
        match self {
            Arch::X64 => t == cabi::Target::SysV,
            Arch::Arm64 => matches!(t, cabi::Target::Darwin64 | cabi::Target::Aapcs64),
        }
    }
}

/// Per block: the index of its call made as a jump (what follows it -- moves of the results, the
/// jumps to the Ret, the Ret -- is not emitted). Empty when the function has none.
pub fn sibling_calls(options: &relax_session::Options, f: &Func, reach: &[bool], arch: Arch) -> Vec<Option<usize>> {
    if f.naked || crate::stats::opt_off(options, "-tailcall") {
        return Vec::new();
    }
    let mut cands = Vec::new();
    for (bi, b) in f.blocks.iter().enumerate() {
        if !reach[bi] || matches!(b.term, Term::Invoke(..)) {
            continue;
        }
        // the block's last call, followed by moves only
        let Some(k) = b.insts.iter().rposition(|i| !matches!(i, Inst::Mov(..))) else { continue };
        let Inst::Call(c, _, rets) = &b.insts[k] else { continue };
        if !matches!(c, Callee::Asm(_) | Callee::Host(_) | Callee::CHost(..)) && returns_results(f, bi, k + 1, rets) {
            cands.push((bi, k));
        }
    }
    if cands.is_empty() || !caller_ok(f, arch) {
        return Vec::new();
    }
    let Some(derived) = frame_addresses(f, reach) else { return Vec::new() };
    let mut out = vec![None; f.blocks.len()];
    let mut any = false;
    for (bi, k) in cands {
        let Inst::Call(c, args, rets) = &f.blocks[bi].insts[k] else { continue };
        if args.iter().any(|a| derived[a.0 as usize]) {
            continue;
        }
        if let Callee::Indirect(v) | Callee::CIndirect(v, _) = c {
            if derived[v.0 as usize] {
                continue;
            }
        }
        if callee_ok(f, arch, c, args, rets) {
            out[bi] = Some(k);
            any = true;
        }
    }
    if any { out } else { Vec::new() }
}

/// Whether everything from instruction `at` of block `b` on only moves the results `rets` of the
/// call before it into the values the function returns: moves, jumps through blocks of moves
/// (the join of an `if` whose arms end in calls, as rustc's MIR has it), a Ret of exactly the
/// results in order (LLVM's CodeGenPrepare dupRetToEnableTailCallOpts does the same through phis).
pub fn returns_results(f: &Func, mut b: usize, mut at: usize, rets: &[VReg]) -> bool {
    // the values holding each result (result index per vreg)
    let mut holds: Vec<(VReg, usize)> = rets.iter().enumerate().map(|(k, r)| (*r, k)).collect();
    for _ in 0..8 {
        let blk = &f.blocks[b];
        for i in &blk.insts[at..] {
            let Inst::Mov(d, s) = i else { return false };
            let from = holds.iter().find(|x| x.0 == *s).map(|x| x.1);
            holds.retain(|x| x.0 != *d);
            if let Some(k) = from {
                holds.push((*d, k));
            }
        }
        match &blk.term {
            Term::Ret(vals) => {
                return vals.len() == rets.len() && vals.iter().enumerate().all(|(k, v)| holds.iter().any(|x| x.0 == *v && x.1 == k));
            }
            Term::Jump(t) => {
                b = *t as usize;
                at = 0;
            }
            _ => return false,
        }
    }
    false
}

/// The caller's own convention allows its frame to be replaced: Relax's, or a C body in a
/// compatible convention that returns no aggregate and rebuilds no aggregate parameter in its
/// frame.
fn caller_ok(f: &Func, arch: Arch) -> bool {
    let Some(sig) = &f.cabi else { return true };
    if !arch.c_compatible(sig.conv.target()) || sig.ret.is_some() || sig.n_fixed != u32::MAX {
        return false;
    }
    let plan = cabi::plan(sig, sig.conv.target());
    plan.ret == RetPlan::Scalar && plan.args.iter().all(|a| !matches!(a, ArgPlan::Parts(_)))
}

fn callee_ok(f: &Func, arch: Arch, c: &Callee, args: &[VReg], rets: &[VReg]) -> bool {
    match c {
        Callee::Fn(_) | Callee::Indirect(_) => {
            let (ni, nf) = arch.regs();
            let (mut i, mut fl) = (0, 0);
            for a in args {
                match f.vregs[a.0 as usize] {
                    Cls::I => i += 1,
                    Cls::F32 | Cls::F64 => fl += 1,
                    _ => return false,
                }
            }
            i <= ni && fl <= nf && rets_ok(f, rets)
        }
        Callee::CFn(_, sig) | Callee::CIndirect(_, sig) => {
            if !arch.c_compatible(sig.conv.target()) || sig.ret.is_some() || sig.n_fixed != u32::MAX {
                return false;
            }
            // a narrow C result is extended by the caller after the call: the caller's caller
            // reads it so only when it is a C caller of the same result type
            if sig.ret_narrow.is_some() && f.cabi.as_ref().map(|s| s.ret_narrow) != Some(sig.ret_narrow) {
                return false;
            }
            let plan = cabi::plan(sig, sig.conv.target());
            plan.stack_bytes == 0 && plan.ret == RetPlan::Scalar && plan.args.iter().all(|a| matches!(a, ArgPlan::Scalar(PLoc::Int(_) | PLoc::Flt(_), _))) && rets.len() <= 1 && rets_ok(f, rets)
        }
        _ => false,
    }
}

/// Results in registers: at most two of each class, scalars only.
fn rets_ok(f: &Func, rets: &[VReg]) -> bool {
    let (mut i, mut fl) = (0, 0);
    for r in rets {
        match f.vregs[r.0 as usize] {
            Cls::I => i += 1,
            Cls::F32 | Cls::F64 => fl += 1,
            _ => return false,
        }
    }
    i <= 2 && fl <= 2
}

/// Per value: it may hold an address in this function's frame (a slot address, or computed from
/// one). None when such an address escapes anywhere in the function.
pub fn frame_addresses(f: &Func, reach: &[bool]) -> Option<Vec<bool>> {
    let nv = f.vregs.len();
    let mut d = vec![false; nv];
    let mut changed = true;
    while changed {
        changed = false;
        for (bi, b) in f.blocks.iter().enumerate() {
            if !reach[bi] {
                continue;
            }
            for i in &b.insts {
                let from = match i {
                    Inst::SlotAddr(..) => true,
                    // a loaded value is not the address it was loaded from (an address stored in
                    // memory has escaped already)
                    Inst::Load(..) | Inst::LoadX(..) | Inst::VLoad(..) | Inst::VLoadX(..) | Inst::AtomicLoad(..) | Inst::AtomicRmw(..) | Inst::AtomicCas(..) | Inst::VGather(..) | Inst::VTbl(..) => false,
                    Inst::Call(Callee::Asm(_), _, _) => true,
                    Inst::Call(..) | Inst::Cpuid(..) | Inst::Xgetbv(..) | Inst::FpEnv(..) => false,
                    _ => {
                        let mut any = false;
                        crate::regalloc::for_uses(i, |u| any |= d[u.0 as usize]);
                        any
                    }
                };
                if from {
                    i.defs(|x| {
                        if !d[x.0 as usize] {
                            d[x.0 as usize] = true;
                            changed = true;
                        }
                    });
                }
            }
        }
    }
    for (bi, b) in f.blocks.iter().enumerate() {
        if !reach[bi] {
            continue;
        }
        for i in &b.insts {
            let esc = match i {
                Inst::Store(_, _, _, s) | Inst::StoreX(_, _, _, _, _, s) | Inst::VStore(_, _, s) | Inst::VStoreX(_, _, _, _, s) | Inst::AtomicStore(_, _, _, s) | Inst::AtomicRmw(_, _, _, _, _, s) => d[s.0 as usize],
                Inst::AtomicCas(_, _, _, _, _, e, n) => d[e.0 as usize] || d[n.0 as usize],
                Inst::Call(c, args, _) => {
                    let sret = matches!(c, Callee::Fn(id) if f.sret_callees.contains(id));
                    let target = matches!(c, Callee::Indirect(v) | Callee::CIndirect(v, _) if d[v.0 as usize]);
                    target || args.iter().enumerate().any(|(k, a)| d[a.0 as usize] && !(sret && k == 0))
                }
                _ => false,
            };
            if esc {
                return None;
            }
        }
        if let Term::Ret(vals) = &b.term {
            if vals.iter().any(|v| d[v.0 as usize]) {
                return None;
            }
        }
    }
    Some(d)
}
