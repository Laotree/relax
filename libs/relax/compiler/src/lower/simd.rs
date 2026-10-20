//! rustc's generic SIMD intrinsics (`core::intrinsics::simd`: simd_add .. simd_select) on
//! `#[repr(simd)]` values. A SIMD value lives in memory like any aggregate; each intrinsic is
//! lowered at its call site to the lane-typed vector IR, one 16-byte chunk at a time (`VLoad`,
//! `Inst::VX`, `VStore`). A value whose size is not a multiple of 16 goes through zeroed
//! 16-byte-padded copies (the padding lanes are computed and dropped). The back end encodes
//! each op natively where the target has an instruction sequence and legalises the rest to
//! per-lane scalar code (relax_backend::legal), so every lane type works on every target.
//! Store->load forwarding keeps chains of intrinsics in registers.

use super::*;

/// The lane type of a SIMD value.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Lane {
    S(VW),
    U(VW),
    F(VW),
}

impl Lane {
    fn w(self) -> VW {
        match self {
            Lane::S(w) | Lane::U(w) | Lane::F(w) => w,
        }
    }
}

impl<'a> Lcx<'a> {
    /// (lane type, lane count) of a `#[repr(simd)]` struct: one array field `[E; N]` or N
    /// fields of one primitive type E (the older form); None for any other type.
    fn simd_shape(&mut self, t: TyId) -> Option<(Lane, u32)> {
        let TyKind::Adt(d, args, _) = self.kind(t) else { return None };
        let nf = self.u.tcx.adts.get(&d).filter(|a| !a.is_enum && !a.is_union)?.variants[0].fields.len();
        let env = crate::tcx::TypingEnv::fully_monomorphized(&self.u.prog);
        let fts: Vec<TyId> = (0..nf).map(|i| self.u.tcx.field_ty(&self.u.prog, env, d, 0, i as u32, self.u.tcx.tys.list(args))).collect();
        let lane = |k: &TyKind| -> Option<Lane> {
            Some(match k {
                TyKind::Int(p) | TyKind::Float(p) => match p {
                    Prim::I8 => Lane::S(VW::B),
                    Prim::I16 => Lane::S(VW::H),
                    Prim::I32 => Lane::S(VW::S),
                    Prim::I64 | Prim::Isize => Lane::S(VW::D),
                    Prim::U8 => Lane::U(VW::B),
                    Prim::U16 => Lane::U(VW::H),
                    Prim::U32 => Lane::U(VW::S),
                    Prim::U64 | Prim::Usize => Lane::U(VW::D),
                    Prim::F32 => Lane::F(VW::S),
                    Prim::F64 => Lane::F(VW::D),
                    _ => return None,
                },
                _ => return None,
            })
        };
        match fts.as_slice() {
            [one] => match self.kind(*one) {
                TyKind::Array(e, n) => {
                    let n = n.try_to_target_usize(&self.u.tcx.tys)? as u32;
                    Some((lane(&self.kind(e))?, n))
                }
                k => Some((lane(&k)?, 1)),
            },
            [first, ..] => {
                let l = lane(&self.kind(*first))?;
                fts.iter().all(|f| *f == *first).then_some((l, nf as u32))
            }
            [] => None,
        }
    }

    /// The memory of an operand: (base, offset).
    fn simd_mem(&mut self, v: Val, t: TyId) -> (VReg, i32) {
        match v {
            Val::M(base, off) => (base, off),
            v => {
                let base = self.new_slot_for(t);
                self.store_val(base, 0, t, v);
                (base, 0)
            }
        }
    }

    /// A 16-byte-aligned slot of `chunks` * 16 bytes, its address.
    fn simd_scratch(&mut self, chunks: u32) -> VReg {
        let s = self.f.slot(16 * chunks, 16);
        self.f.slots[s as usize].born = self.coro.is_none();
        let d = self.f.vreg(Cls::I);
        self.emit(Inst::SlotAddr(d, s));
        d
    }

    /// An operand as `chunks` 16-byte pieces in memory: in place when its size is a whole number
    /// of chunks, else copied into a zeroed padded slot.
    fn simd_chunks(&mut self, v: Val, t: TyId, size: u32, chunks: u32) -> (VReg, i32) {
        let (base, off) = self.simd_mem(v, t);
        if size == 16 * chunks {
            return (base, off);
        }
        let pad = self.simd_scratch(chunks);
        let z = self.f.vreg(Cls::V128);
        self.emit(Inst::VConst(z, 0));
        for c in 0..chunks {
            self.emit(Inst::VStore(pad, 16 * c as i32, z));
        }
        let src = self.addr_add(base, off);
        self.emit(Inst::Copy(pad, src, size));
        (pad, 0)
    }

    /// The vector op of a lane-wise intrinsic on lanes `l`; None when the intrinsic is not
    /// lane-wise (or not defined for the lane type).
    fn simd_op(name: &str, l: Lane) -> Option<VX> {
        use Lane::*;
        let w = l.w();
        let h = NanBits::Host;
        let cmp = |c: Cond| match l {
            S(w) => VX::ICmp(c, w),
            U(w) => VX::UCmp(c, w),
            F(w) => VX::FCmp(c, w),
        };
        Some(match (name, l) {
            ("simd_add", F(_)) => VX::FAdd(w, h),
            ("simd_add", _) => VX::Add(w),
            ("simd_sub", F(_)) => VX::FSub(w, h),
            ("simd_sub", _) => VX::Sub(w),
            ("simd_mul", F(_)) => VX::FMul(w, h),
            ("simd_mul", _) => VX::MulLo(w),
            ("simd_div", F(_)) => VX::FDiv(w, h),
            ("simd_and", S(_) | U(_)) => VX::And,
            ("simd_or", S(_) | U(_)) => VX::Or,
            ("simd_xor", S(_) | U(_)) => VX::Xor,
            ("simd_shl", S(_) | U(_)) => VX::ShlV(w),
            ("simd_shr", S(_)) => VX::ShrSV(w),
            ("simd_shr", U(_)) => VX::ShrUV(w),
            ("simd_neg", F(_)) => VX::FNeg(w),
            ("simd_neg", S(_)) => VX::Neg(w),
            ("simd_fabs", F(_)) => VX::FAbs(w),
            ("simd_fsqrt", F(_)) => VX::FSqrt(w, h),
            ("simd_floor", F(_)) => VX::FRound(w, RoundTo::Floor),
            ("simd_ceil", F(_)) => VX::FRound(w, RoundTo::Ceil),
            ("simd_trunc", F(_)) => VX::FRound(w, RoundTo::Trunc),
            ("simd_round", F(_)) => VX::FRound(w, RoundTo::Away),
            ("simd_minimum_number_nsz", F(_)) => VX::FMinNum(w),
            ("simd_maximum_number_nsz", F(_)) => VX::FMaxNum(w),
            ("simd_saturating_add", S(_)) => VX::AddSatS(w),
            ("simd_saturating_add", U(_)) => VX::AddSatU(w),
            ("simd_saturating_sub", S(_)) => VX::SubSatS(w),
            ("simd_saturating_sub", U(_)) => VX::SubSatU(w),
            ("simd_eq", _) => cmp(Cond::Eq),
            ("simd_ne", _) => cmp(Cond::Ne),
            ("simd_lt", _) => cmp(Cond::Lt),
            ("simd_le", _) => cmp(Cond::Le),
            ("simd_gt", _) => cmp(Cond::Gt),
            ("simd_ge", _) => cmp(Cond::Ge),
            _ => return None,
        })
    }

    /// `core::intrinsics::simd::simd_*`; None when `name` is not one this lowering knows.
    pub(super) fn simd_intrinsic(&mut self, name: &str, vals: &[(Val, TyId)], t: TyId) -> Option<Val> {
        let select = name == "simd_select";
        let any = [Lane::S(VW::S), Lane::U(VW::S), Lane::F(VW::S)];
        if !select && !any.iter().any(|&l| Self::simd_op(name, l).is_some()) {
            return None;
        }
        let arity = match name {
            "simd_select" => 3,
            "simd_neg" | "simd_fabs" | "simd_fsqrt" | "simd_floor" | "simd_ceil" | "simd_trunc" | "simd_round" => 1,
            _ => 2,
        };
        // the operand whose lanes the op reads (simd_select: if_true; a compare: its inputs)
        let vt = vals.get(if select { 1 } else { 0 })?.1;
        let Some((lane, n)) = self.simd_shape(vt) else {
            let ts = crate::typeck::ty_to_string(false, &self.u.prog, &self.u.tcx, vt);
            self.err(self.pos, format!("E0511: invalid monomorphization of `{}` intrinsic: expected SIMD input type, found non-SIMD `{}`", name, ts));
            return Some(self.dummy_val(t));
        };
        let op = if select { None } else { Self::simd_op(name, lane) };
        if !select && op.is_none() {
            let ts = crate::typeck::ty_to_string(false, &self.u.prog, &self.u.tcx, vt);
            self.err(self.pos, format!("E0511: invalid monomorphization of `{}` intrinsic: unsupported element type of `{}`", name, ts));
            return Some(self.dummy_val(t));
        }
        if vals.len() != arity {
            self.err(self.pos, format!("internal: `{}` takes {} arguments", name, arity));
            return Some(self.dummy_val(t));
        }
        // the result (and simd_select's mask) has the lane count and width of the input
        for ty in [Some(t), select.then_some(vals[0].1)].into_iter().flatten() {
            match self.simd_shape(ty) {
                Some((l2, n2)) if n2 == n && l2.w() == lane.w() => {}
                _ => {
                    let (ts, us) = (crate::typeck::ty_to_string(false, &self.u.prog, &self.u.tcx, ty), crate::typeck::ty_to_string(false, &self.u.prog, &self.u.tcx, vt));
                    self.err(self.pos, format!("E0511: invalid monomorphization of `{}` intrinsic: `{}` must have {} lanes of the width of `{}`", name, ts, n, us));
                    return Some(self.dummy_val(t));
                }
            }
        }
        let size = n * lane.w().bits() / 8;
        let chunks = size.div_ceil(16);
        let ops: Vec<(VReg, i32)> = vals.iter().map(|(v, ty)| self.simd_chunks(v.clone(), *ty, size, chunks)).collect();
        let out = if size == 16 * chunks { self.new_slot_for(t) } else { self.simd_scratch(chunks) };
        for c in 0..chunks as i32 {
            let regs: Vec<VReg> = ops
                .iter()
                .map(|&(base, off)| {
                    let r = self.f.vreg(Cls::V128);
                    self.emit(Inst::VLoad(r, base, off + 16 * c));
                    r
                })
                .collect();
            let d = self.f.vreg(Cls::V128);
            match op {
                None => self.emit(Inst::VSel(d, regs[0], regs[1], regs[2])),
                Some(op) => self.emit(Inst::VX(op, d, regs[0], if arity == 1 { regs[0] } else { regs[1] })),
            }
            self.emit(Inst::VStore(out, 16 * c, d));
        }
        if size == 16 * chunks {
            return Some(Val::M(out, 0));
        }
        let res = self.new_slot_for(t);
        self.emit(Inst::Copy(res, out, size));
        Some(Val::M(res, 0))
    }
}
