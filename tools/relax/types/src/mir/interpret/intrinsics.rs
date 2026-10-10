//! rustc_const_eval/src/interpret/intrinsics.rs:170,931,1045,1106;
//! const_eval/machine.rs:489,508,538. Names are resolved once, execution uses DefId.
use super::operand::Value;
use super::*;
use std::collections::HashMap;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Intrinsic {
    SizeOf,
    AlignOf,
    NeedsDrop,
    Transmute,
    Ctpop,
    Ctlz,
    Cttz,
    CtlzNonzero,
    CttzNonzero,
    Bswap,
    Bitreverse,
    RotateLeft,
    RotateRight,
    WrappingAdd,
    WrappingSub,
    WrappingMul,
    UncheckedAdd,
    UncheckedSub,
    UncheckedMul,
    UncheckedDiv,
    UncheckedRem,
    UncheckedShl,
    UncheckedShr,
    SaturatingAdd,
    SaturatingSub,
    ExactDiv,
    PtrOffsetFrom,
    PtrOffsetFromUnsigned,
    Copy,
    CopyNonoverlapping,
    WriteBytes,
    DiscriminantValue,
    TypeId,
    TypeIdHi,
    TypeName,
    ConstAllocate,
    ConstDeallocate,
    ConstMakeGlobal,
    Assume,
    Likely,
    Unlikely,
    BlackBox,
    MinAlignOfVal,
    SizeOfVal,
}
const NAMES: &[(&str, Intrinsic)] = &[
    ("size_of", Intrinsic::SizeOf),
    ("align_of", Intrinsic::AlignOf),
    ("min_align_of", Intrinsic::AlignOf),
    ("needs_drop", Intrinsic::NeedsDrop),
    ("transmute", Intrinsic::Transmute),
    ("ctpop", Intrinsic::Ctpop),
    ("ctlz", Intrinsic::Ctlz),
    ("cttz", Intrinsic::Cttz),
    ("ctlz_nonzero", Intrinsic::CtlzNonzero),
    ("cttz_nonzero", Intrinsic::CttzNonzero),
    ("bswap", Intrinsic::Bswap),
    ("bitreverse", Intrinsic::Bitreverse),
    ("rotate_left", Intrinsic::RotateLeft),
    ("rotate_right", Intrinsic::RotateRight),
    ("wrapping_add", Intrinsic::WrappingAdd),
    ("wrapping_sub", Intrinsic::WrappingSub),
    ("wrapping_mul", Intrinsic::WrappingMul),
    ("unchecked_add", Intrinsic::UncheckedAdd),
    ("unchecked_sub", Intrinsic::UncheckedSub),
    ("unchecked_mul", Intrinsic::UncheckedMul),
    ("unchecked_div", Intrinsic::UncheckedDiv),
    ("unchecked_rem", Intrinsic::UncheckedRem),
    ("unchecked_shl", Intrinsic::UncheckedShl),
    ("unchecked_shr", Intrinsic::UncheckedShr),
    ("saturating_add", Intrinsic::SaturatingAdd),
    ("saturating_sub", Intrinsic::SaturatingSub),
    ("exact_div", Intrinsic::ExactDiv),
    ("ptr_offset_from", Intrinsic::PtrOffsetFrom),
    ("ptr_offset_from_unsigned", Intrinsic::PtrOffsetFromUnsigned),
    ("copy", Intrinsic::Copy),
    ("copy_nonoverlapping", Intrinsic::CopyNonoverlapping),
    ("write_bytes", Intrinsic::WriteBytes),
    ("discriminant_value", Intrinsic::DiscriminantValue),
    ("type_id", Intrinsic::TypeId),
    ("type_id_hi", Intrinsic::TypeIdHi),
    ("type_name", Intrinsic::TypeName),
    ("const_allocate", Intrinsic::ConstAllocate),
    ("const_deallocate", Intrinsic::ConstDeallocate),
    ("const_make_global", Intrinsic::ConstMakeGlobal),
    ("assume", Intrinsic::Assume),
    ("likely", Intrinsic::Likely),
    ("unlikely", Intrinsic::Unlikely),
    ("black_box", Intrinsic::BlackBox),
    ("min_align_of_val", Intrinsic::MinAlignOfVal),
    ("align_of_val", Intrinsic::MinAlignOfVal),
    ("size_of_val", Intrinsic::SizeOfVal),
];
#[derive(Default)]
pub struct Intrinsics {
    items: HashMap<DefId, Intrinsic>,
}
impl Intrinsics {
    /// Register only items identified as intrinsic definitions by the caller's resolver.
    pub fn register(&mut self, def: DefId, name: &str) -> Result<(), ConstEvalError> {
        for &(n, intrinsic) in NAMES {
            if n == name {
                self.items.insert(def, intrinsic);
                return Ok(());
            }
        }
        Err(ConstEvalError::Unsupported("intrinsic is not supported in constant evaluation"))
    }
    pub fn get(&self, def: DefId) -> Option<Intrinsic> {
        self.items.get(&def).copied()
    }
}
impl Interpreter<'_> {
    pub(super) fn copy_intrinsic(&mut self, src: Value, dst: Value, count: Value, nonoverlap: bool) -> Result<(), ConstEvalError> {
        let ty = match self.kind(src.ty) {
            TyKind::Ptr(_, t) | TyKind::Ref(_, t, _) => *t,
            _ => return Err(ConstEvalError::InvalidMir("copy source is not a pointer")),
        };
        let l = self.layout(ty)?;
        let n = bits(self.scalar(count)?)?;
        let size = n.checked_mul(l.size as u128).filter(|n| *n <= i64::MAX as u128).ok_or(ConstEvalError::Ub("copy size overflow"))? as u64;
        self.copy_bytes(self.scalar(src)?, self.scalar(dst)?, size, l.align as u64, nonoverlap)
    }
    pub(super) fn intrinsic(&mut self, intrinsic: Intrinsic, types: &[TyId], args: &[Value], dest: MPlace) -> Result<(), ConstEvalError> {
        use Intrinsic::*;
        let dl = self.layout(dest.ty)?;
        let arg = |i: usize| args.get(i).copied().ok_or(ConstEvalError::InvalidMir("missing intrinsic argument"));
        let type_arg = || types.first().copied().ok_or(ConstEvalError::InvalidMir("missing intrinsic type argument"));
        let v = match intrinsic {
            SizeOf | AlignOf | SizeOfVal | MinAlignOfVal => {
                let ty = type_arg()?;
                if self.provider.is_unsized(ty)? {
                    return Err(ConstEvalError::Unsupported("unsized layout intrinsic requires dynamic layout query"));
                }
                let l = self.layout(ty)?;
                Immediate::Scalar(int(
                    if matches!(intrinsic, SizeOf | SizeOfVal) { l.size as u128 } else { l.align as u128 },
                    dl.size as u8,
                ))
            }
            NeedsDrop => Immediate::Scalar(int(self.provider.needs_drop(type_arg()?)? as u128, 1)),
            TypeId | TypeIdHi => {
                let hash = self.provider.type_hash(type_arg()?)?;
                Immediate::Scalar(int(if intrinsic == TypeId { hash } else { hash >> 64 }, 8))
            }
            TypeName => {
                let name = self.provider.type_name(type_arg()?)?;
                let ptr = self.allocate(name.len() as u64, 1, MemoryKind::Global)?;
                let id = ptr_parts(ptr)?.0;
                let a = &mut self.memory.allocations[id.0 as usize];
                a.bytes.copy_from_slice(name.as_bytes());
                a.init_mask.fill(true);
                a.mutability = Mutability::Not;
                Immediate::ScalarPair(ptr, int(name.len() as u128, 8))
            }
            Transmute => return self.transmute(dest, arg(0)?),
            Likely | Unlikely | BlackBox => return self.write(dest, arg(0)?),
            Assume => {
                if bits(self.scalar(arg(0)?)?)? != 1 {
                    return Err(ConstEvalError::Ub("assume called with false"));
                }
                Immediate::Uninit
            }
            ConstAllocate => {
                let size = bits(self.scalar(arg(0)?)?)? as u64;
                let align = bits(self.scalar(arg(1)?)?)? as u64;
                Immediate::Scalar(self.allocate(size, align, MemoryKind::Heap(false))?)
            }
            ConstDeallocate => {
                self.deallocate(self.scalar(arg(0)?)?, bits(self.scalar(arg(1)?)?)? as u64, bits(self.scalar(arg(2)?)?)? as u64)?;
                Immediate::Uninit
            }
            ConstMakeGlobal => {
                let ptr = self.scalar(arg(0)?)?;
                self.make_global(ptr)?;
                Immediate::Scalar(ptr)
            }
            Copy | CopyNonoverlapping => {
                self.copy_intrinsic(arg(0)?, arg(1)?, arg(2)?, intrinsic == CopyNonoverlapping)?;
                Immediate::Uninit
            }
            WriteBytes => {
                let ptr = self.scalar(arg(0)?)?;
                let byte = bits(self.scalar(arg(1)?)?)? as u8;
                let n = bits(self.scalar(arg(2)?)?)?;
                let l = self.layout(type_arg()?)?;
                let size = n
                    .checked_mul(l.size as u128)
                    .filter(|n| *n <= i64::MAX as u128)
                    .ok_or(ConstEvalError::Ub("write_bytes size overflow"))? as u64;
                self.uninit(ptr, size)?;
                if let Some((id, off)) = self.access(ptr, size, l.align as u64, true)? {
                    let a = &mut self.memory.allocations[id.0 as usize];
                    a.bytes[off..off + size as usize].fill(byte);
                    a.init_mask[off..off + size as usize].fill(true);
                }
                Immediate::Uninit
            }
            DiscriminantValue => {
                let p = self.deref(arg(0)?)?;
                Immediate::Scalar(int(self.discriminant(p.ty, self.read_discriminant(p)?)?, dl.size as u8))
            }
            PtrOffsetFrom | PtrOffsetFromUnsigned => {
                let stride = self.layout(type_arg()?)?.size as i128;
                if stride == 0 {
                    return Err(ConstEvalError::Ub("ptr_offset_from called on zero-sized type"));
                }
                let a = self.scalar(arg(0)?)?;
                let b = self.scalar(arg(1)?)?;
                let delta = if a == b {
                    0
                } else {
                    let (aid, ao) = ptr_parts(a)?;
                    let (bid, bo) = ptr_parts(b)?;
                    if aid != bid {
                        return Err(ConstEvalError::Ub("ptr_offset_from called on pointers into different allocations"));
                    }
                    self.access(a, 0, 1, false)?;
                    self.access(b, 0, 1, false)?;
                    ao as i128 - bo as i128
                };
                if delta % stride != 0
                    || delta < i64::MIN as i128
                    || delta > i64::MAX as i128
                    || (intrinsic == PtrOffsetFromUnsigned && delta < 0)
                {
                    return Err(ConstEvalError::Ub("invalid ptr_offset_from distance"));
                }
                Immediate::Scalar(int((delta / stride) as u128, dl.size as u8))
            }
            Ctpop | Ctlz | Cttz | CtlzNonzero | CttzNonzero | Bswap | Bitreverse | RotateLeft | RotateRight => {
                let a = arg(0)?;
                let n = bits(self.scalar(a)?)?;
                let width = self.layout(a.ty)?.size * 8;
                let out = match intrinsic {
                    Ctpop => n.count_ones() as u128,
                    Ctlz | CtlzNonzero => {
                        if n == 0 && intrinsic == CtlzNonzero {
                            return Err(ConstEvalError::Ub("ctlz_nonzero called with zero"));
                        }
                        (n.leading_zeros() - (128 - width)) as u128
                    }
                    Cttz | CttzNonzero => {
                        if n == 0 && intrinsic == CttzNonzero {
                            return Err(ConstEvalError::Ub("cttz_nonzero called with zero"));
                        }
                        n.trailing_zeros().min(width) as u128
                    }
                    Bswap => n.swap_bytes() >> (128 - width),
                    Bitreverse => n.reverse_bits() >> (128 - width),
                    RotateLeft | RotateRight => {
                        let shift = (bits(self.scalar(arg(1)?)?)? % width as u128) as u32;
                        if shift == 0 {
                            n
                        } else if intrinsic == RotateLeft {
                            (n << shift) | (n >> (width - shift))
                        } else {
                            (n >> shift) | (n << (width - shift))
                        }
                    }
                    _ => unreachable!(),
                };
                Immediate::Scalar(int(out, dl.size as u8))
            }
            WrappingAdd | WrappingSub | WrappingMul | UncheckedAdd | UncheckedSub | UncheckedMul | UncheckedDiv | UncheckedRem
            | UncheckedShl | UncheckedShr | SaturatingAdd | SaturatingSub | ExactDiv => {
                let a = arg(0)?;
                let b = arg(1)?;
                let op = match intrinsic {
                    WrappingAdd => BinOp::Add,
                    WrappingSub => BinOp::Sub,
                    WrappingMul => BinOp::Mul,
                    UncheckedAdd => BinOp::AddUnchecked,
                    UncheckedSub => BinOp::SubUnchecked,
                    UncheckedMul => BinOp::MulUnchecked,
                    UncheckedDiv | ExactDiv => BinOp::Div,
                    UncheckedRem => BinOp::Rem,
                    UncheckedShl => BinOp::ShlUnchecked,
                    UncheckedShr => BinOp::ShrUnchecked,
                    SaturatingAdd => BinOp::AddWithOverflow,
                    SaturatingSub => BinOp::SubWithOverflow,
                    _ => unreachable!(),
                };
                let result = self.binary(op, a, b, dest.ty)?;
                if intrinsic == ExactDiv {
                    let rem = self.binary(BinOp::Rem, a, b, dest.ty)?;
                    if !matches!(rem, Immediate::Scalar(Scalar::Int { bits: 0, .. })) {
                        return Err(ConstEvalError::Ub("exact_div: the remainder is not zero"));
                    }
                }
                if let Immediate::ScalarPair(result, overflow) = result {
                    if bits(overflow)? == 0 {
                        Immediate::Scalar(result)
                    } else {
                        let size = dl.size as u8;
                        let bound = if signed(self.kind(a.ty)) {
                            let negative = sext(bits(self.scalar(a)?)?, size) < 0;
                            if negative {
                                1u128 << (size * 8 - 1)
                            } else {
                                mask(size) >> 1
                            }
                        } else if intrinsic == SaturatingAdd {
                            mask(size)
                        } else {
                            0
                        };
                        Immediate::Scalar(int(bound, size))
                    }
                } else {
                    result
                }
            }
        };
        self.write(dest, Value::immediate(dest.ty, v))
    }
}
