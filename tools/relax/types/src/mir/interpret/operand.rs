//! rustc_const_eval/src/interpret/operand.rs (Immediate/Operand, read_immediate),
//! operator.rs:84 and cast.rs:23. MIR's ordinary integer arithmetic wraps; Assert
//! implements language overflow checks, while Unchecked operators fail on overflow.
use super::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Immediate {
    Scalar(Scalar),
    ScalarPair(Scalar, Scalar),
    Uninit,
}
#[derive(Clone, Copy)]
pub(super) enum OperandValue {
    Immediate(Immediate),
    Indirect(MPlace),
}
#[derive(Clone, Copy)]
pub(super) struct Value {
    pub ty: TyId,
    pub value: OperandValue,
}
impl Value {
    pub fn indirect(p: MPlace) -> Self {
        Self { ty: p.ty, value: OperandValue::Indirect(p) }
    }
    pub fn immediate(ty: TyId, v: Immediate) -> Self {
        Self { ty, value: OperandValue::Immediate(v) }
    }
}
impl<'a> Interpreter<'a> {
    pub(super) fn immediate(&self, value: Value) -> Result<Immediate, ConstEvalError> {
        let l = self.layout(value.ty)?;
        let v = match value.value {
            OperandValue::Immediate(v) => v,
            OperandValue::Indirect(p) => {
                if l.size == 0 {
                    return Ok(Immediate::Uninit);
                }
                match self.kind(p.ty) {
                    TyKind::Ptr(..) | TyKind::Ref(..) if l.size == 16 => Immediate::ScalarPair(
                        self.read_scalar(p.ptr, 8, p.align)?,
                        self.read_scalar(add_offset(p.ptr, 8)?, 8, p.align.min(8))?,
                    ),
                    TyKind::Tuple(fields) if fields.len() == 2 => {
                        let a = self.field(p, 0)?;
                        let b = self.field(p, 1)?;
                        Immediate::ScalarPair(self.scalar(Value::indirect(a))?, self.scalar(Value::indirect(b))?)
                    }
                    TyKind::Int(_)
                    | TyKind::Float(_)
                    | TyKind::Bool
                    | TyKind::Char
                    | TyKind::Ptr(..)
                    | TyKind::Ref(..)
                    | TyKind::FnPtr(..) => Immediate::Scalar(self.read_scalar(p.ptr, l.size as u64, p.align)?),
                    _ => return Err(ConstEvalError::InvalidMir("aggregate used as an immediate")),
                }
            }
        };
        if let Immediate::Scalar(s) = v {
            if let Scalar::Int { bits, size } = s {
                if size as u32 != l.size || size == 0 || size > 16 || bits & !mask(size) != 0 {
                    return Err(ConstEvalError::Ub("invalid scalar representation"));
                }
            }
            match self.kind(value.ty) {
                TyKind::Bool if bits(s)? > 1 => return Err(ConstEvalError::Ub("invalid boolean value")),
                TyKind::Char if char::from_u32(bits(s)? as u32).is_none() => return Err(ConstEvalError::Ub("invalid char value")),
                TyKind::Int(_) | TyKind::Float(_) => {
                    bits(s)?;
                }
                TyKind::FnPtr(..) => {
                    let (id, off) = ptr_parts(s)?;
                    if off != 0 || !matches!(self.kinds.get(id.0 as usize), Some(MemoryKind::Function(..))) {
                        return Err(ConstEvalError::Ub("invalid function pointer"));
                    }
                }
                _ => {}
            }
        }
        Ok(v)
    }
    pub(super) fn scalar(&self, value: Value) -> Result<Scalar, ConstEvalError> {
        match self.immediate(value)? {
            Immediate::Scalar(s) => Ok(s),
            Immediate::Uninit => Err(ConstEvalError::Ub("using uninitialized data")),
            _ => Err(ConstEvalError::InvalidMir("scalar pair used as scalar")),
        }
    }
    pub(super) fn write(&mut self, dest: MPlace, value: Value) -> Result<(), ConstEvalError> {
        let dl = self.layout(dest.ty)?;
        let sl = self.layout(value.ty)?;
        if dl.size != sl.size {
            return Err(ConstEvalError::InvalidMir("assignment size mismatch"));
        }
        match value.value {
            OperandValue::Indirect(p) => self.copy_bytes(p.ptr, dest.ptr, dl.size as u64, p.align.min(dest.align), false),
            OperandValue::Immediate(Immediate::Uninit) => self.uninit(dest.ptr, dl.size as u64),
            OperandValue::Immediate(Immediate::Scalar(s)) => {
                if dl.size == 0 {
                    Ok(())
                } else {
                    self.write_scalar(dest.ptr, s, dl.size as u64, dest.align)
                }
            }
            OperandValue::Immediate(Immediate::ScalarPair(a, b)) => {
                if matches!(self.kind(dest.ty), TyKind::Ref(..) | TyKind::Ptr(..)) {
                    self.write_scalar(dest.ptr, a, 8, dest.align)?;
                    self.write_scalar(add_offset(dest.ptr, 8)?, b, 8, dest.align.min(8))
                } else {
                    let x = self.field(dest, 0)?;
                    let y = self.field(dest, 1)?;
                    self.write_scalar(x.ptr, a, self.layout(x.ty)?.size as u64, x.align)?;
                    self.write_scalar(y.ptr, b, self.layout(y.ty)?.size as u64, y.align)
                }
            }
        }?;
        self.retag_copy(MPlace { ty: value.ty, ..dest })?;
        if value.ty != dest.ty {
            self.retag_copy(dest)?;
        }
        Ok(())
    }
    /// Retag the references in a typed copy without following their referents.
    /// rustc_const_eval/src/interpret/place.rs:845-874, validity.rs:648-693;
    /// const_eval/machine.rs:845-880. Raw copies never enter this walk.
    pub(super) fn retag_copy(&mut self, p: MPlace) -> Result<(), ConstEvalError> {
        match self.kind(p.ty) {
            TyKind::Ref(false, pointee, _) => {
                let pointee = *pointee;
                let ptr = self.read_scalar(p.ptr, 8, p.align)?;
                if let Scalar::Ptr { provenance, offset } = ptr {
                    if !provenance.immutable() {
                        let provenance =
                            if self.provider.is_freeze(pointee)? { provenance.as_immutable() } else { provenance.as_shared_ref() };
                        self.write_scalar(p.ptr, Scalar::Ptr { provenance, offset }, 8, p.align)?;
                    }
                }
            }
            TyKind::Array(..) => {
                for i in 0..self.len(p)? {
                    self.retag_copy(self.index(p, i)?)?;
                }
            }
            TyKind::Tuple(_) | TyKind::Adt(..) | TyKind::Closure(..) => {
                if let TyKind::Adt(d, _, _) = self.kind(p.ty) {
                    if self.provider.tcx().adts[d].is_union {
                        return Ok(());
                    }
                }
                let v = self.read_discriminant(p)?;
                let l = self.layout(p.ty)?;
                let count = l.variant_fields.get(v as usize).unwrap_or(&l.fields).len();
                for i in 0..count {
                    self.retag_copy(self.field(MPlace { variant: Some(v), ..p }, i as u32)?)?;
                }
            }
            _ => {}
        }
        Ok(())
    }
    pub(super) fn operand(&mut self, op: &Operand) -> Result<Value, ConstEvalError> {
        match op {
            // As in rustc's interpreter, Move does not poison the source; move checking is MIR's job.
            Operand::Copy(p) | Operand::Move(p) => {
                let p = self.place(p)?;
                let v = Value::indirect(p);
                match self.kind(p.ty) {
                    TyKind::Int(_)
                    | TyKind::Float(_)
                    | TyKind::Bool
                    | TyKind::Char
                    | TyKind::Ref(..)
                    | TyKind::Ptr(..)
                    | TyKind::FnPtr(..) => Ok(Value::immediate(p.ty, self.immediate(v)?)),
                    _ => Ok(v),
                }
            }
            Operand::Constant(c) => self.constant(&c.const_),
        }
    }
    pub(super) fn constant(&mut self, c: &Const) -> Result<Value, ConstEvalError> {
        match c {
            Const::Val(v, ty) => {
                let l = self.layout(*ty)?;
                Ok(match *v {
                    ConstValue::Scalar(s) => Value::immediate(*ty, Immediate::Scalar(s)),
                    ConstValue::ZeroSized if l.size == 0 => Value::immediate(*ty, Immediate::Uninit),
                    ConstValue::ZeroSized => return Err(ConstEvalError::InvalidMir("non-zero-sized constant")),
                    ConstValue::Slice { alloc, meta } => Value::immediate(
                        *ty,
                        Immediate::ScalarPair(
                            Scalar::Ptr { provenance: CtfeProvenance::new(alloc).as_immutable(), offset: 0 },
                            int(meta as u128, 8),
                        ),
                    ),
                    ConstValue::Indirect { alloc, offset } => Value::indirect(MPlace {
                        ptr: Scalar::Ptr { provenance: CtfeProvenance::new(alloc).as_immutable(), offset },
                        ty: *ty,
                        meta: None,
                        variant: None,
                        align: l.align as u64,
                    }),
                })
            }
            Const::Unevaluated { def, args, promoted } => {
                let body = self.provider.body(*def, args).ok_or(ConstEvalError::MissingBody(*def))?;
                let body = if let Some(id) = promoted {
                    body.promoted.get(id.0 as usize).ok_or(ConstEvalError::InvalidMir("missing promoted MIR"))?
                } else {
                    body
                };
                let ty = body.local_decls[0].ty;
                let p = self.allocate_place(ty, MemoryKind::Stack)?;
                let depth = self.frames.len();
                self.push_frame(body, &[], Some(p))?;
                while self.frames.len() > depth {
                    self.step()?;
                }
                self.validate_value(p, &mut Vec::new())?;
                self.intern(ptr_parts(p.ptr)?.0)?;
                Ok(Value::indirect(p))
            }
        }
    }
    pub(super) fn binary(&self, op: BinOp, lhs: Value, rhs: Value, dest_ty: TyId) -> Result<Immediate, ConstEvalError> {
        let l = self.scalar(lhs)?;
        let r = self.scalar(rhs)?;
        if matches!(self.kind(lhs.ty), TyKind::Ptr(..) | TyKind::Ref(..) | TyKind::FnPtr(..)) {
            if op == BinOp::Offset {
                let t = match self.kind(lhs.ty) {
                    TyKind::Ptr(_, t) | TyKind::Ref(_, t, _) => *t,
                    _ => return Err(ConstEvalError::InvalidMir("offset of function pointer")),
                };
                let n = if signed(self.kind(rhs.ty)) {
                    sext(bits(r)?, self.layout(rhs.ty)?.size as u8)
                } else {
                    i128::try_from(bits(r)?).map_err(|_| ConstEvalError::Ub("pointer offset overflow"))?
                };
                let delta = n.checked_mul(self.layout(t)?.size as i128).ok_or(ConstEvalError::Ub("pointer offset overflow"))?;
                if delta < i64::MIN as i128 || delta > i64::MAX as i128 {
                    return Err(ConstEvalError::Ub("pointer offset overflow"));
                }
                let result = match l {
                    Scalar::Ptr { provenance, offset } => {
                        let new = (offset as i128)
                            .checked_add(delta)
                            .filter(|n| *n >= 0 && *n <= u64::MAX as i128)
                            .ok_or(ConstEvalError::Ub("pointer offset overflow"))?;
                        self.access(l, 0, 1, false)?;
                        let p = Scalar::Ptr { provenance, offset: new as u64 };
                        self.access(p, 0, 1, false)?;
                        p
                    }
                    _ if delta == 0 => l,
                    _ => return Err(ConstEvalError::Ub("offset on a pointer without provenance")),
                };
                return Ok(Immediate::Scalar(result));
            }
            return Err(ConstEvalError::Unsupported("pointers cannot be reliably compared during const eval"));
        }
        let lb = bits(l)?;
        let rb = bits(r)?;
        if let TyKind::Float(p) = self.kind(lhs.ty) {
            return self.float_binary(op, lb, rb, *p);
        }
        let size = self.layout(lhs.ty)?.size as u8;
        let width = size as u32 * 8;
        let sign = signed(self.kind(lhs.ty));
        let a = sext(lb, size);
        let b = sext(rb, size);
        let ord = if sign { a.cmp(&b) } else { lb.cmp(&rb) };
        let bool_result = match op {
            BinOp::Eq => Some(lb == rb),
            BinOp::Ne => Some(lb != rb),
            BinOp::Lt => Some(ord.is_lt()),
            BinOp::Le => Some(!ord.is_gt()),
            BinOp::Gt => Some(ord.is_gt()),
            BinOp::Ge => Some(!ord.is_lt()),
            _ => None,
        };
        if let Some(v) = bool_result {
            return Ok(Immediate::Scalar(int(v as u128, 1)));
        }
        if op == BinOp::Cmp {
            return Ok(Immediate::Scalar(int(
                match ord {
                    std::cmp::Ordering::Less => u128::MAX,
                    std::cmp::Ordering::Equal => 0,
                    std::cmp::Ordering::Greater => 1,
                },
                self.layout(dest_ty)?.size as u8,
            )));
        }
        let (raw, host_overflow) = match op {
            BinOp::Add | BinOp::AddUnchecked | BinOp::AddWithOverflow => {
                if sign {
                    let (v, o) = a.overflowing_add(b);
                    (v as u128, o)
                } else {
                    lb.overflowing_add(rb)
                }
            }
            BinOp::Sub | BinOp::SubUnchecked | BinOp::SubWithOverflow => {
                if sign {
                    let (v, o) = a.overflowing_sub(b);
                    (v as u128, o)
                } else {
                    lb.overflowing_sub(rb)
                }
            }
            BinOp::Mul | BinOp::MulUnchecked | BinOp::MulWithOverflow => {
                if sign {
                    let (v, o) = a.overflowing_mul(b);
                    (v as u128, o)
                } else {
                    lb.overflowing_mul(rb)
                }
            }
            BinOp::Div | BinOp::Rem => {
                if rb == 0 {
                    return Err(ConstEvalError::Ub(if op == BinOp::Div {
                        "attempt to divide by zero"
                    } else {
                        "attempt to calculate the remainder with a divisor of zero"
                    }));
                }
                if sign {
                    if a == sext(1u128 << (width - 1), size) && b == -1 {
                        return Err(ConstEvalError::Ub("overflow in signed division or remainder"));
                    }
                    ((if op == BinOp::Div { a / b } else { a % b }) as u128, false)
                } else {
                    (if op == BinOp::Div { lb / rb } else { lb % rb }, false)
                }
            }
            BinOp::BitXor => (lb ^ rb, false),
            BinOp::BitAnd => (lb & rb, false),
            BinOp::BitOr => (lb | rb, false),
            BinOp::Shl | BinOp::ShlUnchecked | BinOp::Shr | BinOp::ShrUnchecked => {
                let shift = (rb % width as u128) as u32;
                let overflow = rb >= width as u128;
                if overflow && matches!(op, BinOp::ShlUnchecked | BinOp::ShrUnchecked) {
                    return Err(ConstEvalError::Ub("overflowing shift"));
                }
                let v = if matches!(op, BinOp::Shl | BinOp::ShlUnchecked) {
                    lb << shift
                } else if sign {
                    (a >> shift) as u128
                } else {
                    lb >> shift
                };
                return Ok(Immediate::Scalar(int(v, size)));
            }
            _ => return Err(ConstEvalError::InvalidMir("invalid integer operator")),
        };
        let value = raw & mask(size);
        let overflow = host_overflow || if sign { sext(value, size) != raw as i128 } else { raw != value };
        if overflow && matches!(op, BinOp::AddUnchecked | BinOp::SubUnchecked | BinOp::MulUnchecked) {
            return Err(ConstEvalError::Ub("overflow in unchecked arithmetic"));
        }
        let s = int(value, size);
        Ok(if matches!(op, BinOp::AddWithOverflow | BinOp::SubWithOverflow | BinOp::MulWithOverflow) {
            Immediate::ScalarPair(s, int(overflow as u128, 1))
        } else {
            Immediate::Scalar(s)
        })
    }
    pub(super) fn float_binary(&self, op: BinOp, lhs: u128, rhs: u128, p: Prim) -> Result<Immediate, ConstEvalError> {
        let l = if p == Prim::F32 { f32::from_bits(lhs as u32) as f64 } else { f64::from_bits(lhs as u64) };
        let r = if p == Prim::F32 { f32::from_bits(rhs as u32) as f64 } else { f64::from_bits(rhs as u64) };
        let b = match op {
            BinOp::Eq => Some(l == r),
            BinOp::Ne => Some(l != r),
            BinOp::Lt => Some(l < r),
            BinOp::Le => Some(l <= r),
            BinOp::Gt => Some(l > r),
            BinOp::Ge => Some(l >= r),
            _ => None,
        };
        if let Some(b) = b {
            return Ok(Immediate::Scalar(int(b as u128, 1)));
        }
        let s = if p == Prim::F32 {
            let l = l as f32;
            let r = r as f32;
            let v = match op {
                BinOp::Add => l + r,
                BinOp::Sub => l - r,
                BinOp::Mul => l * r,
                BinOp::Div => l / r,
                BinOp::Rem => l % r,
                _ => return Err(ConstEvalError::InvalidMir("invalid float operator")),
            };
            int(v.to_bits() as u128, 4)
        } else {
            let v = match op {
                BinOp::Add => l + r,
                BinOp::Sub => l - r,
                BinOp::Mul => l * r,
                BinOp::Div => l / r,
                BinOp::Rem => l % r,
                _ => return Err(ConstEvalError::InvalidMir("invalid float operator")),
            };
            int(v.to_bits() as u128, 8)
        };
        Ok(Immediate::Scalar(s))
    }
    /// Transmute is a byte copy, including padding and relocations, never a scalar conversion.
    /// rustc_const_eval/src/interpret/cast.rs:23, place.rs (copy_op_allow_transmute).
    pub(super) fn transmute(&mut self, dest: MPlace, value: Value) -> Result<(), ConstEvalError> {
        let src_layout = self.layout(value.ty)?;
        if src_layout.size != self.layout(dest.ty)?.size {
            return Err(ConstEvalError::Ub("transmuting between differently-sized types"));
        }
        if let OperandValue::Indirect(p) = value.value {
            self.copy_bytes(p.ptr, dest.ptr, src_layout.size as u64, p.align.min(dest.align), false)?;
        } else {
            let temp = self.allocate_place(value.ty, MemoryKind::Stack)?;
            self.write(temp, value)?;
            let result = self.copy_bytes(temp.ptr, dest.ptr, src_layout.size as u64, temp.align.min(dest.align), false);
            self.memory.allocations[ptr_parts(temp.ptr)?.0 .0 as usize].deallocated = true;
            result?;
        }
        self.retag_copy(MPlace { ty: value.ty, ..dest })?;
        self.retag_copy(dest)
    }
    /// rustc_const_eval/src/interpret/cast.rs:461: recurse through the one changing
    /// non-1-ZST field of a CoerceUnsized ADT; pointer pointees use lockstep tails.
    pub(super) fn unsize(&mut self, dest: MPlace, value: Value) -> Result<(), ConstEvalError> {
        if let (TyKind::Adt(source, _, _), TyKind::Adt(target, _, _)) = (self.kind(value.ty), self.kind(dest.ty)) {
            if source != target {
                return Err(ConstEvalError::InvalidMir("unsizing different ADTs"));
            }
            let p = match value.value {
                OperandValue::Indirect(p) => p,
                _ => return Err(ConstEvalError::InvalidMir("unsizing immediate ADT")),
            };
            let count = self.layout(value.ty)?.fields.len();
            let mut changed = false;
            for i in 0..count {
                let src = self.field(p, i as u32)?;
                let dst = self.field(dest, i as u32)?;
                let sl = self.layout(src.ty)?;
                let dl = self.layout(dst.ty)?;
                if sl.size == 0 && sl.align == 1 && dl.size == 0 && dl.align == 1 {
                    continue;
                }
                if src.ty == dst.ty {
                    self.write(dst, Value::indirect(src))?;
                } else {
                    if changed {
                        return Err(ConstEvalError::InvalidMir("more than one unsizing field"));
                    }
                    changed = true;
                    self.unsize(dst, Value::indirect(src))?;
                }
            }
            return Ok(());
        }
        let mut source = match self.kind(value.ty) {
            TyKind::Ref(_, t, _) | TyKind::Ptr(_, t) => *t,
            _ => return Err(ConstEvalError::InvalidMir("unsize of non-pointer")),
        };
        let mut target = match self.kind(dest.ty) {
            TyKind::Ref(_, t, _) | TyKind::Ptr(_, t) => *t,
            _ => return Err(ConstEvalError::InvalidMir("unsize to non-pointer")),
        };
        while let (TyKind::Adt(a, _, _), TyKind::Adt(b, _, _)) = (self.kind(source), self.kind(target)) {
            if a != b {
                return Err(ConstEvalError::InvalidMir("unsizing different pointee ADTs"));
            }
            let n = self.layout(source)?.fields.len();
            if n == 0 {
                break;
            }
            source = self.provider.field_ty(source, 0, n as u32 - 1)?;
            target = self.provider.field_ty(target, 0, n as u32 - 1)?;
        }
        let (ptr, old_meta) = match self.immediate(value)? {
            Immediate::Scalar(p) => (p, None),
            Immediate::ScalarPair(p, meta) => (p, Some(meta)),
            _ => return Err(ConstEvalError::Ub("uninitialized pointer")),
        };
        let meta = match (self.kind(source), self.kind(target)) {
            (TyKind::Array(_, n), TyKind::Slice(_)) => int(self.array_len(*n).ok_or(LayoutError::Unknown(source))? as u128, 8),
            (_, TyKind::Dyn(..)) if source == target => old_meta.ok_or(ConstEvalError::InvalidMir("missing vtable"))?,
            (_, TyKind::Dyn(..)) => self.provider.vtable(source, target, old_meta)?,
            _ => return Err(ConstEvalError::InvalidMir("invalid pointer unsizing")),
        };
        self.write(dest, Value::immediate(dest.ty, Immediate::ScalarPair(ptr, meta)))
    }
    pub(super) fn cast(&mut self, kind: CastKind, value: Value, ty: TyId, dest: MPlace) -> Result<(), ConstEvalError> {
        let dl = self.layout(ty)?;
        let sl = self.layout(value.ty)?;
        if kind == CastKind::Transmute {
            return self.transmute(dest, value);
        }
        if matches!(kind, CastKind::PointerCoercion(PointerCoercion::Unsize, _)) {
            return self.unsize(dest, value);
        }
        let v = match kind {
            CastKind::PointerCoercion(PointerCoercion::ReifyFnPointer, _) => {
                let (d, args) = match self.kind(value.ty) {
                    TyKind::FnDef(d, args, _) => self.provider.reify(*d, args)?,
                    _ => return Err(ConstEvalError::InvalidMir("reify of non-function")),
                };
                Immediate::Scalar(self.allocate(0, 1, MemoryKind::Function(d, args))?)
            }
            CastKind::PointerCoercion(PointerCoercion::ClosureFnPointer, _) => {
                let (d, args) = self.provider.closure_fn(value.ty)?;
                Immediate::Scalar(self.allocate(0, 1, MemoryKind::Function(d, args))?)
            }
            CastKind::PtrToPtr | CastKind::FnPtrToPtr | CastKind::PointerCoercion(_, _) => match self.immediate(value)? {
                Immediate::ScalarPair(p, _) if dl.size == 8 => Immediate::Scalar(p),
                v => v,
            },
            CastKind::PointerExposeProvenance => {
                let s = self.scalar(value)?;
                Immediate::Scalar(int(bits(s)?, dl.size as u8))
            }
            CastKind::PointerWithExposedProvenance => {
                let n = bits(self.scalar(value)?)?;
                Immediate::Scalar(int(if signed(self.kind(value.ty)) { sext(n, sl.size as u8) as u128 } else { n }, dl.size as u8))
            }
            CastKind::IntToInt | CastKind::IntToFloat => {
                let n = bits(self.scalar(value)?)?;
                let sign = signed(self.kind(value.ty));
                let v = sext(n, sl.size as u8);
                let result = if kind == CastKind::IntToInt {
                    int(if sign { v as u128 } else { n }, dl.size as u8)
                } else if dl.size == 4 {
                    int((if sign { v as f32 } else { n as f32 }).to_bits() as u128, 4)
                } else {
                    int((if sign { v as f64 } else { n as f64 }).to_bits() as u128, 8)
                };
                Immediate::Scalar(result)
            }
            CastKind::FloatToInt | CastKind::FloatToFloat => {
                let n = bits(self.scalar(value)?)?;
                let f = if sl.size == 4 { f32::from_bits(n as u32) as f64 } else { f64::from_bits(n as u64) };
                let result = if kind == CastKind::FloatToFloat {
                    if dl.size == 4 {
                        int((f as f32).to_bits() as u128, 4)
                    } else {
                        int(f.to_bits() as u128, 8)
                    }
                } else if signed(self.kind(ty)) {
                    let min = sext(1u128 << (dl.size * 8 - 1), dl.size as u8);
                    let max = !min;
                    int((f as i128).clamp(min, max) as u128, dl.size as u8)
                } else {
                    int((f as u128).min(mask(dl.size as u8)), dl.size as u8)
                };
                Immediate::Scalar(result)
            }
            CastKind::Transmute => unreachable!(),
        };
        self.write(dest, Value::immediate(ty, v))
    }
}
