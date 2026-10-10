//! rustc_const_eval/src/interpret/step.rs:40,80,495 and call.rs (stack frames).
//! Runtime-only statements are exhaustive; analysis-only constructs are malformed MIR.
use super::operand::Value;
use super::*;

impl<'a> Interpreter<'a> {
    pub(super) fn push_frame(&mut self, body: &'a Body, args: &[Value], destination: Option<MPlace>) -> Result<(), ConstEvalError> {
        #[cfg(test)]
        assert!(
            super::super::validate::validate(body, self.provider.tcx()).is_empty(),
            "invalid test MIR: {:?}",
            super::super::validate::validate(body, self.provider.tcx())
        );
        if !matches!(body.phase, MirPhase::Runtime(_)) {
            return Err(ConstEvalError::InvalidMir("CTFE requires runtime MIR"));
        }
        if self.frames.len() >= self.limits.call_depth {
            return Err(ConstEvalError::CallDepth);
        }
        if body.arg_count as usize != args.len() || body.local_decls.is_empty() {
            return Err(ConstEvalError::InvalidMir("argument count mismatch"));
        }
        let mut explicit_storage = vec![false; body.local_decls.len()];
        for block in &body.basic_blocks {
            for stmt in &block.statements {
                if let StatementKind::StorageLive(l) | StatementKind::StorageDead(l) = stmt.kind {
                    *explicit_storage.get_mut(l.0 as usize).ok_or(ConstEvalError::InvalidMir("invalid storage local"))? = true;
                }
            }
        }
        let mut locals = Vec::new();
        for (i, decl) in body.local_decls.iter().enumerate() {
            locals.push(if i <= args.len() || !explicit_storage[i] {
                Some(self.allocate_place(decl.ty, MemoryKind::Stack)?)
            } else {
                None
            });
        }
        for (i, arg) in args.iter().enumerate() {
            self.write(locals[i + 1].unwrap(), *arg)?;
        }
        self.frames.push(Frame { body, locals, block: 0, statement: 0, destination });
        Ok(())
    }
    pub(super) fn jump(&mut self, target: BasicBlock) {
        let frame = self.frames.last_mut().unwrap();
        frame.block = target.0 as usize;
        frame.statement = 0;
    }
    pub(super) fn return_frame(&mut self) -> Result<(), ConstEvalError> {
        let frame = self.frames.last().unwrap();
        let ret = frame.locals[0].ok_or(ConstEvalError::Ub("dead return local"))?;
        let destination = frame.destination.ok_or(ConstEvalError::Ub("returning from a diverging call"))?;
        self.write(destination, Value::indirect(ret))?;
        let frame = self.frames.pop().unwrap();
        for p in frame.locals.into_iter().flatten() {
            let (id, _) = ptr_parts(p.ptr)?;
            self.memory.allocations[id.0 as usize].deallocated = true;
        }
        Ok(())
    }
    pub(super) fn step(&mut self) -> Result<(), ConstEvalError> {
        self.tick()?;
        let frame = self.frames.last().ok_or(ConstEvalError::InvalidMir("empty interpreter stack"))?;
        let body = frame.body;
        let block = body.basic_blocks.get(frame.block).ok_or(ConstEvalError::InvalidMir("invalid basic block"))?;
        if let Some(statement) = block.statements.get(frame.statement) {
            self.frames.last_mut().unwrap().statement += 1;
            return self.statement(&statement.kind);
        }
        let term = &block.terminator.as_ref().ok_or(ConstEvalError::InvalidMir("missing terminator"))?.kind;
        match term {
            TerminatorKind::Goto { target } => self.jump(*target),
            TerminatorKind::SwitchInt { discr, targets } => {
                let v = self.operand(discr)?;
                let n = bits(self.scalar(v)?)?;
                let mut target = targets.otherwise;
                if targets.values.len() != targets.targets.len() {
                    return Err(ConstEvalError::InvalidMir("invalid switch targets"));
                }
                for i in 0..targets.values.len() {
                    if targets.values[i] == n {
                        target = targets.targets[i];
                        break;
                    }
                }
                self.jump(target);
            }
            TerminatorKind::Return => self.return_frame()?,
            TerminatorKind::Unreachable => return Err(ConstEvalError::Ub("entering unreachable code")),
            TerminatorKind::Drop { place, target, .. } => {
                let p = self.place(place)?;
                if self.provider.needs_drop(p.ty)? {
                    return Err(ConstEvalError::Unsupported("drop in const eval needs drop glue MIR, step M4"));
                }
                self.jump(*target);
            }
            TerminatorKind::Call { func, args, destination, target, .. } => {
                let f = self.operand(func)?;
                let dest = self.place(destination)?;
                let mut values = Vec::new();
                for arg in args {
                    values.push(self.operand(arg)?);
                }
                let (def, generic_args) = self.function(f)?;
                if let Some(intrinsic) = self.intrinsics.get(def) {
                    self.intrinsic(intrinsic, &generic_args, &values, dest)?;
                    self.jump(target.ok_or(ConstEvalError::Ub("returning from a diverging intrinsic"))?);
                } else {
                    if let Some(target) = target {
                        self.jump(*target);
                    }
                    let callee = self.provider.body(def, &generic_args).ok_or(ConstEvalError::MissingBody(def))?;
                    self.push_frame(callee, &values, target.map(|_| dest))?;
                }
            }
            TerminatorKind::TailCall { func, args, .. } => {
                let f = self.operand(func)?;
                let (def, generic_args) = self.function(f)?;
                let mut values = Vec::new();
                for arg in args {
                    values.push(self.operand(arg)?);
                }
                let dest = self.frames.last().unwrap().destination;
                let callee = self.provider.body(def, &generic_args).ok_or(ConstEvalError::MissingBody(def))?;
                // Arguments must be copied before killing caller storage, but a tail call
                // does not consume an extra recursion slot (rustc interpret/call.rs).
                let old = self.frames.len() - 1;
                self.frames[old].destination = None;
                let saved_limit = self.limits.call_depth;
                self.limits.call_depth = saved_limit.saturating_add(1);
                let pushed = self.push_frame(callee, &values, dest);
                self.limits.call_depth = saved_limit;
                pushed?;
                let frame = self.frames.remove(old);
                for p in frame.locals.into_iter().flatten() {
                    self.memory.allocations[ptr_parts(p.ptr)?.0 .0 as usize].deallocated = true;
                }
            }
            TerminatorKind::Assert { cond, expected, msg, target, .. } => {
                let v = self.operand(cond)?;
                let b = bits(self.scalar(v)?)?;
                if b > 1 {
                    return Err(ConstEvalError::Ub("invalid boolean value"));
                }
                if (b != 0) != *expected {
                    return Err(ConstEvalError::Panic(self.assert_message(msg)?));
                }
                self.jump(*target);
            }
            TerminatorKind::InlineAsm(_) => {
                return Err(ConstEvalError::Unsupported("inline assembly is not supported in constant evaluation"))
            }
            TerminatorKind::UnwindResume | TerminatorKind::UnwindTerminate(_) => {
                return Err(ConstEvalError::Ub("unwinding in constant evaluation"))
            }
            TerminatorKind::Yield { .. }
            | TerminatorKind::CoroutineDrop
            | TerminatorKind::FalseEdge { .. }
            | TerminatorKind::FalseUnwind { .. } => return Err(ConstEvalError::InvalidMir("non-runtime terminator in CTFE")),
        }
        Ok(())
    }
    pub(super) fn function(&self, value: Value) -> Result<(DefId, Vec<TyId>), ConstEvalError> {
        if let TyKind::FnDef(d, args, _) = self.kind(value.ty) {
            return Ok((*d, args.clone()));
        }
        let (id, offset) = ptr_parts(self.scalar(value)?)?;
        if offset == 0 {
            if let Some(MemoryKind::Function(d, args)) = self.kinds.get(id.0 as usize) {
                return Ok((*d, args.clone()));
            }
        }
        Err(ConstEvalError::Ub("invalid function pointer"))
    }
    pub(super) fn statement(&mut self, stmt: &StatementKind) -> Result<(), ConstEvalError> {
        match stmt {
            StatementKind::Assign(dest, value) => {
                let dest = self.place(dest)?;
                self.rvalue(value, dest)?;
            }
            StatementKind::SetDiscriminant { place, variant_index } => {
                let p = self.place(place)?;
                self.set_discriminant(p, variant_index.0)?;
            }
            StatementKind::StorageLive(l) => {
                let frame = self.frames.last().unwrap();
                let decl = frame.body.local_decls.get(l.0 as usize).ok_or(ConstEvalError::InvalidMir("invalid local"))?;
                let ty = decl.ty;
                if let Some(p) = frame.locals[l.0 as usize] {
                    self.memory.allocations[ptr_parts(p.ptr)?.0 .0 as usize].deallocated = true;
                }
                let p = self.allocate_place(ty, MemoryKind::Stack)?;
                self.frames.last_mut().unwrap().locals[l.0 as usize] = Some(p);
            }
            StatementKind::StorageDead(l) => {
                let p =
                    self.frames.last_mut().unwrap().locals.get_mut(l.0 as usize).ok_or(ConstEvalError::InvalidMir("invalid local"))?.take();
                if let Some(p) = p {
                    self.memory.allocations[ptr_parts(p.ptr)?.0 .0 as usize].deallocated = true;
                }
            }
            StatementKind::Intrinsic(NonDivergingIntrinsic::Assume(op)) => {
                let v = self.operand(op)?;
                if bits(self.scalar(v)?)? != 1 {
                    return Err(ConstEvalError::Ub("assume called with false"));
                }
            }
            StatementKind::Intrinsic(NonDivergingIntrinsic::CopyNonOverlapping { src, dst, count }) => {
                let s = self.operand(src)?;
                let d = self.operand(dst)?;
                let n = self.operand(count)?;
                self.copy_intrinsic(s, d, n, true)?;
            }
            StatementKind::Nop | StatementKind::ConstEvalCounter => {}
            StatementKind::PlaceMention(p) => {
                self.place(p)?;
            }
            StatementKind::FakeRead(..) | StatementKind::AscribeUserType(..) => {
                return Err(ConstEvalError::InvalidMir("analysis statement in runtime MIR"))
            }
        }
        Ok(())
    }
    pub(super) fn rvalue(&mut self, rv: &Rvalue, dest: MPlace) -> Result<(), ConstEvalError> {
        let dl = self.layout(dest.ty)?;
        let immediate = match rv {
            Rvalue::Use(op) => {
                let v = self.operand(op)?;
                return self.write(dest, v);
            }
            Rvalue::CopyForDeref(p) => {
                let p = self.place(p)?;
                return self.write(dest, Value::indirect(p));
            }
            Rvalue::Repeat(op, count) => {
                let v = self.operand(op)?;
                let n = self.constant(count)?;
                let n = bits(self.scalar(n)?)?;
                if n != self.len(dest)? as u128 {
                    return Err(ConstEvalError::InvalidMir("repeat length mismatch"));
                }
                for i in 0..n as u64 {
                    self.tick()?;
                    self.write(self.index(dest, i)?, v)?;
                }
                return Ok(());
            }
            Rvalue::Ref(_, borrow, p) => {
                if matches!(borrow, BorrowKind::Fake(_)) {
                    return Err(ConstEvalError::InvalidMir("fake borrow in runtime MIR"));
                }
                let p = self.place(p)?;
                let l = self.layout(p.ty)?;
                self.access(p.ptr, l.size as u64, l.align as u64, false)?;
                match p.meta {
                    Some(meta) => Immediate::ScalarPair(p.ptr, meta),
                    None => Immediate::Scalar(p.ptr),
                }
            }
            Rvalue::RawPtr(_, p) => {
                let p = self.place(p)?;
                match p.meta {
                    Some(meta) => Immediate::ScalarPair(p.ptr, meta),
                    None => Immediate::Scalar(p.ptr),
                }
            }
            Rvalue::Len(p) => {
                let p = self.place(p)?;
                Immediate::Scalar(int(self.len(p)? as u128, dl.size as u8))
            }
            Rvalue::Cast(k, op, ty) => {
                let v = self.operand(op)?;
                return self.cast(*k, v, *ty, dest);
            }
            Rvalue::BinaryOp(op, operands) => {
                let l = self.operand(&operands.0)?;
                let r = self.operand(&operands.1)?;
                self.binary(*op, l, r, dest.ty)?
            }
            Rvalue::UnaryOp(op, operand) => {
                let v = self.operand(operand)?;
                if *op == UnOp::PtrMetadata {
                    match self.immediate(v)? {
                        Immediate::ScalarPair(_, meta) => Immediate::Scalar(meta),
                        Immediate::Scalar(_) => Immediate::Uninit,
                        _ => return Err(ConstEvalError::Ub("uninitialized pointer")),
                    }
                } else {
                    let s = bits(self.scalar(v)?)?;
                    let n = match op {
                        UnOp::Not if matches!(self.kind(v.ty), TyKind::Bool) => s ^ 1,
                        UnOp::Not => !s,
                        UnOp::Neg if matches!(self.kind(v.ty), TyKind::Float(_)) => s ^ (1 << (dl.size * 8 - 1)),
                        UnOp::Neg => 0u128.wrapping_sub(s),
                        UnOp::PtrMetadata => unreachable!(),
                    };
                    Immediate::Scalar(int(n, dl.size as u8))
                }
            }
            Rvalue::NullaryOp(op, ty) => {
                let n = match op {
                    NullOp::SizeOf => self.layout(*ty)?.size as u64,
                    NullOp::AlignOf => self.layout(*ty)?.align as u64,
                    NullOp::UbChecks => 0,
                    NullOp::ContractChecks => 0,
                    NullOp::OffsetOf(fields) => {
                        let mut ty = *ty;
                        let mut offset = 0u64;
                        for &(v, f) in fields {
                            let l = self.layout(ty)?;
                            let offsets = l.variant_fields.get(v.0 as usize).unwrap_or(&l.fields);
                            offset += *offsets.get(f.0 as usize).ok_or(ConstEvalError::InvalidMir("invalid offset_of field"))? as u64;
                            ty = self.provider.field_ty(ty, v.0, f.0)?;
                        }
                        offset
                    }
                };
                Immediate::Scalar(int(n as u128, dl.size as u8))
            }
            Rvalue::Discriminant(p) => {
                let p = self.place(p)?;
                Immediate::Scalar(int(self.discriminant(p.ty, self.read_discriminant(p)?)?, dl.size as u8))
            }
            Rvalue::Aggregate(kind, ops) => {
                let mut values = Vec::new();
                for op in ops {
                    values.push(self.operand(op)?);
                }
                let mut aggregate = dest;
                let mut active = None;
                if let AggregateKind::Adt(_, v, _, _, field) = **kind {
                    aggregate.variant = Some(v.0);
                    active = field;
                }
                for (i, v) in values.into_iter().enumerate() {
                    let p = match **kind {
                        AggregateKind::Array(_) => self.index(dest, i as u64)?,
                        AggregateKind::RawPtr(..) => {
                            if self.layout(v.ty)?.size == 0 {
                                continue;
                            }
                            self.write_scalar(add_offset(dest.ptr, i as u64 * 8)?, self.scalar(v)?, 8, dest.align.min(8))?;
                            continue;
                        }
                        _ => self.field(aggregate, active.map_or(i as u32, |f| f.0))?,
                    };
                    self.write(p, v)?;
                }
                if let AggregateKind::Adt(_, v, ..) = **kind {
                    self.set_discriminant(dest, v.0)?;
                }
                return Ok(());
            }
            Rvalue::ThreadLocalRef(_) => {
                return Err(ConstEvalError::Unsupported("cannot access thread-local storage in constant evaluation"))
            }
            Rvalue::ShallowInitBox(op, _) => {
                let v = self.operand(op)?;
                Immediate::Scalar(self.scalar(v)?)
            }
        };
        self.write(dest, Value::immediate(dest.ty, immediate))
    }
    pub(super) fn operand_text(&mut self, op: &Operand) -> Result<String, ConstEvalError> {
        let v = self.operand(op)?;
        let s = bits(self.scalar(v)?)?;
        Ok(if signed(self.kind(v.ty)) { sext(s, self.layout(v.ty)?.size as u8).to_string() } else { s.to_string() })
    }
    /// rustc_middle/src/mir/terminator.rs:345 (AssertMessage formatting).
    pub(super) fn assert_message(&mut self, msg: &AssertKind) -> Result<String, ConstEvalError> {
        Ok(match msg {
            AssertKind::BoundsCheck { len, index } => {
                format!("index out of bounds: the length is {} but the index is {}", self.operand_text(len)?, self.operand_text(index)?)
            }
            AssertKind::Overflow(op, a, b) => {
                let a = self.operand_text(a)?;
                let b = self.operand_text(b)?;
                match op {
                    BinOp::Shl | BinOp::Shr => {
                        format!("attempt to shift {} by `{b}`, which would overflow", if *op == BinOp::Shl { "left" } else { "right" })
                    }
                    _ => format!(
                        "attempt to compute `{a} {} {b}`, which would overflow",
                        match op {
                            BinOp::Add => "+",
                            BinOp::Sub => "-",
                            BinOp::Mul => "*",
                            BinOp::Div => "/",
                            BinOp::Rem => "%",
                            _ => return Err(ConstEvalError::InvalidMir("invalid overflow assertion")),
                        }
                    ),
                }
            }
            AssertKind::OverflowNeg(v) => format!("attempt to negate `{}`, which would overflow", self.operand_text(v)?),
            AssertKind::DivisionByZero(v) => format!("attempt to divide `{}` by zero", self.operand_text(v)?),
            AssertKind::RemainderByZero(v) => {
                format!("attempt to calculate the remainder of `{}` with a divisor of zero", self.operand_text(v)?)
            }
            AssertKind::MisalignedPointerDereference { required, found } => format!(
                "misaligned pointer dereference: address must be a multiple of {} but is {}",
                self.operand_text(required)?,
                self.operand_text(found)?
            ),
            AssertKind::NullPointerDereference => "null pointer dereference occurred".into(),
            AssertKind::ResumedAfterReturn(_) => "coroutine resumed after completion".into(),
            AssertKind::ResumedAfterPanic(_) => "coroutine resumed after panicking".into(),
        })
    }
}
