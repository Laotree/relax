//! rustc_const_eval/src/interpret/place.rs (MemPlace/PlaceTy, projection and writes),
//! discriminant.rs:19,52. Packed projections lower the guaranteed alignment.
use super::*;

#[derive(Clone, Copy, Debug)]
pub struct MPlace {
    pub ptr: Scalar,
    pub ty: TyId,
    pub meta: Option<Scalar>,
    pub variant: Option<u32>,
    pub align: u64,
}

impl Interpreter<'_> {
    pub(super) fn local(&self, local: Local) -> Result<MPlace, ConstEvalError> {
        self.frames
            .last()
            .and_then(|f| f.locals.get(local.0 as usize))
            .copied()
            .flatten()
            .ok_or(ConstEvalError::Ub("accessing a dead local"))
    }
    pub(super) fn project(&self, base: MPlace, offset: u64, ty: TyId) -> Result<MPlace, ConstEvalError> {
        let align = self.layout(ty)?.align as u64;
        let offset_align = if offset == 0 { base.align } else { 1u64 << offset.trailing_zeros() };
        Ok(MPlace { ptr: add_offset(base.ptr, offset)?, ty, meta: None, variant: None, align: align.min(base.align).min(offset_align) })
    }
    pub(super) fn field(&self, base: MPlace, index: u32) -> Result<MPlace, ConstEvalError> {
        let l = self.layout(base.ty)?;
        let offsets = if let Some(v) = base.variant { l.variant_fields.get(v as usize).unwrap_or(&l.fields) } else { &l.fields };
        let offset = *offsets.get(index as usize).ok_or(ConstEvalError::InvalidMir("field index out of range"))?;
        let ty = self.provider.field_ty(base.ty, base.variant.unwrap_or(0), index)?;
        let mut p = self.project(base, offset as u64, ty)?;
        if self.provider.is_unsized(ty)? {
            p.meta = base.meta;
        }
        Ok(p)
    }
    pub(super) fn len(&self, place: MPlace) -> Result<u64, ConstEvalError> {
        match self.kind(place.ty) {
            TyKind::Array(_, n) => self.array_len(*n).ok_or(ConstEvalError::Layout(LayoutError::Unknown(place.ty))),
            TyKind::Slice(_) | TyKind::Str => Ok(bits(place.meta.ok_or(ConstEvalError::InvalidMir("missing slice metadata"))?)? as u64),
            _ => Err(ConstEvalError::InvalidMir("length of non-array")),
        }
    }
    pub(super) fn index(&self, place: MPlace, index: u64) -> Result<MPlace, ConstEvalError> {
        let n = self.len(place)?;
        if index >= n {
            return Err(ConstEvalError::Ub("out-of-bounds array index"));
        }
        let ty = match self.kind(place.ty) {
            TyKind::Array(t, _) | TyKind::Slice(t) => *t,
            TyKind::Str => self.provider.tcx().tys.u8_,
            _ => unreachable!(),
        };
        let offset = index.checked_mul(self.layout(ty)?.size as u64).ok_or(ConstEvalError::Ub("array offset overflow"))?;
        self.project(place, offset, ty)
    }
    pub(super) fn deref(&self, value: operand::Value) -> Result<MPlace, ConstEvalError> {
        let ty = match self.kind(value.ty) {
            TyKind::Ref(_, t, _) | TyKind::Ptr(_, t) => *t,
            _ => return Err(ConstEvalError::InvalidMir("dereference of non-pointer")),
        };
        let (ptr, meta) = match self.immediate(value)? {
            Immediate::Scalar(p) => (p, None),
            Immediate::ScalarPair(p, m) => (p, Some(m)),
            Immediate::Uninit => return Err(ConstEvalError::Ub("using uninitialized data")),
        };
        let l = self.layout(ty)?;
        Ok(MPlace { ptr, ty, meta, variant: None, align: l.align as u64 })
    }
    pub(super) fn place(&mut self, place: &Place) -> Result<MPlace, ConstEvalError> {
        let mut p = self.local(place.local)?;
        for elem in &place.projection {
            p = match *elem {
                PlaceElem::Deref => self.deref(operand::Value::indirect(p))?,
                PlaceElem::Field(f, ty) => {
                    let p = self.field(p, f.0)?;
                    if p.ty != ty {
                        return Err(ConstEvalError::InvalidMir("field projection type mismatch"));
                    }
                    p
                }
                PlaceElem::Index(i) => {
                    let n = bits(self.scalar(operand::Value::indirect(self.local(i)?))?)? as u64;
                    self.index(p, n)?
                }
                PlaceElem::ConstantIndex { offset, min_length, from_end } => {
                    let n = self.len(p)?;
                    if n < min_length {
                        return Err(ConstEvalError::Ub("constant index minimum length violated"));
                    }
                    self.index(
                        p,
                        if from_end { n.checked_sub(offset).ok_or(ConstEvalError::Ub("out-of-bounds array index"))? } else { offset },
                    )?
                }
                PlaceElem::Subslice { from, to, from_end } => {
                    let len = self.len(p)?;
                    let end = if from_end { len.checked_sub(to) } else { Some(to) }.ok_or(ConstEvalError::Ub("out-of-bounds subslice"))?;
                    if from > end || end > len {
                        return Err(ConstEvalError::Ub("out-of-bounds subslice"));
                    }
                    let (elem, array) = match self.kind(p.ty) {
                        TyKind::Array(t, _) => (*t, true),
                        TyKind::Slice(t) => (*t, false),
                        _ => return Err(ConstEvalError::InvalidMir("subslice of non-array")),
                    };
                    let stride = self.layout(elem)?.size as u64;
                    let ty = self.provider.tcx().tys.intern(if array { TyKind::Array(elem, end - from) } else { TyKind::Slice(elem) });
                    MPlace {
                        ptr: add_offset(p.ptr, from.checked_mul(stride).ok_or(ConstEvalError::Ub("offset overflow"))?)?,
                        ty,
                        meta: if array { None } else { Some(int((end - from) as u128, 8)) },
                        ..p
                    }
                }
                PlaceElem::Downcast(_, v) => {
                    p.variant = Some(v.0);
                    p
                }
                PlaceElem::OpaqueCast(t) | PlaceElem::Subtype(t) => {
                    p.ty = t;
                    p
                }
            };
        }
        Ok(p)
    }
    pub(super) fn variant_count(&self, ty: TyId) -> Result<u32, ConstEvalError> {
        if let TyKind::Adt(d, _, _) = self.kind(ty) {
            let a = self.provider.tcx().adts.get(d).ok_or(ConstEvalError::Layout(LayoutError::Unknown(ty)))?;
            Ok(a.variants.len() as u32)
        } else {
            Ok(1)
        }
    }
    pub(super) fn discriminant(&self, ty: TyId, variant: u32) -> Result<u128, ConstEvalError> {
        if let TyKind::Adt(d, _, _) = self.kind(ty) {
            let a = self.provider.tcx().adts.get(d).ok_or(ConstEvalError::Layout(LayoutError::Unknown(ty)))?;
            Ok(a.variants.get(variant as usize).ok_or(ConstEvalError::InvalidMir("bad variant"))?.disc as u128)
        } else {
            Ok(0)
        }
    }
    pub(super) fn read_discriminant(&self, p: MPlace) -> Result<u32, ConstEvalError> {
        let l = self.layout(p.ty)?;
        if l.uninhabited {
            return Err(ConstEvalError::Ub("reading an uninhabited enum"));
        }
        if let TagEnc::Single(v) = l.enc {
            return Ok(v);
        }
        let Some((off, mem)) = l.tag else {
            return Ok(0);
        };
        let size = mem_size(mem) as u64;
        let tag = self.read_scalar(add_offset(p.ptr, off as u64)?, size, 1)?;
        match l.enc {
            TagEnc::Niche { untagged, lo, hi, start } => {
                let value = match tag {
                    Scalar::Ptr { provenance, offset } if start == 0 && lo == hi => {
                        let a = self.memory.get(provenance.alloc).ok_or(ConstEvalError::Ub("invalid enum tag"))?;
                        if a.deallocated || offset > a.bytes.len() as u64 {
                            return Err(ConstEvalError::Ub("invalid enum tag"));
                        }
                        return Ok(untagged);
                    }
                    _ => bits(tag)?,
                };
                let v = value.wrapping_sub(start) & mask(size as u8);
                if v <= (hi - lo) as u128 && lo + v as u32 == untagged {
                    return Err(ConstEvalError::Ub("invalid enum tag"));
                }
                Ok(if v <= (hi - lo) as u128 { lo + v as u32 } else { untagged })
            }
            TagEnc::Direct => {
                let value = bits(tag)?;
                for v in 0..self.variant_count(p.ty)? {
                    if self.discriminant(p.ty, v)? & mask(size as u8) == value {
                        return Ok(v);
                    }
                }
                Err(ConstEvalError::Ub("invalid enum tag"))
            }
            TagEnc::Single(v) => Ok(v),
        }
    }
    pub(super) fn set_discriminant(&mut self, p: MPlace, v: u32) -> Result<(), ConstEvalError> {
        let l = self.layout(p.ty)?;
        if v >= self.variant_count(p.ty)? || l.uninhabited {
            return Err(ConstEvalError::Ub("writing an invalid enum variant"));
        }
        let value = match l.enc {
            TagEnc::Direct => self.discriminant(p.ty, v)?,
            TagEnc::Niche { untagged, lo, hi, start } => {
                if v == untagged {
                    if self.read_discriminant(p)? != v {
                        return Err(ConstEvalError::Ub("invalid niche for untagged variant"));
                    }
                    return Ok(());
                }
                if v < lo || v > hi {
                    return Err(ConstEvalError::Ub("invalid niche variant"));
                }
                start.wrapping_add((v - lo) as u128)
            }
            TagEnc::Single(single) => {
                if single != v {
                    return Err(ConstEvalError::Ub("invalid single variant"));
                }
                return Ok(());
            }
        };
        if let Some((off, mem)) = l.tag {
            let size = mem_size(mem) as u64;
            self.write_scalar(add_offset(p.ptr, off as u64)?, int(value, size as u8), size, 1)?;
        }
        Ok(())
    }
    /// Validate typed fields, not padding; references recursively validate their referents.
    /// rustc_const_eval/src/interpret/validity.rs (validate_operand, visit_value).
    pub(super) fn validate_value(&self, p: MPlace, seen: &mut Vec<(Scalar, TyId, bool)>) -> Result<(), ConstEvalError> {
        self.validate_inner(p, seen, false)
    }
    fn validate_inner(&self, p: MPlace, seen: &mut Vec<(Scalar, TyId, bool)>, behind_reference: bool) -> Result<(), ConstEvalError> {
        if seen.contains(&(p.ptr, p.ty, behind_reference)) {
            return Ok(());
        }
        seen.push((p.ptr, p.ty, behind_reference));
        let l = self.layout(p.ty)?;
        if l.uninhabited {
            return Err(ConstEvalError::Ub("uninhabited value"));
        }
        // Check the active value, not is_freeze on the whole enclosing enum:
        // &None::<UnsafeCell<T>> contains no UnsafeCell. Owned cells at the root
        // are allowed. rustc_const_eval/src/interpret/validity.rs:1319,1370.
        if behind_reference && l.size != 0 {
            if let TyKind::Adt(d, _, _) = self.kind(p.ty) {
                let is_union = self.provider.tcx().adts[d].is_union;
                if self.provider.is_unsafe_cell(p.ty)? || (is_union && !self.provider.is_freeze(p.ty)?) {
                    return Err(ConstEvalError::Ub("UnsafeCell in read-only memory"));
                }
            }
        }
        if let Some(niche) = l.niche {
            let tag = self.read_scalar(add_offset(p.ptr, niche.off as u64)?, niche.bytes as u64, 1)?;
            match tag {
                Scalar::Int { bits, .. } => {
                    let valid = if niche.start <= niche.end {
                        bits >= niche.start && bits <= niche.end
                    } else {
                        bits >= niche.start || bits <= niche.end
                    };
                    if !valid {
                        return Err(ConstEvalError::Ub("value outside scalar valid range"));
                    }
                }
                Scalar::Ptr { .. } if niche.start == 1 && niche.end == mask(niche.bytes as u8) => {}
                Scalar::Ptr { .. } => return Err(ConstEvalError::Unsupported("pointer in scalar with restricted valid range")),
            }
        }
        match self.kind(p.ty) {
            TyKind::Ref(mutable, _, _) => {
                if *mutable {
                    return Err(ConstEvalError::MutableReference);
                }
                let referent = self.deref(operand::Value::indirect(p))?;
                let rl = self.layout(referent.ty)?;
                let size = match self.kind(referent.ty) {
                    TyKind::Slice(t) => {
                        self.len(referent)?.checked_mul(self.layout(*t)?.size as u64).ok_or(ConstEvalError::Ub("slice size overflow"))?
                    }
                    TyKind::Str => self.len(referent)?,
                    _ => rl.size as u64,
                };
                self.access(referent.ptr, size, rl.align as u64, false)?;
                self.validate_inner(referent, seen, true)?;
            }
            TyKind::Array(_, _) | TyKind::Slice(_) => {
                for i in 0..self.len(p)? {
                    self.validate_inner(self.index(p, i)?, seen, behind_reference)?;
                }
            }
            TyKind::Str => {
                let n = self.len(p)?;
                if let Some((id, off)) = self.access(p.ptr, n, 1, false)? {
                    let a = &self.memory.allocations[id.0 as usize];
                    if a.init_mask[off..off + n as usize].contains(&false) {
                        return Err(ConstEvalError::Ub("using uninitialized data"));
                    }
                    std::str::from_utf8(&a.bytes[off..off + n as usize]).map_err(|_| ConstEvalError::Ub("invalid UTF-8 in str"))?;
                }
            }
            TyKind::Tuple(_) | TyKind::Adt(..) | TyKind::Closure(..) => {
                if let TyKind::Adt(d, _, _) = self.kind(p.ty) {
                    if self.provider.tcx().adts[d].is_union {
                        return Ok(());
                    }
                }
                let v = self.read_discriminant(p)?;
                let p = MPlace { variant: Some(v), ..p };
                let n = l.variant_fields.get(v as usize).unwrap_or(&l.fields).len();
                for i in 0..n {
                    self.validate_inner(self.field(p, i as u32)?, seen, behind_reference)?;
                }
            }
            TyKind::FnDef(..) => {}
            _ => {
                self.immediate(operand::Value::indirect(p))?;
            }
        }
        Ok(())
    }
}
