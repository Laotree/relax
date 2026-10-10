//! rustc_const_eval/src/interpret/memory.rs:335,498 and
//! rustc_middle/src/mir/interpret/allocation.rs:95. Relax's targets have 8-byte pointers.
use super::*;

fn byte_provenance(a: &Allocation, offset: u64) -> Option<(CtfeProvenance, u8)> {
    for &(start, id) in &a.provenance {
        if offset >= start && offset - start < 8 {
            return Some((id, (offset - start) as u8));
        }
    }
    for &(at, id, byte) in &a.provenance_fragments {
        if at == offset {
            return Some((id, byte));
        }
    }
    None
}
fn clear_provenance(a: &mut Allocation, start: u64, end: u64) {
    a.provenance_fragments.retain(|&(at, _, _)| at < start || at >= end);
    let mut i = 0;
    while i < a.provenance.len() {
        let (at, id) = a.provenance[i];
        if at < end && at + 8 > start {
            a.provenance.swap_remove(i);
            for byte in 0..8 {
                if at + byte < start || at + byte >= end {
                    a.provenance_fragments.push((at + byte, id, byte as u8));
                }
            }
        } else {
            i += 1;
        }
    }
}
impl Interpreter<'_> {
    pub(super) fn allocate(&mut self, size: u64, align: u64, kind: MemoryKind) -> Result<Scalar, ConstEvalError> {
        if !align.is_power_of_two() {
            return Err(ConstEvalError::Ub("allocation alignment is not a power of two"));
        }
        let len = usize::try_from(size).map_err(|_| ConstEvalError::Ub("allocation is too large"))?;
        if size > isize::MAX as u64 {
            return Err(ConstEvalError::Ub("allocation is too large"));
        }
        let mut bytes = Vec::new();
        bytes.try_reserve_exact(len).map_err(|_| ConstEvalError::Ub("allocation is too large"))?;
        bytes.resize(len, 0);
        let id = self.memory.insert(Allocation {
            bytes,
            align,
            init_mask: vec![false; len],
            deallocated: false,
            provenance: Vec::new(),
            provenance_fragments: Vec::new(),
            mutability: Mutability::Mut,
        });
        if let MemoryKind::Function(def, args) = &kind {
            self.memory.functions.push((id, *def, args.clone()));
        }
        self.kinds.push(kind);
        Ok(Scalar::Ptr { provenance: CtfeProvenance::new(id), offset: 0 })
    }
    pub(super) fn access(&self, ptr: Scalar, size: u64, align: u64, write: bool) -> Result<Option<(AllocId, usize)>, ConstEvalError> {
        if !align.is_power_of_two() {
            return Err(ConstEvalError::InvalidMir("invalid access alignment"));
        }
        let (id, off) = match ptr {
            Scalar::Ptr { provenance, offset } => (provenance.alloc, offset),
            Scalar::Int { bits, .. } if size == 0 && bits != 0 && bits % align as u128 == 0 => return Ok(None),
            _ => return Err(ConstEvalError::Ub("dangling or null pointer")),
        };
        let a = self.memory.get(id).ok_or(ConstEvalError::Ub("dangling pointer"))?;
        if a.deallocated {
            return Err(ConstEvalError::Ub("pointer to deallocated allocation"));
        }
        if a.init_mask.len() != a.bytes.len() {
            return Err(ConstEvalError::InvalidMir("allocation initialization mask size mismatch"));
        }
        if size != 0 && a.mutability == Mutability::Mut && matches!(self.kinds[id.0 as usize], MemoryKind::Global) {
            return Err(ConstEvalError::Ub("constant accesses mutable global memory"));
        }
        if matches!(self.kinds[id.0 as usize], MemoryKind::Function(..)) {
            return Err(ConstEvalError::Ub("function pointer used as data"));
        }
        if a.align < align || off % align != 0 {
            return Err(ConstEvalError::Ub("accessing memory with insufficient alignment"));
        }
        if off > a.bytes.len() as u64 || size > a.bytes.len() as u64 - off {
            return Err(ConstEvalError::Ub("out-of-bounds pointer use"));
        }
        if write && size != 0 && a.mutability == Mutability::Not {
            return Err(ConstEvalError::Ub("writing to read-only memory"));
        }
        // rustc_const_eval/src/const_eval/machine.rs:894: permissions belong to
        // this pointer; an owner pointer to the same allocation can still write.
        if write && size != 0 && matches!(ptr, Scalar::Ptr { provenance, .. } if provenance.immutable()) {
            return Err(ConstEvalError::Ub("writing through an immutable pointer"));
        }
        Ok(Some((id, off as usize)))
    }
    pub(super) fn read_scalar(&self, ptr: Scalar, size: u64, align: u64) -> Result<Scalar, ConstEvalError> {
        if size == 0 || size > 16 {
            return Err(ConstEvalError::InvalidMir("invalid scalar size"));
        }
        let (id, off) = self.access(ptr, size, align, false)?.ok_or(ConstEvalError::Ub("dangling pointer"))?;
        let a = &self.memory.allocations[id.0 as usize];
        let mut value = 0;
        let mut prov = None;
        for i in 0..size as usize {
            if !a.init_mask[off + i] {
                return Err(ConstEvalError::Ub("using uninitialized data"));
            }
            value |= (a.bytes[off + i] as u128) << (i * 8);
            if let Some((p, byte)) = byte_provenance(a, (off + i) as u64) {
                if size != 8 || byte != i as u8 || (i != 0 && prov != Some(p)) {
                    return Err(ConstEvalError::Unsupported("reading a partial pointer"));
                }
                prov = Some(p);
            } else if prov.is_some() {
                return Err(ConstEvalError::Unsupported("reading a partial pointer"));
            }
        }
        Ok(match prov {
            Some(provenance) => Scalar::Ptr { provenance, offset: value as u64 },
            None => int(value, size as u8),
        })
    }
    pub(super) fn write_scalar(&mut self, ptr: Scalar, value: Scalar, size: u64, align: u64) -> Result<(), ConstEvalError> {
        if size == 0 || size > 16 {
            return Err(ConstEvalError::InvalidMir("invalid scalar size"));
        }
        let (value_bits, provenance) = match value {
            Scalar::Int { bits, size: n } if n as u64 == size => (bits, None),
            Scalar::Ptr { provenance, offset } if size == 8 => (offset as u128, Some(provenance)),
            _ => return Err(ConstEvalError::InvalidMir("scalar size mismatch")),
        };
        let (id, off) = self.access(ptr, size, align, true)?.ok_or(ConstEvalError::Ub("dangling pointer"))?;
        let a = &mut self.memory.allocations[id.0 as usize];
        clear_provenance(a, off as u64, off as u64 + size);
        for i in 0..size as usize {
            a.bytes[off + i] = (value_bits >> (i * 8)) as u8;
            a.init_mask[off + i] = true;
        }
        if let Some(p) = provenance {
            a.provenance.push((off as u64, p));
        }
        Ok(())
    }
    pub(super) fn copy_bytes(&mut self, src: Scalar, dst: Scalar, size: u64, align: u64, nonoverlap: bool) -> Result<(), ConstEvalError> {
        let s = self.access(src, size, align, false)?;
        let d = self.access(dst, size, align, true)?;
        if size == 0 {
            return Ok(());
        }
        let (sid, so) = s.unwrap();
        let (did, doff) = d.unwrap();
        let n = size as usize;
        if nonoverlap && sid == did && so < doff + n && doff < so + n {
            return Err(ConstEvalError::Ub("copy_nonoverlapping called on overlapping ranges"));
        }
        let source = &self.memory.allocations[sid.0 as usize];
        let bytes = source.bytes[so..so + n].to_vec();
        let init = source.init_mask[so..so + n].to_vec();
        let mut provenance = Vec::new();
        for i in 0..n {
            if let Some((p, byte)) = byte_provenance(source, (so + i) as u64) {
                provenance.push(((doff + i) as u64, p, byte));
            }
        }
        let dest = &mut self.memory.allocations[did.0 as usize];
        clear_provenance(dest, doff as u64, doff as u64 + size);
        dest.bytes[doff..doff + n].copy_from_slice(&bytes);
        dest.init_mask[doff..doff + n].copy_from_slice(&init);
        dest.provenance_fragments.extend(provenance);
        Ok(())
    }
    pub(super) fn uninit(&mut self, ptr: Scalar, size: u64) -> Result<(), ConstEvalError> {
        if let Some((id, off)) = self.access(ptr, size, 1, true)? {
            let a = &mut self.memory.allocations[id.0 as usize];
            a.init_mask[off..off + size as usize].fill(false);
            clear_provenance(a, off as u64, off as u64 + size);
        }
        Ok(())
    }
    pub(super) fn deallocate(&mut self, ptr: Scalar, size: u64, align: u64) -> Result<(), ConstEvalError> {
        let (id, off) = ptr_parts(ptr)?;
        let a = self.memory.get(id).ok_or(ConstEvalError::Ub("dangling pointer"))?;
        if matches!(self.kinds[id.0 as usize], MemoryKind::Global) {
            return Ok(());
        }
        if a.deallocated
            || off != 0
            || a.bytes.len() as u64 != size
            || a.align != align
            || !matches!(self.kinds[id.0 as usize], MemoryKind::Heap(false))
        {
            return Err(ConstEvalError::Ub("incorrect allocation or layout passed to const_deallocate"));
        }
        self.memory.allocations[id.0 as usize].deallocated = true;
        Ok(())
    }
    pub(super) fn make_global(&mut self, ptr: Scalar) -> Result<(), ConstEvalError> {
        let (id, off) = ptr_parts(ptr)?;
        let a = self.memory.get(id).ok_or(ConstEvalError::Ub("dangling pointer"))?;
        if a.deallocated || off != 0 || !matches!(self.kinds[id.0 as usize], MemoryKind::Heap(false)) {
            return Err(ConstEvalError::Ub("const_make_global requires a live, non-global heap allocation at offset zero"));
        }
        self.kinds[id.0 as usize] = MemoryKind::Heap(true);
        self.memory.allocations[id.0 as usize].mutability = Mutability::Not;
        Ok(())
    }
    /// Intern only after typed validation; scan raw relocations too (unions/raw pointers).
    /// rustc_const_eval/src/interpret/intern.rs:65,108.
    pub(super) fn intern(&mut self, root: AllocId) -> Result<(), ConstEvalError> {
        let mut pending = vec![root];
        let mut seen = vec![false; self.memory.allocations.len()];
        while let Some(id) = pending.pop() {
            let a = self.memory.get(id).ok_or(ConstEvalError::Ub("dangling pointer in final value"))?;
            if a.deallocated {
                return Err(ConstEvalError::Ub("dangling pointer in final value"));
            }
            if seen[id.0 as usize] {
                continue;
            }
            seen[id.0 as usize] = true;
            if matches!(self.kinds[id.0 as usize], MemoryKind::Heap(false)) {
                return Err(ConstEvalError::HeapNotGlobal);
            }
            let mut fragments = a.provenance_fragments.clone();
            fragments.sort_unstable_by_key(|p| p.0);
            let mut merged = Vec::new();
            let mut i = 0;
            while i < fragments.len() {
                let (at, p, byte) = fragments[i];
                if byte != 0 || i + 8 > fragments.len() {
                    return Err(ConstEvalError::Unsupported("partial pointer in const value"));
                }
                for j in 0..8 {
                    if fragments[i + j] != (at + j as u64, p, j as u8) {
                        return Err(ConstEvalError::Unsupported("partial pointer in const value"));
                    }
                }
                merged.push((at, p));
                i += 8;
            }
            let a = &mut self.memory.allocations[id.0 as usize];
            a.provenance.extend(merged);
            a.provenance_fragments.clear();
            for &(_, next) in &a.provenance {
                // Check every edge, even when another pointer already reached this allocation.
                // Existing globals (including const_make_global) need no new justification.
                // rustc_const_eval/src/interpret/intern.rs:286-326.
                if !next.shared_ref() && matches!(self.kinds.get(next.alloc.0 as usize), Some(MemoryKind::Stack)) {
                    return Err(ConstEvalError::MutableReference);
                }
                pending.push(next.alloc);
            }
        }
        for (i, yes) in seen.into_iter().enumerate() {
            if yes {
                self.memory.allocations[i].mutability = Mutability::Not;
                if !matches!(self.kinds[i], MemoryKind::Function(..)) {
                    self.kinds[i] = MemoryKind::Global;
                }
            }
        }
        Ok(())
    }
}
