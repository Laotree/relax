//! CTFE over runtime MIR. rustc_const_eval/src/interpret/eval_context.rs:75,
//! step.rs:40 and const_eval/machine.rs:467. All semantic queries belong to the provider.
mod intrinsics;
mod memory;
mod operand;
mod place;
mod step;
#[cfg(test)]
mod tests;

use super::*;
use crate::layout::{Layout, TagEnc};
use crate::program::Prim;
use crate::tcx::Tcx;
use crate::types::TyKind;
pub use intrinsics::{Intrinsic, Intrinsics};
pub use operand::Immediate;
pub use place::MPlace;

pub type LayoutRef = &'static Layout;
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LayoutError {
    Unknown(TyId),
    TooBig(TyId),
    CoroutineNotAvailable(TyId),
}

/// Bodies and field types are instantiated and normalized before entering the machine.
/// Layout failures must include nested unresolved types; a placeholder layout is never valid.
/// rustc_const_eval/src/interpret/eval_context.rs:135; rustc_middle/src/ty/layout.rs:719.
pub trait MirProvider {
    fn tcx(&self) -> &Tcx;
    fn body(&self, def: DefId, args: &[TyId]) -> Option<&Body>;
    fn layout_of(&self, ty: TyId) -> Result<LayoutRef, LayoutError>;
    fn field_ty(&self, ty: TyId, variant: u32, field: u32) -> Result<TyId, ConstEvalError>;
    fn is_unsized(&self, ty: TyId) -> Result<bool, LayoutError>;
    fn is_freeze(&self, ty: TyId) -> Result<bool, LayoutError>;
    /// Lang-item identity, not the layout's no_niche flag (also used by UnsafePinned).
    /// rustc_const_eval/src/interpret/validity.rs:1377.
    fn is_unsafe_cell(&self, ty: TyId) -> Result<bool, LayoutError>;
    fn needs_drop(&self, _ty: TyId) -> Result<bool, ConstEvalError> {
        Err(ConstEvalError::Query("needs_drop requires Q1b"))
    }
    fn type_hash(&self, _ty: TyId) -> Result<u128, ConstEvalError> {
        Err(ConstEvalError::Query("stable::type_hash requires Program"))
    }
    fn type_name(&self, _ty: TyId) -> Result<String, ConstEvalError> {
        Err(ConstEvalError::Query("type_name requires Program"))
    }
    fn reify(&self, def: DefId, args: &[TyId]) -> Result<(DefId, Vec<TyId>), ConstEvalError> {
        Ok((def, args.to_vec()))
    }
    fn closure_fn(&self, _ty: TyId) -> Result<(DefId, Vec<TyId>), ConstEvalError> {
        Err(ConstEvalError::Query("closure function pointer requires M6 shim MIR"))
    }
    fn vtable(&self, _source: TyId, _target: TyId, _old: Option<Scalar>) -> Result<Scalar, ConstEvalError> {
        Err(ConstEvalError::Query("vtable requires M6"))
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ConstEvalError {
    Layout(LayoutError),
    Query(&'static str),
    InvalidMir(&'static str),
    Ub(&'static str),
    Unsupported(&'static str),
    Panic(String),
    StepLimit,
    CallDepth,
    MissingBody(DefId),
    MutableReference,
    HeapNotGlobal,
}
impl From<LayoutError> for ConstEvalError {
    fn from(e: LayoutError) -> Self {
        Self::Layout(e)
    }
}
impl std::fmt::Display for ConstEvalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "evaluation of constant value failed: ")?;
        match self {
            Self::Layout(e) => write!(f, "layout query failed: {e:?}"),
            Self::Query(s) | Self::InvalidMir(s) | Self::Ub(s) | Self::Unsupported(s) => f.write_str(s),
            Self::Panic(s) => f.write_str(s),
            Self::StepLimit => f.write_str("constant evaluation exceeded the step limit"),
            Self::CallDepth => f.write_str("reached the configured maximum number of stack frames"),
            Self::MissingBody(d) => write!(f, "no runtime MIR for {d:?}"),
            Self::MutableReference => f.write_str("mutable reference in the final value of a constant"),
            Self::HeapNotGlobal => f.write_str("non-global heap allocation in const value"),
        }
    }
}
impl std::error::Error for ConstEvalError {}

#[derive(Clone, Copy)]
pub struct Limits {
    pub steps: u64,
    pub call_depth: usize,
}
impl Default for Limits {
    fn default() -> Self {
        Self { steps: 1_000_000, call_depth: 128 }
    }
}

#[derive(Clone, Debug)]
enum MemoryKind {
    Stack,
    Heap(bool),
    Global,
    Function(DefId, Vec<TyId>),
}
struct Frame<'a> {
    body: &'a Body,
    locals: Vec<Option<MPlace>>,
    block: usize,
    statement: usize,
    destination: Option<MPlace>,
}

/// AllocIds are scoped to `memory`; constants supplied by the provider must use this same table.
/// Successful results remain in that table, including all reachable immutable allocations.
pub struct Interpreter<'a> {
    provider: &'a dyn MirProvider,
    pub memory: AllocMap,
    kinds: Vec<MemoryKind>,
    intrinsics: &'a Intrinsics,
    limits: Limits,
    steps: u64,
    frames: Vec<Frame<'a>>,
}
impl<'a> Interpreter<'a> {
    pub fn new(provider: &'a dyn MirProvider, memory: AllocMap, intrinsics: &'a Intrinsics, limits: Limits) -> Self {
        let mut kinds = vec![MemoryKind::Global; memory.allocations.len()];
        for (id, def, args) in &memory.functions {
            kinds[id.0 as usize] = MemoryKind::Function(*def, args.clone());
        }
        Self { provider, memory, kinds, intrinsics, limits, steps: 0, frames: Vec::new() }
    }
    fn layout(&self, ty: TyId) -> Result<LayoutRef, ConstEvalError> {
        Ok(self.provider.layout_of(ty)?)
    }
    fn kind(&self, ty: TyId) -> &TyKind {
        self.provider.tcx().tys.kind(ty)
    }
    fn tick(&mut self) -> Result<(), ConstEvalError> {
        self.steps = self.steps.checked_add(1).ok_or(ConstEvalError::StepLimit)?;
        if self.steps > self.limits.steps {
            return Err(ConstEvalError::StepLimit);
        }
        Ok(())
    }
    pub fn eval_to_allocation(&mut self, body: &'a Body) -> Result<(AllocId, LayoutRef), ConstEvalError> {
        if !self.frames.is_empty() {
            return Err(ConstEvalError::InvalidMir("evaluation already active"));
        }
        self.steps = 0;
        let first_alloc = self.memory.allocations.len();
        let result = self.eval_body(body);
        if result.is_err() {
            self.frames.clear();
            for i in first_alloc..self.memory.allocations.len() {
                if !matches!(self.kinds[i], MemoryKind::Global | MemoryKind::Function(..)) {
                    self.memory.allocations[i].deallocated = true;
                }
            }
        }
        result
    }
    fn eval_body(&mut self, body: &'a Body) -> Result<(AllocId, LayoutRef), ConstEvalError> {
        let ty = body.local_decls.first().ok_or(ConstEvalError::InvalidMir("missing return local"))?.ty;
        let result = self.allocate_place(ty, MemoryKind::Stack)?;
        self.push_frame(body, &[], Some(result))?;
        while !self.frames.is_empty() {
            self.step()?;
        }
        self.validate_value(result, &mut Vec::new())?;
        let id = ptr_parts(result.ptr)?.0;
        self.intern(id)?;
        Ok((id, self.layout(ty)?))
    }
    pub fn eval_to_scalar(&mut self, body: &'a Body) -> Result<Scalar, ConstEvalError> {
        let (id, layout) = self.eval_to_allocation(body)?;
        self.read_scalar(Scalar::Ptr { provenance: CtfeProvenance::new(id), offset: 0 }, layout.size as u64, layout.align as u64)
    }
    fn allocate_place(&mut self, ty: TyId, kind: MemoryKind) -> Result<MPlace, ConstEvalError> {
        let l = self.layout(ty)?;
        let ptr = self.allocate(l.size as u64, l.align as u64, kind)?;
        Ok(MPlace { ptr, ty, meta: None, variant: None, align: l.align as u64 })
    }
}
fn mask(size: u8) -> u128 {
    if size >= 16 {
        u128::MAX
    } else {
        (1u128 << (size * 8)) - 1
    }
}
fn int(bits: u128, size: u8) -> Scalar {
    Scalar::Int { bits: bits & mask(size), size }
}
fn bits(s: Scalar) -> Result<u128, ConstEvalError> {
    match s {
        Scalar::Int { bits, .. } => Ok(bits),
        Scalar::Ptr { .. } => Err(ConstEvalError::Unsupported("unable to turn pointer into integer")),
    }
}
fn ptr_parts(s: Scalar) -> Result<(AllocId, u64), ConstEvalError> {
    match s {
        Scalar::Ptr { provenance, offset } => Ok((provenance.alloc, offset)),
        _ => Err(ConstEvalError::Ub("dangling pointer (no provenance)")),
    }
}
fn signed(k: &TyKind) -> bool {
    matches!(k, TyKind::Int(Prim::I8 | Prim::I16 | Prim::I32 | Prim::I64 | Prim::I128 | Prim::Isize))
}
fn sext(v: u128, size: u8) -> i128 {
    let shift = 128 - size as u32 * 8;
    ((v << shift) as i128) >> shift
}
fn add_offset(ptr: Scalar, offset: u64) -> Result<Scalar, ConstEvalError> {
    match ptr {
        Scalar::Ptr { provenance, offset: base } => {
            Ok(Scalar::Ptr { provenance, offset: base.checked_add(offset).ok_or(ConstEvalError::Ub("pointer offset overflow"))? })
        }
        Scalar::Int { bits, size } => Ok(int(bits.checked_add(offset as u128).ok_or(ConstEvalError::Ub("pointer offset overflow"))?, size)),
    }
}
fn mem_size(mem: crate::rir::Mem) -> u8 {
    match mem {
        crate::rir::Mem::Int(n, _) => n,
        crate::rir::Mem::F32 => 4,
        crate::rir::Mem::F64 => 8,
    }
}
impl Interpreter<'_> {
    fn array_len(&self, n: u64) -> Option<u64> {
        match crate::types::len_ty(n) {
            None => Some(n),
            Some(t) => match self.kind(t) {
                TyKind::ConstVal(v) => Some(*v),
                _ => None,
            },
        }
    }
}
