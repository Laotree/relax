use super::*;
use crate::layout::Layouts;
use crate::program::Program;
use crate::tcx::{AdtT, FieldT, VariantT};
use std::collections::HashMap;

struct Provider {
    tcx: Tcx,
    layouts: Layouts,
    bodies: HashMap<DefId, Body>,
    prog: Program,
    freeze: HashMap<TyId, Result<bool, LayoutError>>,
    unsafe_cells: Vec<TyId>,
}
impl Provider {
    fn new() -> Self {
        Self {
            tcx: Tcx::new(),
            layouts: Layouts::new(),
            bodies: HashMap::new(),
            prog: Program::new(&std::sync::Arc::new(crate::Session::default())),
            freeze: HashMap::new(),
            unsafe_cells: Vec::new(),
        }
    }
    fn check_type(&self, ty: TyId, seen: &mut Vec<TyId>) -> Result<(), LayoutError> {
        if seen.contains(&ty) {
            return Ok(());
        }
        seen.push(ty);
        if self.tcx.is_coroutine(ty) {
            return Err(LayoutError::CoroutineNotAvailable(ty));
        }
        if !self.tcx.tys.is_concrete(ty) {
            return Err(LayoutError::Unknown(ty));
        }
        match self.tcx.tys.kind(ty) {
            TyKind::Param(_) | TyKind::Infer(_) | TyKind::Assoc(..) | TyKind::Opaque(..) | TyKind::Error | TyKind::ConstVal(_) => {
                return Err(LayoutError::Unknown(ty))
            }
            TyKind::Array(t, n) => {
                if crate::types::len_ty(*n).is_some() {
                    return Err(LayoutError::Unknown(ty));
                }
                self.check_type(*t, seen)?;
            }
            TyKind::Tuple(ts) => {
                for t in ts {
                    self.check_type(*t, seen)?;
                }
            }
            TyKind::Adt(d, args, _) => {
                let adt = self.tcx.adts.get(d).ok_or(LayoutError::Unknown(ty))?;
                for v in &adt.variants {
                    for f in &v.fields {
                        self.check_type(self.tcx.tys.subst(f.ty, args), seen)?;
                    }
                }
            }
            TyKind::Closure(_, _, _, upvars, _) => self.check_type(*upvars, seen)?,
            _ => {}
        }
        Ok(())
    }
}
impl MirProvider for Provider {
    fn tcx(&self) -> &Tcx {
        &self.tcx
    }
    fn body(&self, def: DefId, _: &[TyId]) -> Option<&Body> {
        self.bodies.get(&def)
    }
    fn layout_of(&self, ty: TyId) -> Result<LayoutRef, LayoutError> {
        self.check_type(ty, &mut Vec::new())?;
        let l = self.layouts.of(&crate::layout::LayoutCx::new(&self.prog), &self.tcx, ty);
        if self.layouts.is_too_big(ty) {
            return Err(LayoutError::TooBig(ty));
        }
        Ok(l)
    }
    fn field_ty(&self, ty: TyId, variant: u32, field: u32) -> Result<TyId, ConstEvalError> {
        match self.tcx.tys.kind(ty) {
            TyKind::Tuple(ts) => ts.get(field as usize).copied().ok_or(ConstEvalError::InvalidMir("bad field")),
            TyKind::Adt(d, args, _) => Ok(self.tcx.tys.subst(self.tcx.adts[d].variants[variant as usize].fields[field as usize].ty, args)),
            TyKind::Closure(_, _, _, upvars, _) => self.field_ty(*upvars, variant, field),
            _ => Err(ConstEvalError::InvalidMir("no fields")),
        }
    }
    fn is_unsized(&self, ty: TyId) -> Result<bool, LayoutError> {
        self.check_type(ty, &mut Vec::new())?;
        Ok(self.layouts.is_unsized(&crate::layout::LayoutCx::new(&self.prog), &self.tcx, ty))
    }
    fn needs_drop(&self, _: TyId) -> Result<bool, ConstEvalError> {
        Ok(false)
    }
    fn is_freeze(&self, ty: TyId) -> Result<bool, LayoutError> {
        if let Some(answer) = self.freeze.get(&ty) {
            return answer.clone();
        }
        self.check_type(ty, &mut Vec::new())?;
        Ok(true)
    }
    fn is_unsafe_cell(&self, ty: TyId) -> Result<bool, LayoutError> {
        self.check_type(ty, &mut Vec::new())?;
        Ok(self.unsafe_cells.contains(&ty))
    }
    fn type_hash(&self, ty: TyId) -> Result<u128, ConstEvalError> {
        Ok(crate::stable::type_hash(&self.prog, &self.tcx, ty))
    }
    fn type_name(&self, ty: TyId) -> Result<String, ConstEvalError> {
        Ok(crate::typeck::type_name(&self.prog, &self.tcx, ty))
    }
}
fn local(n: u32) -> Place {
    Place::local(Local(n))
}
fn copy(n: u32) -> Operand {
    Operand::Copy(local(n))
}
fn val(ty: TyId, value: ConstValue) -> Operand {
    Operand::Constant(Box::new(ConstOperand { span: Span::default(), user_ty: None, const_: Const::Val(value, ty) }))
}
fn number(p: &Provider, ty: TyId, n: u128) -> Operand {
    val(ty, ConstValue::Scalar(int(n, p.layout_of(ty).unwrap().size as u8)))
}
fn stmt(kind: StatementKind) -> Statement {
    Statement { source_info: SourceInfo::default(), kind }
}
fn assign(n: u32, r: Rvalue) -> Statement {
    stmt(StatementKind::Assign(local(n), r))
}
fn block(statements: Vec<Statement>, kind: TerminatorKind) -> BasicBlockData {
    BasicBlockData { statements, terminator: Some(Terminator { source_info: SourceInfo::default(), kind }), is_cleanup: false }
}
fn body(tys: &[TyId], blocks: Vec<BasicBlockData>, arg_count: u32) -> Body {
    let mut locals = Vec::new();
    for (i, ty) in tys.iter().enumerate() {
        locals.push(LocalDecl {
            ty: *ty,
            mutability: Mutability::Mut,
            user_ty: Vec::new(),
            source_info: SourceInfo::default(),
            kind: if i == 0 {
                LocalKind::Return
            } else if i <= arg_count as usize {
                LocalKind::Arg
            } else {
                LocalKind::Temp
            },
            local_info: LocalInfo::Boring,
        });
    }
    Body {
        phase: MirPhase::Runtime(RuntimePhase::Initial),
        source: MirSource { owner: DefId(0), kind: BodyKind::Const },
        basic_blocks: blocks,
        local_decls: locals,
        source_scopes: vec![SourceScopeData { span: Span::default(), parent_scope: None }],
        user_type_annotations: Vec::new(),
        var_debug_info: Vec::new(),
        arg_count,
        spread_arg: None,
        promoted: Vec::new(),
        coroutine: None,
    }
}
fn run(p: &Provider, b: &Body) -> Result<Scalar, ConstEvalError> {
    let table = Intrinsics::default();
    Interpreter::new(p, AllocMap::default(), &table, Limits::default()).eval_to_scalar(b)
}
fn field(n: u32, f: u32, ty: TyId) -> Place {
    Place { local: Local(n), projection: vec![PlaceElem::Field(FieldIdx(f), ty)] }
}
fn bin(op: BinOp, a: Operand, b: Operand) -> Rvalue {
    Rvalue::BinaryOp(op, Box::new((a, b)))
}
fn call(p: &Provider, def: u32, types: Vec<TyId>, args: Vec<Operand>, dest: u32, next: u32) -> TerminatorKind {
    let ty = p.tcx.tys.intern(TyKind::FnDef(DefId(def), types, crate::types::RegionArgsId::EMPTY));
    TerminatorKind::Call {
        func: val(ty, ConstValue::ZeroSized),
        args,
        destination: local(dest),
        target: Some(BasicBlock(next)),
        unwind: UnwindAction::Unreachable,
        call_source: CallSource::Normal,
        fn_span: Span::default(),
        arg_spans: Vec::new(),
    }
}
#[test]
fn checked_overflow_assert_and_wrapping() {
    let p = Provider::new();
    let t = p.tcx.tys.u8_;
    let boolean = p.tcx.tys.bool_;
    let pair = p.tcx.tys.intern(TyKind::Tuple(vec![t, boolean]));
    let a = number(&p, t, 255);
    let b = number(&p, t, 1);
    let mir = body(
        &[t, pair],
        vec![
            block(
                vec![assign(1, bin(BinOp::AddWithOverflow, a.clone(), b.clone()))],
                TerminatorKind::Assert {
                    cond: Operand::Copy(field(1, 1, boolean)),
                    expected: false,
                    msg: AssertKind::Overflow(BinOp::Add, a, b),
                    target: BasicBlock(1),
                    unwind: UnwindAction::Unreachable,
                },
            ),
            block(vec![assign(0, Rvalue::Use(Operand::Copy(field(1, 0, t))))], TerminatorKind::Return),
        ],
        0,
    );
    assert_eq!(run(&p, &mir), Err(ConstEvalError::Panic("attempt to compute `255 + 1`, which would overflow".into())));
    let mir = body(&[t], vec![block(vec![assign(0, bin(BinOp::Add, number(&p, t, 255), number(&p, t, 1)))], TerminatorKind::Return)], 0);
    assert_eq!(run(&p, &mir), Ok(int(0, 1)));
}
#[test]
fn loop_to_1000_and_step_limit() {
    let p = Provider::new();
    let t = p.tcx.tys.u32_;
    let b = p.tcx.tys.bool_;
    let mir = body(
        &[t, b],
        vec![
            block(vec![assign(0, Rvalue::Use(number(&p, t, 0)))], TerminatorKind::Goto { target: BasicBlock(1) }),
            block(
                vec![assign(0, bin(BinOp::Add, copy(0), number(&p, t, 1))), assign(1, bin(BinOp::Lt, copy(0), number(&p, t, 1000)))],
                TerminatorKind::SwitchInt {
                    discr: copy(1),
                    targets: SwitchTargets { values: vec![1], targets: vec![BasicBlock(1)], otherwise: BasicBlock(2) },
                },
            ),
            block(vec![], TerminatorKind::Return),
        ],
        0,
    );
    assert_eq!(run(&p, &mir), Ok(int(1000, 4)));
    let table = Intrinsics::default();
    let mut ecx = Interpreter::new(&p, AllocMap::default(), &table, Limits { steps: 100, call_depth: 128 });
    assert_eq!(ecx.eval_to_scalar(&mir), Err(ConstEvalError::StepLimit));
}
#[test]
fn provider_call_and_depth_limit() {
    let mut p = Provider::new();
    let t = p.tcx.tys.u32_;
    let callee = body(&[t, t], vec![block(vec![assign(0, bin(BinOp::Mul, copy(1), number(&p, t, 2)))], TerminatorKind::Return)], 1);
    p.bodies.insert(DefId(7), callee);
    let mir = body(&[t], vec![block(vec![], call(&p, 7, vec![], vec![number(&p, t, 21)], 0, 1)), block(vec![], TerminatorKind::Return)], 0);
    assert_eq!(run(&p, &mir), Ok(int(42, 4)));
    let table = Intrinsics::default();
    let mut ecx = Interpreter::new(&p, AllocMap::default(), &table, Limits { steps: 100, call_depth: 1 });
    assert_eq!(ecx.eval_to_scalar(&mir), Err(ConstEvalError::CallDepth));
}
fn adt(p: &mut Provider, id: u32, variants: Vec<Vec<TyId>>, is_enum: bool) -> TyId {
    let name = p.prog.syms.intern("field");
    let mut vs = Vec::new();
    for (i, types) in variants.into_iter().enumerate() {
        let mut fields = Vec::new();
        for ty in types {
            fields.push(FieldT { name, ty, is_pub: true, vis_mod: u32::MAX });
        }
        vs.push(VariantT { def: DefId(id + i as u32 + 1), name, shape: 1, fields, disc: i as i128 });
    }
    p.tcx.adts.insert(
        DefId(id),
        AdtT {
            region_contract: Default::default(), generic_indices: Default::default(),
            region_params: crate::types::RegionArgsId::EMPTY,
            flags: if is_enum { crate::tcx::AdtFlags::IS_ENUM } else { crate::tcx::AdtFlags::IS_STRUCT },
            is_enum,
            is_union: false,
            n_generics: 0,
            variants: vs,
            repr_c: false,
            repr_int: None,
            repr_align: 0,
            repr_packed: 0,
            valid_start: None,
            valid_end: None,
            no_niche: false,
            param_maybe_unsized: Vec::new(),
            ext_from: u32::MAX,
            ext_conv: Vec::new(),
        },
    );
    p.tcx.tys.intern(TyKind::Adt(DefId(id), vec![], crate::types::RegionArgsId::EMPTY))
}
#[test]
fn struct_aggregate_and_field_read() {
    let mut p = Provider::new();
    let t = p.tcx.tys.u32_;
    let byte = p.tcx.tys.u8_;
    let ty = adt(&mut p, 10, vec![vec![byte, t]], false);
    let mir = body(
        &[t, ty],
        vec![block(
            vec![
                assign(
                    1,
                    Rvalue::Aggregate(
                        Box::new(AggregateKind::Adt(DefId(10), VariantIdx(0), vec![], None, None)),
                        vec![number(&p, byte, 3), number(&p, t, 42)],
                    ),
                ),
                assign(0, Rvalue::Use(Operand::Copy(field(1, 1, t)))),
            ],
            TerminatorKind::Return,
        )],
        0,
    );
    assert_eq!(run(&p, &mir), Ok(int(42, 4)));
}
#[test]
fn niche_enum_and_discriminant() {
    let mut p = Provider::new();
    let t = p.tcx.tys.u32_;
    let reference = p.tcx.tys.intern(TyKind::Ref(false, t, crate::types::RegionId::ERASED));
    let ty = adt(&mut p, 20, vec![vec![], vec![reference]], true);
    assert!(matches!(p.layout_of(ty).unwrap().enc, TagEnc::Niche { .. }));
    let mir = body(
        &[t, ty, t, reference],
        vec![block(
            vec![
                assign(2, Rvalue::Use(number(&p, t, 77))),
                assign(3, Rvalue::Ref(Region::ERASED, BorrowKind::Shared, local(2))),
                assign(1, Rvalue::Aggregate(Box::new(AggregateKind::Adt(DefId(20), VariantIdx(1), vec![], None, None)), vec![copy(3)])),
                assign(0, Rvalue::Discriminant(local(1))),
            ],
            TerminatorKind::Return,
        )],
        0,
    );
    assert_eq!(run(&p, &mir), Ok(int(1, 4)));
    let mir = body(
        &[t, ty],
        vec![block(
            vec![
                stmt(StatementKind::SetDiscriminant { place: local(1), variant_index: VariantIdx(0) }),
                assign(0, Rvalue::Discriminant(local(1))),
            ],
            TerminatorKind::Return,
        )],
        0,
    );
    assert_eq!(run(&p, &mir), Ok(int(0, 4)));
}
#[test]
fn promoted_static_slice_and_nested_interning() {
    let mut p = Provider::new();
    let t = p.tcx.tys.u8_;
    let array = p.tcx.tys.intern(TyKind::Array(t, 3));
    let reference = p.tcx.tys.intern(TyKind::Ref(false, array, crate::types::RegionId::ERASED));
    let slice = p.tcx.tys.intern(TyKind::Ref(false, p.tcx.tys.intern(TyKind::Slice(t)), crate::types::RegionId::ERASED));
    let promoted = body(
        &[array],
        vec![block(
            vec![assign(
                0,
                Rvalue::Aggregate(Box::new(AggregateKind::Array(t)), vec![number(&p, t, 1), number(&p, t, 2), number(&p, t, 3)]),
            )],
            TerminatorKind::Return,
        )],
        0,
    );
    p.bodies.insert(DefId(30), promoted);
    let table = Intrinsics::default();
    let mut ecx = Interpreter::new(&p, AllocMap::default(), &table, Limits::default());
    let (alloc, _) = ecx.eval_to_allocation(&p.bodies[&DefId(30)]).unwrap();
    let mir = body(
        &[slice, reference],
        vec![block(
            vec![
                assign(
                    1,
                    Rvalue::Use(val(reference, ConstValue::Scalar(Scalar::Ptr { provenance: CtfeProvenance::new(alloc), offset: 0 }))),
                ),
                assign(0, Rvalue::Cast(CastKind::PointerCoercion(PointerCoercion::Unsize, CoercionSource::Implicit), copy(1), slice)),
            ],
            TerminatorKind::Return,
        )],
        0,
    );
    let (out, l) = ecx.eval_to_allocation(&mir).unwrap();
    assert_eq!(l.size, 16);
    assert_eq!(ecx.read_scalar(Scalar::Ptr { provenance: CtfeProvenance::new(out), offset: 8 }, 8, 8).unwrap(), int(3, 8));
    assert_eq!(ecx.memory.get(alloc).unwrap().mutability, Mutability::Not);
}
#[test]
fn transmute_array_bytes_to_u32() {
    let p = Provider::new();
    let t = p.tcx.tys.u8_;
    let array = p.tcx.tys.intern(TyKind::Array(t, 4));
    let u32_ = p.tcx.tys.u32_;
    let mir = body(
        &[u32_, array],
        vec![block(
            vec![
                assign(
                    1,
                    Rvalue::Aggregate(
                        Box::new(AggregateKind::Array(t)),
                        vec![number(&p, t, 0x78), number(&p, t, 0x56), number(&p, t, 0x34), number(&p, t, 0x12)],
                    ),
                ),
                assign(0, Rvalue::Cast(CastKind::Transmute, copy(1), u32_)),
            ],
            TerminatorKind::Return,
        )],
        0,
    );
    assert_eq!(run(&p, &mir), Ok(int(0x12345678, 4)));
}
#[test]
fn uninit_out_of_bounds_alignment_and_dangling() {
    let p = Provider::new();
    let t = p.tcx.tys.u32_;
    let mir = body(&[t], vec![block(vec![], TerminatorKind::Return)], 0);
    assert_eq!(run(&p, &mir), Err(ConstEvalError::Ub("using uninitialized data")));
    let table = Intrinsics::default();
    let mut ecx = Interpreter::new(&p, AllocMap::default(), &table, Limits::default());
    let ptr = ecx.allocate(4, 4, MemoryKind::Heap(false)).unwrap();
    assert_eq!(ecx.read_scalar(add_offset(ptr, 4).unwrap(), 1, 1), Err(ConstEvalError::Ub("out-of-bounds pointer use")));
    assert_eq!(ecx.read_scalar(add_offset(ptr, 1).unwrap(), 1, 4), Err(ConstEvalError::Ub("accessing memory with insufficient alignment")));
    ecx.deallocate(ptr, 4, 4).unwrap();
    assert_eq!(ecx.read_scalar(ptr, 4, 4), Err(ConstEvalError::Ub("pointer to deallocated allocation")));
}
#[test]
fn heap_intrinsic_global_and_interning_rules() {
    let p = Provider::new();
    let byte = p.tcx.tys.u8_;
    let ptr = p.tcx.tys.intern(TyKind::Ptr(true, byte));
    let n = p.tcx.tys.usize_;
    let mir = body(
        &[ptr],
        vec![
            block(vec![], call(&p, 40, vec![], vec![number(&p, n, 4), number(&p, n, 4)], 0, 1)),
            block(vec![], call(&p, 41, vec![], vec![copy(0)], 0, 2)),
            block(vec![], TerminatorKind::Return),
        ],
        0,
    );
    let mut table = Intrinsics::default();
    table.register(DefId(40), "const_allocate").unwrap();
    table.register(DefId(41), "const_make_global").unwrap();
    let mut ecx = Interpreter::new(&p, AllocMap::default(), &table, Limits::default());
    let result = ecx.eval_to_scalar(&mir).unwrap();
    let (id, _) = ptr_parts(result).unwrap();
    assert_eq!(ecx.memory.get(id).unwrap().mutability, Mutability::Not);
    assert_eq!(ecx.write_scalar(result, int(0, 4), 4, 4), Err(ConstEvalError::Ub("writing to read-only memory")));
    assert!(ecx.make_global(result).is_err());
    let nonglobal = body(
        &[ptr],
        vec![block(vec![], call(&p, 40, vec![], vec![number(&p, n, 4), number(&p, n, 4)], 0, 1)), block(vec![], TerminatorKind::Return)],
        0,
    );
    let mut ecx = Interpreter::new(&p, AllocMap::default(), &table, Limits::default());
    assert_eq!(ecx.eval_to_scalar(&nonglobal), Err(ConstEvalError::HeapNotGlobal));
}
#[test]
fn pointer_fragments_reconstruct_and_integer_reads_reject() {
    let p = Provider::new();
    let table = Intrinsics::default();
    let mut ecx = Interpreter::new(&p, AllocMap::default(), &table, Limits::default());
    let pointee = ecx.allocate(1, 1, MemoryKind::Heap(false)).unwrap();
    let src = ecx.allocate(8, 8, MemoryKind::Stack).unwrap();
    let dst = ecx.allocate(8, 8, MemoryKind::Stack).unwrap();
    ecx.write_scalar(src, pointee, 8, 8).unwrap();
    ecx.copy_bytes(src, dst, 4, 1, true).unwrap();
    assert!(ecx.read_scalar(dst, 4, 1).is_err());
    ecx.copy_bytes(add_offset(src, 4).unwrap(), add_offset(dst, 4).unwrap(), 4, 1, true).unwrap();
    assert_eq!(ecx.read_scalar(dst, 8, 8).unwrap(), pointee);
    ecx.write_scalar(add_offset(dst, 1).unwrap(), int(0, 1), 1, 1).unwrap();
    assert!(ecx.read_scalar(dst, 8, 8).is_err());
}
#[test]
fn mutable_reference_and_dead_stack_result_rejected() {
    let p = Provider::new();
    let t = p.tcx.tys.u32_;
    let r = p.tcx.tys.intern(TyKind::Ref(true, t, crate::types::RegionId::ERASED));
    let mir = body(
        &[r, t],
        vec![block(
            vec![
                assign(1, Rvalue::Use(number(&p, t, 1))),
                assign(0, Rvalue::Ref(Region::ERASED, BorrowKind::Mut { kind: MutBorrowKind::Default }, local(1))),
            ],
            TerminatorKind::Return,
        )],
        0,
    );
    assert_eq!(run(&p, &mir), Err(ConstEvalError::MutableReference));
    let r = p.tcx.tys.intern(TyKind::Ref(false, t, crate::types::RegionId::ERASED));
    let mir = body(
        &[r, t],
        vec![block(
            vec![assign(1, Rvalue::Use(number(&p, t, 1))), assign(0, Rvalue::Ref(Region::ERASED, BorrowKind::Shared, local(1)))],
            TerminatorKind::Return,
        )],
        0,
    );
    assert_eq!(run(&p, &mir), Err(ConstEvalError::Ub("pointer to deallocated allocation")));
}
#[test]
fn layout_errors_are_fallible() {
    let p = Provider::new();
    let ty = p.tcx.tys.intern(TyKind::Param(0));
    assert!(matches!(p.layout_of(ty), Err(LayoutError::Unknown(_))));
    let array = p.tcx.tys.intern(TyKind::Array(p.tcx.tys.u32_, u32::MAX as u64));
    assert!(matches!(p.layout_of(array), Err(LayoutError::TooBig(_))));
    let mir = body(&[ty], vec![block(vec![], TerminatorKind::Return)], 0);
    assert_eq!(run(&p, &mir), Err(ConstEvalError::Layout(LayoutError::Unknown(ty))));
}
#[test]
fn casts_saturate_and_preserve_pointer_provenance() {
    let p = Provider::new();
    let f = p.tcx.tys.intern(TyKind::Float(Prim::F64));
    let i = p.tcx.tys.intern(TyKind::Int(Prim::I8));
    for (n, expected) in [(f64::INFINITY, 127), (f64::NEG_INFINITY, 128), (f64::NAN, 0), (-3.8, 253)] {
        let mir = body(
            &[i],
            vec![block(vec![assign(0, Rvalue::Cast(CastKind::FloatToInt, number(&p, f, n.to_bits() as u128), i))], TerminatorKind::Return)],
            0,
        );
        assert_eq!(run(&p, &mir), Ok(int(expected, 1)));
    }
}
#[test]
fn numeric_intrinsics_and_stable_type_hash_halves() {
    let p = Provider::new();
    let t = p.tcx.tys.u64_;
    for (name, input, output) in
        [("ctpop", 0xf0, 4), ("ctlz", 1, 63), ("cttz", 8, 3), ("bswap", 1, 1u128 << 56), ("bitreverse", 1, 1u128 << 63)]
    {
        let mut table = Intrinsics::default();
        table.register(DefId(50), name).unwrap();
        let mir = body(
            &[t],
            vec![block(vec![], call(&p, 50, vec![t], vec![number(&p, t, input)], 0, 1)), block(vec![], TerminatorKind::Return)],
            0,
        );
        let mut ecx = Interpreter::new(&p, AllocMap::default(), &table, Limits::default());
        assert_eq!(ecx.eval_to_scalar(&mir), Ok(int(output, 8)), "{name}");
    }
    let hash = crate::stable::type_hash(&p.prog, &p.tcx, t);
    for (name, expected) in [("type_id", hash), ("type_id_hi", hash >> 64)] {
        let mut table = Intrinsics::default();
        table.register(DefId(50), name).unwrap();
        let mir = body(&[t], vec![block(vec![], call(&p, 50, vec![t], vec![], 0, 1)), block(vec![], TerminatorKind::Return)], 0);
        assert_eq!(Interpreter::new(&p, AllocMap::default(), &table, Limits::default()).eval_to_scalar(&mir), Ok(int(expected, 8)));
    }
}
#[test]
fn integer_arithmetic_boundaries_match_width_and_signedness() {
    use super::operand::Value;
    let p = Provider::new();
    let table = Intrinsics::default();
    let ecx = Interpreter::new(&p, AllocMap::default(), &table, Limits::default());
    let signed_ty = p.tcx.tys.intern(TyKind::Int(Prim::I8));
    let unsigned_ty = p.tcx.tys.u8_;
    for a in 0..=255u128 {
        for b in [0, 1, 2, 63, 127, 128, 254, 255] {
            for (ty, is_signed) in [(signed_ty, true), (unsigned_ty, false)] {
                let lhs = Value::immediate(ty, Immediate::Scalar(int(a, 1)));
                let rhs = Value::immediate(ty, Immediate::Scalar(int(b, 1)));
                for op in [BinOp::AddWithOverflow, BinOp::SubWithOverflow, BinOp::MulWithOverflow] {
                    let (v, overflow) = if is_signed {
                        let (v, o) = match op {
                            BinOp::AddWithOverflow => (a as i8).overflowing_add(b as i8),
                            BinOp::SubWithOverflow => (a as i8).overflowing_sub(b as i8),
                            _ => (a as i8).overflowing_mul(b as i8),
                        };
                        (v as u8, o)
                    } else {
                        match op {
                            BinOp::AddWithOverflow => (a as u8).overflowing_add(b as u8),
                            BinOp::SubWithOverflow => (a as u8).overflowing_sub(b as u8),
                            _ => (a as u8).overflowing_mul(b as u8),
                        }
                    };
                    assert_eq!(ecx.binary(op, lhs, rhs, ty).unwrap(), Immediate::ScalarPair(int(v as u128, 1), int(overflow as u128, 1)));
                }
            }
        }
    }
}
#[test]
fn transmute_immediate_pair_and_padding() {
    use super::operand::Value;
    let p = Provider::new();
    let table = Intrinsics::default();
    let mut ecx = Interpreter::new(&p, AllocMap::default(), &table, Limits::default());
    let byte = p.tcx.tys.u8_;
    let pair = p.tcx.tys.intern(TyKind::Tuple(vec![byte, byte]));
    let u16_ = p.tcx.tys.intern(TyKind::Int(Prim::U16));
    let dest = ecx.allocate_place(u16_, MemoryKind::Stack).unwrap();
    let fields = p.layout_of(pair).unwrap().fields.clone();
    ecx.transmute(dest, Value::immediate(pair, Immediate::ScalarPair(int(0x12, 1), int(0x34, 1)))).unwrap();
    let expected = (0x12u128 << (fields[0] * 8)) | (0x34u128 << (fields[1] * 8));
    assert_eq!(ecx.scalar(Value::indirect(dest)).unwrap(), int(expected, 2));
    let pair = p.tcx.tys.intern(TyKind::Tuple(vec![byte, p.tcx.tys.u32_]));
    let u64_ = p.tcx.tys.u64_;
    let dest = ecx.allocate_place(u64_, MemoryKind::Stack).unwrap();
    ecx.transmute(dest, Value::immediate(pair, Immediate::ScalarPair(int(1, 1), int(2, 4)))).unwrap();
    assert_eq!(ecx.scalar(Value::indirect(dest)), Err(ConstEvalError::Ub("using uninitialized data")));
}
#[test]
fn storage_dead_reference_and_constant_index_bounds() {
    let p = Provider::new();
    let t = p.tcx.tys.u32_;
    let ptr = p.tcx.tys.intern(TyKind::Ptr(false, t));
    let deref = Place { local: Local(2), projection: vec![PlaceElem::Deref] };
    let mir = body(
        &[t, t, ptr],
        vec![block(
            vec![
                stmt(StatementKind::StorageLive(Local(1))),
                assign(1, Rvalue::Use(number(&p, t, 42))),
                assign(2, Rvalue::RawPtr(RawPtrKind::Const, local(1))),
                stmt(StatementKind::StorageDead(Local(1))),
                assign(0, Rvalue::Use(Operand::Copy(deref))),
            ],
            TerminatorKind::Return,
        )],
        0,
    );
    assert_eq!(run(&p, &mir), Err(ConstEvalError::Ub("pointer to deallocated allocation")));
    let array = p.tcx.tys.intern(TyKind::Array(t, 1));
    let index = Place { local: Local(1), projection: vec![PlaceElem::ConstantIndex { offset: 1, min_length: 1, from_end: false }] };
    let mir = body(
        &[t, array],
        vec![block(
            vec![
                assign(1, Rvalue::Aggregate(Box::new(AggregateKind::Array(t)), vec![number(&p, t, 1)])),
                assign(0, Rvalue::Use(Operand::Copy(index))),
            ],
            TerminatorKind::Return,
        )],
        0,
    );
    assert_eq!(run(&p, &mir), Err(ConstEvalError::Ub("out-of-bounds array index")));
}
#[test]
fn unevaluated_promoted_body_is_interned() {
    let mut p = Provider::new();
    let t = p.tcx.tys.u32_;
    let promoted = body(&[t], vec![block(vec![assign(0, Rvalue::Use(number(&p, t, 123)))], TerminatorKind::Return)], 0);
    let mut parent = body(&[t], vec![block(vec![], TerminatorKind::Return)], 0);
    parent.promoted.push(promoted);
    p.bodies.insert(DefId(60), parent);
    let op = Operand::Constant(Box::new(ConstOperand {
        span: Span::default(),
        user_ty: None,
        const_: Const::Unevaluated { def: DefId(60), args: vec![], promoted: Some(PromotedId(0)) },
    }));
    let mir = body(&[t], vec![block(vec![assign(0, Rvalue::Use(op))], TerminatorKind::Return)], 0);
    assert_eq!(run(&p, &mir), Ok(int(123, 4)));
}
#[test]
fn repeat_len_offsetof_and_subslice() {
    let p = Provider::new();
    let t = p.tcx.tys.u32_;
    let n = p.tcx.tys.usize_;
    let array = p.tcx.tys.intern(TyKind::Array(t, 5));
    let sub = Place { local: Local(1), projection: vec![PlaceElem::Subslice { from: 1, to: 1, from_end: true }] };
    let mir = body(
        &[n, array],
        vec![block(
            vec![assign(1, Rvalue::Repeat(number(&p, t, 7), Const::Val(ConstValue::Scalar(int(5, 8)), n))), assign(0, Rvalue::Len(sub))],
            TerminatorKind::Return,
        )],
        0,
    );
    assert_eq!(run(&p, &mir), Ok(int(3, 8)));
    let tuple = p.tcx.tys.intern(TyKind::Tuple(vec![p.tcx.tys.u8_, t]));
    let expected = p.layout_of(tuple).unwrap().fields[1];
    let mir = body(
        &[n],
        vec![block(
            vec![assign(0, Rvalue::NullaryOp(NullOp::OffsetOf(vec![(VariantIdx(0), FieldIdx(1))]), tuple))],
            TerminatorKind::Return,
        )],
        0,
    );
    assert_eq!(run(&p, &mir), Ok(int(expected as u128, 8)));
}
#[test]
fn reified_function_pointer_call_and_thin_pointer_aggregate() {
    let mut p = Provider::new();
    let t = p.tcx.tys.u32_;
    let fn_ty = p.tcx.tys.intern(TyKind::FnDef(DefId(70), vec![], crate::types::RegionArgsId::EMPTY));
    let fn_ptr = p.tcx.tys.intern(TyKind::FnPtr(vec![], t, crate::types::FnHeader::RUST, 0));
    p.bodies.insert(DefId(70), body(&[t], vec![block(vec![assign(0, Rvalue::Use(number(&p, t, 88)))], TerminatorKind::Return)], 0));
    let mut term = call(&p, 70, vec![], vec![], 0, 1);
    if let TerminatorKind::Call { func, .. } = &mut term {
        *func = copy(1);
    }
    let mir = body(
        &[t, fn_ptr],
        vec![
            block(
                vec![assign(
                    1,
                    Rvalue::Cast(
                        CastKind::PointerCoercion(PointerCoercion::ReifyFnPointer, CoercionSource::Implicit),
                        val(fn_ty, ConstValue::ZeroSized),
                        fn_ptr,
                    ),
                )],
                term,
            ),
            block(vec![], TerminatorKind::Return),
        ],
        0,
    );
    assert_eq!(run(&p, &mir), Ok(int(88, 4)));
    let ptr = p.tcx.tys.intern(TyKind::Ptr(false, t));
    let unit = p.tcx.tys.intern(TyKind::Tuple(vec![]));
    let mir = body(
        &[ptr],
        vec![block(
            vec![assign(
                0,
                Rvalue::Aggregate(
                    Box::new(AggregateKind::RawPtr(t, Mutability::Not)),
                    vec![val(ptr, ConstValue::Scalar(int(4, 8))), val(unit, ConstValue::ZeroSized)],
                ),
            )],
            TerminatorKind::Return,
        )],
        0,
    );
    assert_eq!(run(&p, &mir), Ok(int(4, 8)));
}
#[test]
fn numeric_intrinsic_overflow_rotation_and_exact_division() {
    let p = Provider::new();
    let u = p.tcx.tys.u8_;
    let i = p.tcx.tys.intern(TyKind::Int(Prim::I8));
    for (name, ty, a, b, expected) in [
        ("wrapping_add", u, 255, 1, 0),
        ("saturating_add", u, 255, 1, 255),
        ("saturating_sub", u, 0, 1, 0),
        ("saturating_add", i, 127, 1, 127),
        ("saturating_sub", i, 128, 1, 128),
        ("rotate_left", u, 0x81, 1, 3),
        ("rotate_right", u, 3, 1, 0x81),
        ("exact_div", u, 18, 3, 6),
    ] {
        let mut table = Intrinsics::default();
        table.register(DefId(80), name).unwrap();
        let mir = body(
            &[ty],
            vec![
                block(vec![], call(&p, 80, vec![ty], vec![number(&p, ty, a), number(&p, ty, b)], 0, 1)),
                block(vec![], TerminatorKind::Return),
            ],
            0,
        );
        assert_eq!(
            Interpreter::new(&p, AllocMap::default(), &table, Limits::default()).eval_to_scalar(&mir),
            Ok(int(expected, 1)),
            "{name}"
        );
    }
    for name in ["unchecked_add", "exact_div"] {
        let mut table = Intrinsics::default();
        table.register(DefId(80), name).unwrap();
        let mir = body(
            &[u],
            vec![
                block(vec![], call(&p, 80, vec![u], vec![number(&p, u, 255), number(&p, u, 2)], 0, 1)),
                block(vec![], TerminatorKind::Return),
            ],
            0,
        );
        assert!(Interpreter::new(&p, AllocMap::default(), &table, Limits::default()).eval_to_scalar(&mir).is_err());
    }
}
#[test]
fn copy_overlap_and_uninit_mask_propagation() {
    let p = Provider::new();
    let table = Intrinsics::default();
    let mut ecx = Interpreter::new(&p, AllocMap::default(), &table, Limits::default());
    let ptr = ecx.allocate(8, 8, MemoryKind::Stack).unwrap();
    ecx.write_scalar(ptr, int(0x030201, 4), 4, 1).unwrap();
    assert!(ecx.copy_bytes(ptr, add_offset(ptr, 1).unwrap(), 4, 1, true).is_err());
    ecx.copy_bytes(ptr, add_offset(ptr, 1).unwrap(), 4, 1, false).unwrap();
    assert_eq!(ecx.read_scalar(add_offset(ptr, 1).unwrap(), 4, 1), Ok(int(0x030201, 4)));
    ecx.copy_bytes(add_offset(ptr, 7).unwrap(), ptr, 1, 1, true).unwrap();
    assert_eq!(ecx.read_scalar(ptr, 1, 1), Err(ConstEvalError::Ub("using uninitialized data")));
}
#[test]
fn pointer_offset_and_unsigned_overflow() {
    use super::operand::Value;
    let p = Provider::new();
    let table = Intrinsics::default();
    let mut ecx = Interpreter::new(&p, AllocMap::default(), &table, Limits::default());
    let t = p.tcx.tys.u32_;
    let ptr_ty = p.tcx.tys.intern(TyKind::Ptr(false, t));
    let ptr = ecx.allocate(8, 4, MemoryKind::Stack).unwrap();
    let lhs = Value::immediate(ptr_ty, Immediate::Scalar(ptr));
    let count = Value::immediate(p.tcx.tys.usize_, Immediate::Scalar(int(2, 8)));
    assert_eq!(ecx.binary(BinOp::Offset, lhs, count, ptr_ty), Ok(Immediate::Scalar(add_offset(ptr, 8).unwrap())));
    let huge = Value::immediate(p.tcx.tys.usize_, Immediate::Scalar(int(u64::MAX as u128, 8)));
    assert!(ecx.binary(BinOp::Offset, lhs, huge, ptr_ty).is_err());
    let ptr_slot = ecx.allocate_place(ptr_ty, MemoryKind::Stack).unwrap();
    ecx.write(ptr_slot, lhs).unwrap();
    let out = ecx.allocate_place(p.tcx.tys.usize_, MemoryKind::Stack).unwrap();
    assert!(ecx.cast(CastKind::PointerExposeProvenance, Value::indirect(ptr_slot), out.ty, out).is_err());
    let other = p.tcx.tys.intern(TyKind::Ptr(false, p.tcx.tys.u8_));
    let out = ecx.allocate_place(other, MemoryKind::Stack).unwrap();
    ecx.cast(CastKind::PtrToPtr, lhs, other, out).unwrap();
    assert_eq!(ecx.scalar(Value::indirect(out)).unwrap(), ptr);
}
#[test]
fn heap_deallocate_and_make_global_rejections() {
    let p = Provider::new();
    let table = Intrinsics::default();
    let mut ecx = Interpreter::new(&p, AllocMap::default(), &table, Limits::default());
    let ptr = ecx.allocate(8, 8, MemoryKind::Heap(false)).unwrap();
    assert!(ecx.make_global(add_offset(ptr, 1).unwrap()).is_err());
    assert!(ecx.deallocate(ptr, 4, 8).is_err());
    assert!(ecx.deallocate(ptr, 8, 4).is_err());
    ecx.deallocate(ptr, 8, 8).unwrap();
    assert!(ecx.deallocate(ptr, 8, 8).is_err());
    assert!(ecx.make_global(ptr).is_err());
    let ptr = ecx.allocate(8, 8, MemoryKind::Stack).unwrap();
    assert!(ecx.make_global(ptr).is_err());
    let ptr = ecx.allocate(8, 8, MemoryKind::Heap(false)).unwrap();
    ecx.make_global(ptr).unwrap();
    assert!(ecx.deallocate(ptr, 8, 8).is_err());
}
#[test]
fn fallible_coroutine_nested_unknown_and_unresolved_array_layouts() {
    let p = Provider::new();
    let unit = p.tcx.tys.intern(TyKind::Tuple(vec![]));
    let sig = p.tcx.tys.intern(TyKind::FnPtr(vec![], unit, crate::types::FnHeader::RUST, 0));
    let owner = p.tcx.tys.intern(TyKind::FnDef(DefId(1), vec![], crate::types::RegionArgsId::EMPTY));
    let coro = p.tcx.tys.intern(TyKind::Closure(1, 1, sig, unit, owner));
    p.tcx.coroutines.insert((1, 1), ());
    assert!(matches!(p.layout_of(coro),Err(LayoutError::CoroutineNotAvailable(t)) if t==coro));
    let tuple = p.tcx.tys.intern(TyKind::Tuple(vec![coro]));
    assert!(matches!(p.layout_of(tuple), Err(LayoutError::CoroutineNotAvailable(_))));
    let param = p.tcx.tys.intern(TyKind::Param(0));
    let array = p.tcx.tys.mk_array(p.tcx.tys.u8_, param);
    assert!(matches!(p.layout_of(array), Err(LayoutError::Unknown(_))));
    let unknown = p.tcx.tys.intern(TyKind::Adt(DefId(999), vec![], crate::types::RegionArgsId::EMPTY));
    assert!(matches!(p.layout_of(unknown), Err(LayoutError::Unknown(_))));
}
#[test]
fn type_name_and_sized_layout_intrinsics() {
    let p = Provider::new();
    let t = p.tcx.tys.u32_;
    let n = p.tcx.tys.usize_;
    for (name, expected) in [("size_of", 4), ("align_of", 4), ("size_of_val", 4), ("min_align_of_val", 4), ("needs_drop", 0)] {
        let ret = if name == "needs_drop" { p.tcx.tys.bool_ } else { n };
        let mut table = Intrinsics::default();
        table.register(DefId(90), name).unwrap();
        let args =
            if name.ends_with("_val") { vec![val(p.tcx.tys.intern(TyKind::Ptr(false, t)), ConstValue::Scalar(int(4, 8)))] } else { vec![] };
        let mir = body(&[ret], vec![block(vec![], call(&p, 90, vec![t], args, 0, 1)), block(vec![], TerminatorKind::Return)], 0);
        assert_eq!(
            Interpreter::new(&p, AllocMap::default(), &table, Limits::default()).eval_to_scalar(&mir),
            Ok(int(expected, p.layout_of(ret).unwrap().size as u8))
        );
    }
    let ret = p.tcx.tys.intern(TyKind::Ref(false, p.tcx.tys.intern(TyKind::Str), crate::types::RegionId::ERASED));
    let mut table = Intrinsics::default();
    table.register(DefId(90), "type_name").unwrap();
    let mir = body(&[ret], vec![block(vec![], call(&p, 90, vec![t], vec![], 0, 1)), block(vec![], TerminatorKind::Return)], 0);
    let mut ecx = Interpreter::new(&p, AllocMap::default(), &table, Limits::default());
    let (id, _) = ecx.eval_to_allocation(&mir).unwrap();
    let ptr = ecx.read_scalar(Scalar::Ptr { provenance: CtfeProvenance::new(id), offset: 0 }, 8, 8).unwrap();
    let (id, _) = ptr_parts(ptr).unwrap();
    assert_eq!(&ecx.memory.get(id).unwrap().bytes, b"u32");
}
#[test]
fn function_pointer_allocation_survives_new_machine() {
    let mut p = Provider::new();
    let t = p.tcx.tys.u32_;
    let fn_ty = p.tcx.tys.intern(TyKind::FnDef(DefId(91), vec![], crate::types::RegionArgsId::EMPTY));
    let fn_ptr = p.tcx.tys.intern(TyKind::FnPtr(vec![], t, crate::types::FnHeader::RUST, 0));
    p.bodies.insert(DefId(91), body(&[t], vec![block(vec![assign(0, Rvalue::Use(number(&p, t, 91)))], TerminatorKind::Return)], 0));
    let mir = body(
        &[fn_ptr],
        vec![block(
            vec![assign(
                0,
                Rvalue::Cast(
                    CastKind::PointerCoercion(PointerCoercion::ReifyFnPointer, CoercionSource::Implicit),
                    val(fn_ty, ConstValue::ZeroSized),
                    fn_ptr,
                ),
            )],
            TerminatorKind::Return,
        )],
        0,
    );
    let table = Intrinsics::default();
    let mut ecx = Interpreter::new(&p, AllocMap::default(), &table, Limits::default());
    let ptr = ecx.eval_to_scalar(&mir).unwrap();
    let mut term = call(&p, 91, vec![], vec![], 0, 1);
    if let TerminatorKind::Call { func, .. } = &mut term {
        *func = val(fn_ptr, ConstValue::Scalar(ptr));
    }
    let mir = body(&[t], vec![block(vec![], term), block(vec![], TerminatorKind::Return)], 0);
    assert_eq!(Interpreter::new(&p, ecx.memory, &table, Limits::default()).eval_to_scalar(&mir), Ok(int(91, 4)));
}
#[test]
fn assertion_diagnostics_and_machine_reuse_after_error() {
    let p = Provider::new();
    let t = p.tcx.tys.u32_;
    let table = Intrinsics::default();
    let failed = body(
        &[t],
        vec![
            block(
                vec![],
                TerminatorKind::Assert {
                    cond: number(&p, p.tcx.tys.bool_, 0),
                    expected: true,
                    msg: AssertKind::BoundsCheck { len: number(&p, t, 3), index: number(&p, t, 9) },
                    target: BasicBlock(1),
                    unwind: UnwindAction::Unreachable,
                },
            ),
            block(vec![], TerminatorKind::Return),
        ],
        0,
    );
    let good = body(&[t], vec![block(vec![assign(0, Rvalue::Use(number(&p, t, 7)))], TerminatorKind::Return)], 0);
    let mut ecx = Interpreter::new(&p, AllocMap::default(), &table, Limits::default());
    assert_eq!(ecx.eval_to_scalar(&failed), Err(ConstEvalError::Panic("index out of bounds: the length is 3 but the index is 9".into())));
    assert_eq!(ecx.eval_to_scalar(&good), Ok(int(7, 4)));
}

#[test]
fn shared_reference_cast_preserves_permissions_without_freezing_owner() {
    let p = Provider::new();
    let t = p.tcx.tys.u32_;
    let reference = p.tcx.tys.intern(TyKind::Ref(false, t, crate::types::RegionId::ERASED));
    let raw = p.tcx.tys.intern(TyKind::Ptr(true, t));
    for write_shared in [false, true] {
        let write = Place { local: Local(if write_shared { 4 } else { 2 }), projection: vec![PlaceElem::Deref] };
        let mir = body(
            &[t, t, raw, reference, raw],
            vec![block(
                vec![
                    assign(1, Rvalue::Use(number(&p, t, 1))),
                    assign(2, Rvalue::RawPtr(RawPtrKind::Mut, local(1))),
                    assign(3, Rvalue::Ref(Region::ERASED, BorrowKind::Shared, local(1))),
                    assign(4, Rvalue::Cast(CastKind::PtrToPtr, copy(3), raw)),
                    stmt(StatementKind::Assign(write, Rvalue::Use(number(&p, t, 42)))),
                    assign(0, Rvalue::Use(copy(1))),
                ],
                TerminatorKind::Return,
            )],
            0,
        );
        assert_eq!(
            run(&p, &mir),
            if write_shared { Err(ConstEvalError::Ub("writing through an immutable pointer")) } else { Ok(int(42, 4)) }
        );
    }
}

#[test]
fn call_arguments_keep_owner_and_shared_permissions_separate() {
    let mut p = Provider::new();
    let t = p.tcx.tys.u32_;
    let reference = p.tcx.tys.intern(TyKind::Ref(false, t, crate::types::RegionId::ERASED));
    let raw = p.tcx.tys.intern(TyKind::Ptr(true, t));
    let deref = Place { local: Local(1), projection: vec![PlaceElem::Deref] };
    p.bodies.insert(
        DefId(110),
        body(
            &[t, raw],
            vec![block(
                vec![
                    stmt(StatementKind::Assign(deref.clone(), Rvalue::Use(number(&p, t, 42)))),
                    assign(0, Rvalue::Use(Operand::Copy(deref))),
                ],
                TerminatorKind::Return,
            )],
            1,
        ),
    );
    for argument in [2, 4] {
        let mir = body(
            &[t, t, raw, reference, raw],
            vec![
                block(
                    vec![
                        assign(1, Rvalue::Use(number(&p, t, 1))),
                        assign(2, Rvalue::RawPtr(RawPtrKind::Mut, local(1))),
                        assign(3, Rvalue::Ref(Region::ERASED, BorrowKind::Shared, local(1))),
                        assign(4, Rvalue::Cast(CastKind::PtrToPtr, copy(3), raw)),
                    ],
                    call(&p, 110, vec![], vec![copy(argument)], 0, 1),
                ),
                block(vec![], TerminatorKind::Return),
            ],
            0,
        );
        assert_eq!(
            run(&p, &mir),
            if argument == 2 { Ok(int(42, 4)) } else { Err(ConstEvalError::Ub("writing through an immutable pointer")) }
        );
    }
}

#[test]
fn typed_aggregate_argument_retags_only_destination() {
    use super::operand::Value;
    let p = Provider::new();
    let t = p.tcx.tys.u32_;
    let reference = p.tcx.tys.intern(TyKind::Ref(false, t, crate::types::RegionId::ERASED));
    let tuple = p.tcx.tys.intern(TyKind::Tuple(vec![reference]));
    let callee = body(&[t, tuple], vec![block(vec![assign(0, Rvalue::Use(number(&p, t, 0)))], TerminatorKind::Return)], 1);
    let table = Intrinsics::default();
    let mut ecx = Interpreter::new(&p, AllocMap::default(), &table, Limits::default());
    let owner = ecx.allocate(4, 4, MemoryKind::Stack).unwrap();
    let source = ecx.allocate_place(tuple, MemoryKind::Stack).unwrap();
    // A raw memory copy can supply reference bytes without a typed retag.
    ecx.write_scalar(ecx.field(source, 0).unwrap().ptr, owner, 8, 8).unwrap();
    ecx.push_frame(&callee, &[Value::indirect(source)], None).unwrap();
    let copied = ecx.field(ecx.local(Local(1)).unwrap(), 0).unwrap();
    let shared = ecx.read_scalar(copied.ptr, 8, 8).unwrap();
    assert_ne!(owner, shared);
    assert_eq!(ptr_parts(owner), ptr_parts(shared));
    assert_eq!(ecx.read_scalar(ecx.field(source, 0).unwrap().ptr, 8, 8).unwrap(), owner);
    ecx.write_scalar(owner, int(42, 4), 4, 4).unwrap();
    assert_eq!(ecx.write_scalar(shared, int(1, 4), 4, 4), Err(ConstEvalError::Ub("writing through an immutable pointer")));
}

#[test]
fn byte_copies_and_transmutes_preserve_permission_fragments() {
    use super::operand::Value;
    let p = Provider::new();
    let t = p.tcx.tys.u32_;
    let reference = p.tcx.tys.intern(TyKind::Ref(false, t, crate::types::RegionId::ERASED));
    let raw = p.tcx.tys.intern(TyKind::Ptr(true, t));
    let table = Intrinsics::default();
    let mut ecx = Interpreter::new(&p, AllocMap::default(), &table, Limits::default());
    let owner = ecx.allocate(4, 4, MemoryKind::Stack).unwrap();
    let source = ecx.allocate_place(reference, MemoryKind::Stack).unwrap();
    ecx.write(source, Value::immediate(reference, Immediate::Scalar(owner))).unwrap();
    let shared = ecx.read_scalar(source.ptr, 8, 8).unwrap();
    let raw_dest = ecx.allocate_place(raw, MemoryKind::Stack).unwrap();
    ecx.transmute(raw_dest, Value::indirect(source)).unwrap();
    assert_eq!(ecx.read_scalar(raw_dest.ptr, 8, 8).unwrap(), shared);
    let dest = ecx.allocate(8, 8, MemoryKind::Stack).unwrap();
    for i in 0..8 {
        ecx.copy_bytes(add_offset(raw_dest.ptr, i).unwrap(), add_offset(dest, i).unwrap(), 1, 1, true).unwrap();
    }
    let copied = ecx.read_scalar(dest, 8, 8).unwrap();
    assert_eq!(copied, shared);
    assert_eq!(ecx.copy_bytes(owner, copied, 4, 1, false), Err(ConstEvalError::Ub("writing through an immutable pointer")));
    assert_eq!(ecx.uninit(copied, 4), Err(ConstEvalError::Ub("writing through an immutable pointer")));
    ecx.copy_bytes(owner, copied, 0, 1, false).unwrap();
    ecx.write_scalar(owner, int(42, 4), 4, 4).unwrap();
    assert_eq!(ecx.read_scalar(copied, 4, 4).unwrap(), int(42, 4));
    // Equal addresses with different permissions cannot be spliced into one pointer.
    ecx.write_scalar(raw_dest.ptr, owner, 8, 8).unwrap();
    ecx.copy_bytes(raw_dest.ptr, dest, 4, 1, true).unwrap();
    assert_eq!(ecx.read_scalar(dest, 8, 8), Err(ConstEvalError::Unsupported("reading a partial pointer")));
}

#[test]
fn nonfreeze_shared_reference_remembers_origin_but_allows_writes() {
    use super::operand::Value;
    let mut p = Provider::new();
    let t = p.tcx.tys.u32_;
    let cell = adt(&mut p, 120, vec![vec![t]], false);
    p.freeze.insert(cell, Ok(false));
    p.unsafe_cells.push(cell);
    let reference = p.tcx.tys.intern(TyKind::Ref(false, cell, crate::types::RegionId::ERASED));
    let raw = p.tcx.tys.intern(TyKind::Ptr(true, t));
    let table = Intrinsics::default();
    let mut ecx = Interpreter::new(&p, AllocMap::default(), &table, Limits::default());
    let owner = ecx.allocate_place(cell, MemoryKind::Stack).unwrap();
    let dest = ecx.allocate_place(reference, MemoryKind::Stack).unwrap();
    ecx.write(dest, Value::immediate(reference, Immediate::Scalar(owner.ptr))).unwrap();
    let shared = ecx.read_scalar(dest.ptr, 8, 8).unwrap();
    assert!(matches!(shared, Scalar::Ptr { provenance, .. } if provenance.shared_ref() && !provenance.immutable()));
    let cast = ecx.allocate_place(raw, MemoryKind::Stack).unwrap();
    ecx.cast(CastKind::PtrToPtr, Value::indirect(dest), raw, cast).unwrap();
    let copied = ecx.read_scalar(cast.ptr, 8, 8).unwrap();
    ecx.write_scalar(copied, int(42, 4), 4, 4).unwrap();
    assert_eq!(ecx.read_scalar(owner.ptr, 4, 4).unwrap(), int(42, 4));
    // A shared borrow of the Freeze field tightens this derived pointer only.
    let field_ref = p.tcx.tys.intern(TyKind::Ref(false, t, crate::types::RegionId::ERASED));
    let field_dest = ecx.allocate_place(field_ref, MemoryKind::Stack).unwrap();
    ecx.write(field_dest, Value::immediate(field_ref, Immediate::Scalar(copied))).unwrap();
    let frozen = ecx.read_scalar(field_dest.ptr, 8, 8).unwrap();
    assert_eq!(ecx.write_scalar(frozen, int(1, 4), 4, 4), Err(ConstEvalError::Ub("writing through an immutable pointer")));
    ecx.write_scalar(copied, int(43, 4), 4, 4).unwrap();
}

#[test]
fn freeze_query_failure_propagates_from_reference_creation() {
    let mut p = Provider::new();
    let t = p.tcx.tys.u32_;
    p.freeze.insert(t, Err(LayoutError::Unknown(t)));
    let reference = p.tcx.tys.intern(TyKind::Ref(false, t, crate::types::RegionId::ERASED));
    let mir = body(
        &[t, t, reference],
        vec![block(
            vec![
                assign(1, Rvalue::Use(number(&p, t, 1))),
                assign(2, Rvalue::Ref(Region::ERASED, BorrowKind::Shared, local(1))),
                assign(0, Rvalue::Use(copy(1))),
            ],
            TerminatorKind::Return,
        )],
        0,
    );
    assert_eq!(run(&p, &mir), Err(ConstEvalError::Layout(LayoutError::Unknown(t))));
}

#[test]
fn interning_checks_each_incoming_pointer_permission() {
    let p = Provider::new();
    let table = Intrinsics::default();
    for owner_first in [false, true] {
        let mut ecx = Interpreter::new(&p, AllocMap::default(), &table, Limits::default());
        let target = ecx.allocate(4, 4, MemoryKind::Stack).unwrap();
        let (id, offset) = ptr_parts(target).unwrap();
        let shared = Scalar::Ptr { provenance: CtfeProvenance::new(id).as_immutable(), offset };
        let root = ecx.allocate(16, 8, MemoryKind::Stack).unwrap();
        ecx.write_scalar(root, if owner_first { target } else { shared }, 8, 8).unwrap();
        ecx.write_scalar(add_offset(root, 8).unwrap(), if owner_first { shared } else { target }, 8, 8).unwrap();
        assert_eq!(ecx.intern(ptr_parts(root).unwrap().0), Err(ConstEvalError::MutableReference));
        assert_eq!(ecx.memory.get(id).unwrap().mutability, Mutability::Mut);
        ecx.write_scalar(root, shared, 8, 8).unwrap();
        ecx.write_scalar(add_offset(root, 8).unwrap(), shared, 8, 8).unwrap();
        ecx.intern(ptr_parts(root).unwrap().0).unwrap();
        assert_eq!(ecx.memory.get(id).unwrap().mutability, Mutability::Not);
    }
}

#[test]
fn final_nonfreeze_reference_validates_active_variant() {
    use super::operand::Value;
    let mut p = Provider::new();
    let t = p.tcx.tys.u32_;
    let cell = adt(&mut p, 130, vec![vec![t]], false);
    let option = adt(&mut p, 140, vec![vec![], vec![cell]], true);
    p.freeze.insert(cell, Ok(false));
    p.freeze.insert(option, Ok(false));
    p.unsafe_cells.push(cell);
    let reference = p.tcx.tys.intern(TyKind::Ref(false, option, crate::types::RegionId::ERASED));
    let table = Intrinsics::default();
    for variant in [0, 1] {
        let mut ecx = Interpreter::new(&p, AllocMap::default(), &table, Limits::default());
        let value = ecx.allocate_place(option, MemoryKind::Stack).unwrap();
        if variant == 1 {
            let cell_value = ecx.field(MPlace { variant: Some(1), ..value }, 0).unwrap();
            let field = ecx.field(cell_value, 0).unwrap();
            ecx.write_scalar(field.ptr, int(42, 4), 4, 4).unwrap();
            // An owned UnsafeCell is valid in a constant's root value.
            ecx.validate_value(cell_value, &mut Vec::new()).unwrap();
        }
        ecx.set_discriminant(value, variant).unwrap();
        let root = ecx.allocate_place(reference, MemoryKind::Stack).unwrap();
        ecx.write(root, Value::immediate(reference, Immediate::Scalar(value.ptr))).unwrap();
        let ptr = ecx.read_scalar(root.ptr, 8, 8).unwrap();
        assert!(matches!(ptr, Scalar::Ptr { provenance, .. } if provenance.shared_ref() && !provenance.immutable()));
        let result = ecx.validate_value(root, &mut Vec::new());
        if variant == 0 {
            result.unwrap();
            ecx.intern(ptr_parts(root.ptr).unwrap().0).unwrap();
            assert_eq!(ecx.memory.get(ptr_parts(value.ptr).unwrap().0).unwrap().mutability, Mutability::Not);
        } else {
            assert_eq!(result, Err(ConstEvalError::Ub("UnsafeCell in read-only memory")));
        }
    }
}

#[test]
fn structural_adt_unsizing_preserves_shared_provenance_and_metadata() {
    use super::operand::Value;
    let mut p = Provider::new();
    let t = p.tcx.tys.u32_;
    let param = p.tcx.tys.intern(TyKind::Param(0));
    let param_ref = p.tcx.tys.intern(TyKind::Ref(false, param, crate::types::RegionId::ERASED));
    adt(&mut p, 150, vec![vec![param_ref]], false);
    p.tcx.adts.get_mut(&DefId(150)).unwrap().n_generics = 1;
    let array = p.tcx.tys.intern(TyKind::Array(t, 3));
    let slice = p.tcx.tys.intern(TyKind::Slice(t));
    let source_ty = p.tcx.tys.intern(TyKind::Adt(DefId(150), vec![array], crate::types::RegionArgsId::EMPTY));
    let target_ty = p.tcx.tys.intern(TyKind::Adt(DefId(150), vec![slice], crate::types::RegionArgsId::EMPTY));
    let table = Intrinsics::default();
    let mut ecx = Interpreter::new(&p, AllocMap::default(), &table, Limits::default());
    let data = ecx.allocate_place(array, MemoryKind::Stack).unwrap();
    let source = ecx.allocate_place(source_ty, MemoryKind::Stack).unwrap();
    let source_field = ecx.field(source, 0).unwrap();
    ecx.write(source_field, Value::immediate(source_field.ty, Immediate::Scalar(data.ptr))).unwrap();
    let before = ecx.scalar(Value::indirect(source_field)).unwrap();
    let dest = ecx.allocate_place(target_ty, MemoryKind::Stack).unwrap();
    ecx.unsize(dest, Value::indirect(source)).unwrap();
    let dest_field = ecx.field(dest, 0).unwrap();
    assert_eq!(ecx.immediate(Value::indirect(dest_field)).unwrap(), Immediate::ScalarPair(before, int(3, 8)));
    assert!(matches!(before, Scalar::Ptr { provenance, .. } if provenance.immutable() && provenance.shared_ref()));
}
