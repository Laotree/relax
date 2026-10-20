//! Disjoint indices (relaxed Rust D3) in the C-NLL4 conflict check. Included from check.rs as a
//! child module, so it extends the private checker state.
//!
//! A conflict between two borrows of elements of one array, slice or `Vec` (`&mut v[i]` while
//! `&mut v[j]` is live) is only a conflict when `i == j`. In a crate with relaxed Rust's
//! `disjoint-index` feature it is accepted when
//!  - the two borrows index the same container place (builtin `[T; N]` / `[T]` indexing, or std
//!    `Vec`'s `IndexMut<usize>`), everything before the index is the same place, and the earlier
//!    borrow dominates the later one; and
//!  - the indices are proven distinct (constants, `i` vs `i + c`, through single assignments in one
//!    straight-line run of blocks), or else the later index is compared at run time with the earlier
//!    one and an overlap panics as `<[T]>::get_disjoint_mut(..).unwrap()` does (`DisjointCheck`,
//!    lowered by the JIT from the verdict; SPEC-V keeps the body unverified until then).
//! Indices proven equal stay an error. Everything else (moves, drops, other places) is untouched.

use super::*;
use crate::borrowck::field_views::{find_feeds, DisjointRecord, Feed};

/// What one D3 acceptance is: the two index borrows and whether the indices are proven distinct.
pub(super) struct DisjointOutcome {
    pub record: DisjointRecord,
}

/// A symbolic `usize` value: a constant, or a local as of a version (0: its value when the
/// straight-line run of blocks is entered; k: after its k-th assignment in the run), plus an offset.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Sym { base: Option<(Local, u32)>, off: i128 }

/// The straight-line run of blocks the two borrows lie in: each block after the first has the
/// previous one as its only predecessor (no edge enters the run in its middle).
struct Run { blocks: Vec<usize> }
impl Run {
    fn pos(&self, at: Location) -> Option<(usize, usize)> {
        self.blocks.iter().position(|&b| b == at.block.0 as usize).map(|k| (k, at.statement_index))
    }
}

impl<'a> MirBorrowckCtxt<'a> {
    /// Relaxed D3: the conflict of the access at `at` (a borrow of `place`) with loan `li` vanishes when
    /// the two borrows are of distinct elements. None: not a disjoint-index conflict (or proven equal).
    pub(super) fn disjoint_outcome(&mut self, li: usize, place: &Place, access: ReadOrWrite, at: Location) -> Option<DisjointOutcome> {
        if !self.d3 { return None; }
        let kind2 = match access {
            Write(WriteKind::MutableBorrow(k)) | Reservation(WriteKind::MutableBorrow(k)) | Activation(WriteKind::MutableBorrow(k), _) | Read(ReadKind::Borrow(k)) => k,
            _ => return None,
        };
        let l1 = &self.borrows[li];
        if matches!(kind2, BorrowKind::Fake(_)) || matches!(l1.kind, BorrowKind::Fake(_)) { return None; }
        let at1 = l1.reserve_location;
        if at1 == at || !self.cfg.location_dominates(at1, at) { return None; }
        let both_mut = matches!(kind2, BorrowKind::Mut { .. }) && matches!(l1.kind, BorrowKind::Mut { .. });
        let l1_place = l1.borrowed_place.clone();
        // (index operand, where it is used, span of the borrow / call that indexes) per side
        let (first, second) = if let Some(x) = self.builtin_index_pair(&l1_place, at1, place, at) { x }
            else { self.vec_index_pair(li, place, at)? };
        let (s1, s2) = (self.sym_at(&first.0, first.1, second.1), self.sym_at(&second.0, second.1, first.1));
        let proven = match (s1, s2) {
            (Some(a), Some(b)) if a == b => return None, // the same element: the conflict stands
            (Some(a), Some(b)) => a.base == b.base && (a.off - b.off).unsigned_abs() < 1 << 31,
            _ => false,
        };
        let index1 = self.index_expr(first.2)?;
        let index2 = self.index_expr(second.2)?;
        Some(DisjointOutcome { record: DisjointRecord { owner: self.body.source.owner, first: index1, second: index2, proven, both_mut,
            code: if both_mut { "E0499" } else { "E0502" } } })
    }

    /// `base[i]` (loan) and `base[j]` (access) with the same `base` (builtin indexing of an array or
    /// slice): the first projections where the places differ are both indices.
    fn builtin_index_pair(&self, p1: &Place, at1: Location, p2: &Place, at2: Location) -> Option<((Operand, Location, Span), (Operand, Location, Span))> {
        if p1.local != p2.local { return None; }
        let k = p1.projection.iter().zip(&p2.projection).position(|(a, b)| a != b)?;
        let index = |e: &PlaceElem| match *e {
            PlaceElem::Index(l) => Some(Operand::Copy(Place::local(l))),
            PlaceElem::ConstantIndex { offset, from_end: false, .. } => Some(Operand::Constant(Box::new(ConstOperand { span: Span::default(), user_ty: None,
                const_: Const::Val(ConstValue::Scalar(Scalar::Int { bits: offset as u128, size: 8 }), self.tcx.tys.usize_) }))),
            _ => None,
        };
        let (i1, i2) = (index(&p1.projection[k])?, index(&p2.projection[k])?);
        let base = Place { local: p1.local, projection: p1.projection[..k].to_vec() };
        if !matches!(self.tcx.tys.kind(self.ty(&base)), TyKind::Array(..) | TyKind::Slice(_)) { return None; }
        Some(((i1, at1, self.span_at(at1)), (i2, at2, self.span_at(at2))))
    }

    /// `v[i]` and `v[j]` through std `Vec`'s `IndexMut<usize>` / `Index<usize>`: both borrows of the same
    /// `Vec` place are the receivers of an `index_mut` / `index` call.
    fn vec_index_pair(&mut self, li: usize, place: &Place, at: Location) -> Option<((Operand, Location, Span), (Operand, Location, Span))> {
        if self.borrows[li].borrowed_place != *place { return None; }
        let TyKind::Adt(d, ..) = self.tcx.tys.kind(self.ty(place)) else { return None };
        if self.prog.def_path(*d) != "core::vec::Vec" { return None; }
        let l2 = self.borrows.borrows_at_location(&at)?.iter().copied().find(|&i| self.borrows[i].borrowed_place == *place)?;
        let call = |this: &mut Self, loan: usize| -> Option<(Operand, Location, Span)> {
            let assigned = this.borrows[loan].assigned_place.clone();
            if !assigned.projection.is_empty() { return None; }
            if this.d3_feeds.is_none() { this.d3_feeds = Some(find_feeds(this.body)); }
            let Some(Feed::Call(bi, 0)) = this.d3_feeds.as_ref()?.get(&assigned.local).copied() else { return None };
            let block = &this.body.basic_blocks[bi];
            let term = block.terminator.as_ref()?;
            let TerminatorKind::Call { func: Operand::Constant(c), args, .. } = &term.kind else { return None };
            let Const::Val(_, fty) = &c.const_ else { return None };
            let TyKind::FnDef(m, targs, _) = this.tcx.tys.kind(*fty) else { return None };
            let tr = this.prog.def(*m).parent;
            let lang = |l| this.tcx.lang_items.get(l) == Some(tr);
            if !(lang(crate::lang_items::LangItem::IndexMut) || lang(crate::lang_items::LangItem::Index)) { return None; }
            // the index type: the trait's `Idx` (after `Self`)
            if this.tcx.tys.list(*targs).get(1).copied() != Some(this.tcx.tys.usize_) { return None; }
            Some((args.get(1)?.clone(), Location { block: BasicBlock(bi as u32), statement_index: block.statements.len() }, term.source_info.span))
        };
        let first = call(self, li)?;
        let second = call(self, l2)?;
        // the earlier indexing call runs before the later one on every path
        if !self.cfg.location_dominates(first.1, second.1) { return None; }
        Some((first, second))
    }

    /// The index expression a borrow / indexing call is written as: the outermost `a[i]` within
    /// `span`. None inside macro expansions (no source position to name, nor to lower a check at).
    fn index_expr(&self, span: Span) -> Option<Span> {
        let pf = &self.prog.files[span.file as usize];
        if span.hi > pf.src_len { return None; }
        let ast = &pf.ast;
        let trees = std::iter::once(ast).chain(ast.part.get().map(|p| &**p));
        let mut best: Option<Span> = None;
        for t in trees {
            for i in 0..t.exprs.len() {
                let e = t.expr(crate::ast::ExprId(t.base[0] + i as u32));
                if matches!(e.kind, crate::ast::ExprKind::Index(..)) && span.lo <= e.lo && e.hi <= span.hi
                    && best.map_or(true, |b| e.hi - e.lo > b.hi - b.lo) {
                    best = Some(Span { file: span.file, lo: e.lo, hi: e.hi });
                }
            }
        }
        best
    }

    /// The straight-line run of blocks that holds `a` and `b` (`a` dominates `b`), extended backwards
    /// over single-predecessor blocks.
    fn straight_run(&self, a: Location, b: Location) -> Option<Run> {
        let mut blocks = vec![b.block.0 as usize];
        let mut cur = b.block.0 as usize;
        // back from b to a: every block entered only from the previous one
        while cur != a.block.0 as usize {
            let [p] = self.cfg.predecessors[cur][..] else { return None };
            cur = p.0 as usize;
            if blocks.contains(&cur) { return None; }
            blocks.push(cur);
        }
        // and further back while the run has no side entry
        for _ in 0..64 {
            let [p] = self.cfg.predecessors[cur][..] else { break };
            if blocks.contains(&(p.0 as usize)) { break; }
            cur = p.0 as usize;
            blocks.push(cur);
        }
        blocks.reverse();
        Some(Run { blocks })
    }

    /// The symbolic value of `op` at `at`, within the run that also holds `other`.
    fn sym_at(&mut self, op: &Operand, at: Location, other: Location) -> Option<Sym> {
        let (a, b) = if self.cfg.location_dominates(at, other) { (at, other) } else { (other, at) };
        let run = self.straight_run(a, b)?;
        self.sym(&run, op, at, 0)
    }

    fn sym(&mut self, run: &Run, op: &Operand, at: Location, depth: u32) -> Option<Sym> {
        if depth > 16 { return None; }
        match op {
            Operand::Constant(c) => match &c.const_ {
                Const::Val(ConstValue::Scalar(Scalar::Int { bits, .. }), _) => Some(Sym { base: None, off: *bits as i128 }),
                _ => None,
            },
            Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => self.sym_local(run, p.local, at, depth),
            _ => None,
        }
    }

    /// `local` at `at`: its latest assignment in the run before `at`, followed through copies and
    /// additions / subtractions of constants (checked ones too: an overflow panics before the use).
    fn sym_local(&mut self, run: &Run, local: Local, at: Location, depth: u32) -> Option<Sym> {
        if self.address_taken(local) { return None; }
        let (k_at, s_at) = run.pos(at)?;
        // the run's statements before `at`, latest first
        let mut version = 0u32;
        let mut latest: Option<(Location, &Rvalue)> = None;
        let mut redefined_opaque = false;
        for (k, &b) in run.blocks.iter().enumerate().take(k_at + 1) {
            let block = &self.body.basic_blocks[b];
            let end = if k == k_at { s_at } else { block.statements.len() + 1 };
            for (si, st) in block.statements.iter().enumerate().take(end) {
                if let StatementKind::Assign(dst, rv) = &st.kind {
                    if dst.local == local {
                        version += 1;
                        if dst.projection.is_empty() { latest = Some((Location { block: BasicBlock(b as u32), statement_index: si }, rv)); redefined_opaque = false; }
                        else { latest = None; redefined_opaque = true; }
                    }
                }
            }
            // a call writing the local (its destination) before `at`
            if k < k_at || end > block.statements.len() {
                if let Some(Terminator { kind: TerminatorKind::Call { destination, .. }, .. }) = &block.terminator {
                    if destination.local == local { version += 1; latest = None; redefined_opaque = true; }
                }
            }
        }
        let opaque = Sym { base: Some((local, version)), off: 0 };
        let Some((d, rv)) = latest else { return if redefined_opaque || version == 0 { Some(opaque) } else { None } };
        let rv = rv.clone();
        let constant = |op: &Operand| match op {
            Operand::Constant(c) => match &c.const_ { Const::Val(ConstValue::Scalar(Scalar::Int { bits, .. }), _) => Some(*bits as i128), _ => None },
            _ => None,
        };
        let r = match &rv {
            Rvalue::Use(Operand::Copy(src) | Operand::Move(src)) if src.projection.len() == 1 && matches!(src.projection[0], PlaceElem::Field(f, _) if f.0 == 0) => {
                // `(_t.0)` of a checked `_t = AddWithOverflow(x, c)`
                self.sym_checked(run, src.local, d, depth)
            }
            Rvalue::Use(o) => self.sym(run, o, d, depth + 1),
            Rvalue::BinaryOp(BinOp::Add | BinOp::AddUnchecked, ops) => match (constant(&ops.0), constant(&ops.1)) {
                (_, Some(c)) => self.sym(run, &ops.0, d, depth + 1).map(|s| Sym { off: s.off + c, ..s }),
                (Some(c), _) => self.sym(run, &ops.1, d, depth + 1).map(|s| Sym { off: s.off + c, ..s }),
                _ => None,
            },
            Rvalue::BinaryOp(BinOp::Sub | BinOp::SubUnchecked, ops) => constant(&ops.1).and_then(|c| self.sym(run, &ops.0, d, depth + 1).map(|s| Sym { off: s.off - c, ..s })),
            _ => None,
        };
        Some(r.unwrap_or(opaque))
    }

    fn sym_checked(&mut self, run: &Run, tuple: Local, at: Location, depth: u32) -> Option<Sym> {
        if self.address_taken(tuple) { return None; }
        let (k_at, s_at) = run.pos(at)?;
        let mut def = None;
        for (k, &b) in run.blocks.iter().enumerate().take(k_at + 1) {
            let block = &self.body.basic_blocks[b];
            let end = if k == k_at { s_at } else { block.statements.len() };
            for (si, st) in block.statements.iter().enumerate().take(end) {
                if let StatementKind::Assign(dst, rv) = &st.kind {
                    if dst.local == tuple { def = Some((Location { block: BasicBlock(b as u32), statement_index: si }, rv.clone(), dst.projection.is_empty())); }
                }
            }
        }
        let (d, rv, whole) = def?;
        if !whole { return None; }
        let constant = |op: &Operand| match op {
            Operand::Constant(c) => match &c.const_ { Const::Val(ConstValue::Scalar(Scalar::Int { bits, .. }), _) => Some(*bits as i128), _ => None },
            _ => None,
        };
        match &rv {
            Rvalue::BinaryOp(BinOp::AddWithOverflow, ops) => match (constant(&ops.0), constant(&ops.1)) {
                (_, Some(c)) => self.sym(run, &ops.0, d, depth + 1).map(|s| Sym { off: s.off + c, ..s }),
                (Some(c), _) => self.sym(run, &ops.1, d, depth + 1).map(|s| Sym { off: s.off + c, ..s }),
                _ => None,
            },
            Rvalue::BinaryOp(BinOp::SubWithOverflow, ops) => constant(&ops.1).and_then(|c| self.sym(run, &ops.0, d, depth + 1).map(|s| Sym { off: s.off - c, ..s })),
            _ => None,
        }
    }

    /// Whether the body borrows or takes the address of `local` (or a part of it): its value can
    /// then change through a pointer.
    fn address_taken(&mut self, local: Local) -> bool {
        if self.d3_taken.is_none() {
            let mut taken = BitSet::new_empty(self.body.local_decls.len());
            for block in &self.body.basic_blocks {
                for st in &block.statements {
                    if let StatementKind::Assign(_, Rvalue::Ref(_, _, p) | Rvalue::RawPtr(_, p)) = &st.kind {
                        if !p.projection.first().is_some_and(|e| *e == PlaceElem::Deref) { taken.insert(p.local.0 as usize); }
                    }
                }
            }
            self.d3_taken = Some(taken);
        }
        self.d3_taken.as_ref().unwrap().contains(local.0 as usize)
    }
}
