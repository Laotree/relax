// ported from N:rustc_middle/src/ty/adjustment.rs and rustc_middle/src/ty/typeck_results.rs
// (adjustments, type_dependent_defs) @8d1a764; 1.97.1 has the same shapes.
//! The adjustments typeck applies to an expression: one list per node, replacing the five tables
//! (`coerce`, `reborrows`, `ov_derefs`, `index_derefs`, `call_derefs`) that each held a slice
//! of it. rustc stores `Vec<Adjustment>` on the adjusted expression; Relax keeps the key its
//! consumers already use (the node that consumes the value) and two sites per node:
//!
//! * `operand`: the autoderef of the node's operand -- the method receiver of a `MethodCall`,
//!   the base of an `Index`, the callee of a `Call`, the operand of a unary `*`.
//! * `value`: the node's own value converted to the type its context expects (a coercion site):
//!   `[Deref*, Borrow?, Coerce?]` in application order, as rustc's `coerce_borrowed_pointer`
//!   (derefs + autoref) followed by the pointer coercion.
use super::*;
use crate::types::TyList;

/// An overloaded `Deref::deref` step: the method and its `[Self]` arguments.
pub type OverloadedDeref = (DefId, TyList);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Adjust {
    /// One autoderef step: built-in for references and raw pointers (`None`), a call of
    /// `Deref::deref` / `deref_mut` otherwise (rustc `Adjust::Deref(Option<OverloadedDeref>)`).
    Deref(Option<OverloadedDeref>),
    /// The final (re)borrow of the adjusted value; `true` for `&mut` / `*mut`
    /// (rustc `Adjust::Borrow(AutoBorrow::Ref | RawPtr)`).
    Borrow(bool),
    /// `Adjust::NeverToAny` and `Adjust::Pointer(..)`; never `Coerce::DerefRef`, which is the
    /// `Deref` entries of the list.
    Coerce(Coerce),
}

#[derive(Clone, Debug, Default, PartialEq)]
pub struct Adjustments {
    pub operand: ThinVec<Adjust>,
    pub value: ThinVec<Adjust>,
}

impl Adjustments {
    fn is_empty(&self) -> bool { self.operand.is_empty() && self.value.is_empty() }
    pub fn heap_bytes(&self) -> usize { self.operand.heap_bytes() + self.value.heap_bytes() }
}

/// Whether the key addresses the `value` site (the legacy `DEREF_COERCE_KEY` bit) and its node.
fn split_key(key: u32) -> (u32, bool) {
    if key & DEREF_COERCE_KEY != 0 { (key & !DEREF_COERCE_KEY, true) } else { (key, false) }
}

impl Body {
    pub fn adjustments(&self, node: u32) -> Option<&Adjustments> { self.adjustments.get(&node) }

    /// The coercion applied to the value of `node` (rustc `Adjust::NeverToAny` / `Pointer`),
    /// or `DerefRef(n)` for n autoderef steps ending in a borrow (`&String -> &str`).
    pub fn coerce(&self, node: u32) -> Option<Coerce> {
        let value = &self.adjustments.get(&node)?.value;
        let mut derefs = 0;
        for a in value.iter() {
            match a {
                Adjust::Coerce(c) => return Some(*c),
                Adjust::Deref(_) => derefs += 1,
                Adjust::Borrow(_) => {}
            }
        }
        (derefs > 0).then_some(Coerce::DerefRef(derefs))
    }

    /// The mutability of the reborrow of the value of `node`, if it is reborrowed.
    pub fn reborrow(&self, node: u32) -> Option<bool> {
        self.adjustments.get(&node)?.value.iter().find_map(|a| match a { Adjust::Borrow(m) => Some(*m), _ => None })
    }

    /// The overloaded deref at `step` of the autoderef addressed by `key`: the node of a
    /// receiver / base / callee / `*` operand, or a node's coercion derefs (`node | DEREF_COERCE_KEY`).
    pub fn ov_deref(&self, key: u32, step: usize) -> Option<OverloadedDeref> {
        let (node, value) = split_key(key);
        let adj = self.adjustments.get(&node)?;
        match (if value { &adj.value } else { &adj.operand }).get(step) {
            Some(Adjust::Deref(Some(ov))) => Some(*ov),
            _ => None,
        }
    }

    /// Autoderef steps from an `Index` base to the indexed type.
    pub fn index_derefs(&self, node: u32) -> usize {
        self.adjustments.get(&node).map_or(0, |a| a.operand.len())
    }

    /// Autoderef steps from a `Call` callee to the callable (none recorded: `None`).
    pub fn call_derefs(&self, node: u32) -> Option<usize> {
        self.adjustments.get(&node).map(|a| a.operand.len()).filter(|&n| n > 0)
    }

    /// Every overloaded deref of the body: (key, step, call), keys as `ov_deref` takes them.
    pub fn overloaded_derefs(&self) -> impl Iterator<Item = (u32, usize, OverloadedDeref)> + '_ {
        self.adjustments.iter().flat_map(|(&node, adj)| {
            let operand = adj.operand.iter().enumerate().filter_map(move |(i, a)| match a { Adjust::Deref(Some(ov)) => Some((node, i, *ov)), _ => None });
            let value = adj.value.iter().enumerate().filter_map(move |(i, a)| match a { Adjust::Deref(Some(ov)) => Some((node | DEREF_COERCE_KEY, i, *ov)), _ => None });
            operand.chain(value)
        })
    }

    /// rustc `TypeckResults::type_dependent_def`: the method an expression calls without
    /// naming it -- a method call, an overloaded operator or index, or an overloaded unary `*`.
    pub fn type_dependent_def(&self, node: u32) -> Option<(DefId, TyList)> {
        if let Some(m) = self.methods.get(&node).or_else(|| self.binops.get(&node)) { return Some((m.def, m.args)); }
        if let Some(ov) = self.ov_index.get(&node) { return Some(*ov); }
        self.ov_deref(node, 0)
    }

    /// Mutable access to every list of overloaded-deref and coercion payload types (writeback,
    /// instantiation): the substitution applies to the arguments and the pointee types.
    pub fn adjust_payloads_mut(&mut self) -> impl Iterator<Item = &mut Adjust> {
        self.adjustments.values_mut().flat_map(|a| a.operand.iter_mut().chain(a.value.iter_mut()))
    }
}

impl Fcx<'_> {
    fn adj_mut(&mut self, node: u32) -> &mut Adjustments { self.b.adjustments.get_or_insert_with(node, Adjustments::default) }

    /// Apply the coercion to the value of `node` (the previous one is replaced).
    pub(super) fn set_coerce(&mut self, node: u32, coerce: Coerce) {
        debug_assert!(!matches!(coerce, Coerce::DerefRef(_)));
        let value = &mut self.adj_mut(node).value;
        value.retain(|a| !matches!(a, Adjust::Coerce(_)));
        value.push(Adjust::Coerce(coerce));
    }

    /// `derefs.len()` autoderef steps, then a borrow of mutability `mutable` (an existing borrow
    /// stays when `None`): `&&T -> &T`, `&String -> &str`.
    pub(super) fn set_deref_ref(&mut self, node: u32, derefs: Vec<Option<OverloadedDeref>>, mutable: Option<bool>) {
        let value = &mut self.adj_mut(node).value;
        let old = value.iter().find_map(|a| match a { Adjust::Borrow(m) => Some(*m), _ => None });
        value.clear();
        for d in derefs { value.push(Adjust::Deref(d)); }
        if let Some(m) = mutable.or(old) { value.push(Adjust::Borrow(m)); }
    }

    /// Reborrow the value of `node` (kept in front of a pointer coercion).
    pub(super) fn set_reborrow(&mut self, node: u32, mutable: bool) {
        let value = &mut self.adj_mut(node).value;
        match value.iter_mut().find(|a| matches!(a, Adjust::Borrow(_))) {
            Some(a) => *a = Adjust::Borrow(mutable),
            None => {
                let at = value.iter().position(|a| matches!(a, Adjust::Coerce(_))).unwrap_or(value.len());
                value.insert(at, Adjust::Borrow(mutable));
            }
        }
    }

    /// The `value` site of `node`, to restore after a coercion attempt fails.
    pub(super) fn save_value_adjustments(&self, node: u32) -> ThinVec<Adjust> {
        self.b.adjustments.get(&node).map_or_else(ThinVec::new, |a| a.value.clone())
    }

    pub(super) fn restore_value_adjustments(&mut self, node: u32, saved: ThinVec<Adjust>) {
        if saved.is_empty() {
            if let Some(adj) = self.b.adjustments.get_mut(&node) {
                adj.value.clear();
                if adj.is_empty() { self.b.adjustments.remove(&node); }
            }
        } else {
            self.adj_mut(node).value = saved;
        }
    }

    /// Give `to` the coercion of `from` (the arms of a `CoerceMany` share one adjustment).
    pub(super) fn copy_value_adjustments(&mut self, from: u32, to: u32) {
        let saved = self.save_value_adjustments(from);
        if !saved.is_empty() { self.adj_mut(to).value = saved; }
    }

    /// Record the step `step` of the operand autoderef of `node`: only overloaded steps are
    /// stored; a built-in step erases what an earlier attempt left there.
    pub(super) fn set_operand_deref(&mut self, node: u32, step: usize, deref: Option<OverloadedDeref>) {
        match deref {
            Some(_) => {
                let operand = &mut self.adj_mut(node).operand;
                while operand.len() <= step { operand.push(Adjust::Deref(None)); }
                operand[step] = Adjust::Deref(deref);
            }
            None => {
                if let Some(slot) = self.b.adjustments.get_mut(&node).and_then(|a| a.operand.get_mut(step)) { *slot = Adjust::Deref(None); }
            }
        }
    }

    /// The operand autoderef of `node` has exactly `n` steps.
    pub(super) fn set_operand_derefs(&mut self, node: u32, n: usize) {
        if n == 0 && !self.b.adjustments.contains_key(&node) { return; }
        let operand = &mut self.adj_mut(node).operand;
        operand.truncate(n);
        while operand.len() < n { operand.push(Adjust::Deref(None)); }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::typeck::solve::program;

    const PRELUDE: &str = "#![no_std]\n#[lang = \"sized\"] trait Sized {}\n#[lang = \"deref\"] trait Deref { type Target: ?Sized; fn deref(&self) -> &Self::Target; }\n";

    fn body_of(src: &str, name: &str) -> (Program, std::sync::Arc<Body>) {
        let (prog, tcx) = program(&format!("{PRELUDE}{src}"));
        let def = prog.defs.iter().enumerate().find(|(_, d)| prog.syms.str(d.name) == name).map(|(i, _)| DefId(i as u32)).unwrap();
        let body = tcx.typeck(&prog, def);
        assert!(body.errors.is_empty(), "{name}: {:?}", body.errors);
        (prog, body)
    }

    /// The tail expression of the fn body, whose coercion site is the return type.
    fn tail(prog: &Program, body: &Body) -> u32 {
        let ast = &prog.files[body.file as usize].ast;
        let block = ast.block(body.body.expect("a body"));
        let Some(crate::ast::Stmt::Expr(tail, false)) = ast.list(block.stmts).last().copied() else { panic!("no tail expression") };
        tail.0
    }

    #[test]
    fn deref_ref_is_derefs_then_borrow() {
        let (prog, body) = body_of("fn f<'a>(x: &'a &'a u8) -> &'a u8 { x }", "f");
        let e = tail(&prog, &body);
        assert_eq!(body.coerce(e), Some(Coerce::DerefRef(1)));
        assert_eq!(body.reborrow(e), Some(false));
        assert_eq!(body.adjustments(e).unwrap().value.as_slice(), &[Adjust::Deref(None), Adjust::Borrow(false)]);
    }

    #[test]
    fn overloaded_coercion_deref_keeps_its_call() {
        let (prog, body) = body_of("struct W(u8); impl Deref for W { type Target = u8; fn deref(&self) -> &u8 { &self.0 } } fn f(x: &W) -> &u8 { x }", "f");
        let e = tail(&prog, &body);
        assert_eq!(body.coerce(e), Some(Coerce::DerefRef(1)));
        let (method, args) = body.ov_deref(e | DEREF_COERCE_KEY, 0).expect("overloaded Deref::deref");
        assert_eq!(prog.name(method), "deref");
        assert!(!args.is_empty());
        assert!(body.ov_deref(e, 0).is_none(), "the operand site is a different list");
        assert_eq!(body.overloaded_derefs().count(), 1);
    }

    #[test]
    fn equal_type_mutable_reference_is_a_reborrow_without_coercion() {
        let (prog, body) = body_of("fn f(x: &mut u8) -> &mut u8 { x }", "f");
        let e = tail(&prog, &body);
        assert_eq!(body.coerce(e), None);
        assert_eq!(body.reborrow(e), Some(true));
    }

    #[test]
    fn unsize_keeps_the_borrow_in_front_of_the_pointer_coercion() {
        let (prog, body) = body_of("fn f(x: &[u8; 2]) -> &[u8] { x }", "f");
        let e = tail(&prog, &body);
        assert_eq!(body.coerce(e), Some(Coerce::Unsize));
        assert_eq!(body.adjustments(e).unwrap().value.as_slice(), &[Adjust::Borrow(false), Adjust::Coerce(Coerce::Unsize)]);
    }

    #[test]
    fn unadjusted_expression_has_no_entry() {
        let (prog, body) = body_of("fn f(x: u8) -> u8 { x }", "f");
        let e = tail(&prog, &body);
        assert!(body.adjustments(e).is_none());
        assert_eq!((body.coerce(e), body.reborrow(e)), (None, None));
    }

    #[test]
    fn index_and_call_operand_derefs_are_counted() {
        let (_, body) = body_of("fn f(v: &&[u8], n: usize) -> u8 { v[n] }", "f");
        let index = body.adjustments.iter().find(|(_, a)| !a.operand.is_empty()).expect("an indexed base");
        assert_eq!(body.index_derefs(*index.0), 2);
        let (_, body) = body_of("fn g(f: &fn() -> u8) -> u8 { f() }", "g");
        let call = body.adjustments.iter().find(|(_, a)| !a.operand.is_empty()).expect("a callee");
        assert_eq!(body.call_derefs(*call.0), Some(1));
        assert_eq!(body.index_derefs(u32::MAX), 0);
    }

    #[test]
    fn failed_coercion_leaves_no_adjustment() {
        // `x` is first tried against the expected `&u8` (a deref coercion fails to find one),
        // then reported: the speculative entry must not stay behind
        let (prog, tcx) = program(&format!("{PRELUDE}fn f(x: &u16) -> &u8 {{ x }}"));
        let def = prog.defs.iter().enumerate().find(|(_, d)| prog.syms.str(d.name) == "f").map(|(i, _)| DefId(i as u32)).unwrap();
        let body = tcx.typeck(&prog, def);
        assert!(!body.errors.is_empty());
        assert!(body.adjustments.iter().all(|(_, a)| a.value.is_empty()), "{:?}", body.adjustments);
    }
}
