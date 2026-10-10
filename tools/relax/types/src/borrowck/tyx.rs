//! Type queries the borrow checker needs, over `&Program` + `&Tcx` only (usable from a
//! background thread under FRONT_RW.read(); no Unit).

use crate::solve::SelectionResult;
use crate::fxhash::HashMap;
use crate::program::{DefId, DefKind, Program, NO_DEF};
use crate::tcx::Tcx;
use crate::types::{TyId, TyKind};
use std::cell::RefCell;

pub struct Tx<'a> {
    pub cx: crate::tcx::EvalCx<'a>,
    pub fv: std::rc::Rc<super::fv::SummaryCx>,
    pub prog: &'a Program,
    pub tcx: &'a Tcx,
    pub pending_traits: RefCell<Vec<(crate::solve::goal::Goal, DefId, crate::solve::goal::Certainty)>>,
    pub obligation_owner: std::cell::Cell<DefId>,
    copy_memo: RefCell<HashMap<TyId, bool>>,
    rawptr_memo: RefCell<HashMap<TyId, bool>>,
    lang_memo: RefCell<HashMap<&'static str, Option<DefId>>>,
    pub box_def: Option<DefId>,
    pub copy_trait: Option<DefId>,
    /// crate indices of core / alloc / std
    std_crates: Vec<u32>,
    /// polymorphic check of a generic fn: per generic param, bounded by Copy
    pub param_copy: RefCell<Vec<bool>>,
    /// checking a generic body polymorphically (typeck's picks there are less faithful)
    pub polymorphic: std::cell::Cell<bool>,
    /// closures built by the checker: Copy when every capture is (by value Copy, or a shared
    /// borrow) -- rustc's rule; Relax's own upvar types hide `&mut` captures as pointers
    pub closure_copy: RefCell<HashMap<(u32, u32), bool>>,
}

impl<'a> Tx<'a> {
    pub fn new(prog: &'a Program, tcx: &'a Tcx, env: crate::tcx::TypingEnv, state: &'a crate::tcx::EvalState) -> Tx<'a> {
        let mut std_crates = Vec::new();
        for (i, c) in prog.crates.iter().enumerate() {
            if matches!(prog.syms.str(c.name), "core" | "alloc" | "std") {
                std_crates.push(i as u32);
            }
        }
        let mut t = Tx {
            cx: crate::tcx::EvalCx::new(prog, env, state),
            fv: Default::default(),
            prog,
            tcx,
            pending_traits: RefCell::new(Vec::new()),
            obligation_owner: std::cell::Cell::new(NO_DEF),
            copy_memo: RefCell::new(HashMap::default()),
            rawptr_memo: RefCell::new(HashMap::default()),
            lang_memo: RefCell::new(HashMap::default()),
            box_def: None,
            copy_trait: tcx.copy_trait,
            std_crates,
            param_copy: RefCell::new(Vec::new()),
            polymorphic: std::cell::Cell::new(false),
            closure_copy: RefCell::new(HashMap::default()),
        };
        t.box_def = t.lang("boxed::Box");
        if t.copy_trait.is_none() {
            t.copy_trait = t.lang("marker::Copy");
        }
        t
    }

    /// For a polymorphic check of `def`: which of its generic params are bounded by Copy (the
    /// fn's own bounds and its impl's).
    pub fn reset_copy_memo(&self) {
        self.copy_memo.borrow_mut().clear();
    }

    /// Back to a monomorphic body (after a polymorphic one).
    pub fn reset_env(&self) {
        if self.polymorphic.get() {
            self.polymorphic.set(false);
            self.param_copy.borrow_mut().clear();
            self.copy_memo.borrow_mut().clear();
        }
    }

    pub fn set_generic_env(&self, def: DefId, n: usize) {
        let mut v = vec![false; n];
        let ct = match self.copy_trait {
            Some(c) => c,
            None => return,
        };
        let implies_copy = |td: DefId| td == ct || self.tcx.trait_closure.get(&td).map_or(false, |c| c.contains(&ct));
        let mark = |bs: &Vec<(u32, DefId, Vec<TyId>)>, v: &mut Vec<bool>| {
            for (p, td, _) in bs {
                if (*p as usize) < n && implies_copy(*td) {
                    v[*p as usize] = true;
                }
            }
        };
        if let Some(bs) = self.tcx.fn_trait_bounds(self.prog, def) {
            mark(bs, &mut v);
        }
        let parent = self.prog.def(def).parent;
        if let Some(bs) = self.tcx.impl_trait_bounds.get(&parent) {
            mark(bs, &mut v);
        }
        // the raw bounds (Copy itself is not in the tables above): the fn's environment
        // includes its impl's params
        let env = self.tcx.item_env(self.prog, def);
        let module = self.prog.def(def).scope;
        for (pi, file, path) in &env.bounds {
            if (*pi as usize) < n && !v[*pi as usize] {
                if let Some(td) = self.tcx.resolve_type_path_def(self.prog, *file, module, path) {
                    if implies_copy(td) {
                        v[*pi as usize] = true;
                    }
                }
            }
        }
        // a trait's Self: Copy when the trait has Copy as a supertrait
        if self.prog.def(parent).kind == DefKind::Trait && n > 0 && implies_copy(parent) {
            v[0] = true;
        }
        *self.param_copy.borrow_mut() = v;
        self.polymorphic.set(true);
        self.copy_memo.borrow_mut().clear();
    }

    pub fn kind(&self, t: TyId) -> TyKind {
        self.tcx.tys.kind(t).clone()
    }

    pub fn is_std_def(&self, d: DefId) -> bool {
        d != NO_DEF && self.std_crates.contains(&self.prog.def(d).krate)
    }

    /// `core::<path>` (also found through core's re-exports), "::"-separated.
    pub fn lang(&self, path: &'static str) -> Option<DefId> {
        if let Some(r) = self.lang_memo.borrow().get(path) {
            return *r;
        }
        let r = self.lang_uncached(path);
        self.lang_memo.borrow_mut().insert(path, r);
        r
    }

    fn lang_uncached(&self, path: &str) -> Option<DefId> {
        let prog = self.prog;
        let core = prog.syms.get("core")?;
        let mut cur = None;
        for c in 0..prog.crates.len() {
            if prog.crates[c].name == core {
                cur = Some(prog.mods[prog.crates[c].root_mod as usize].def);
            }
        }
        let mut cur = cur?;
        for p in path.split("::") {
            let s = prog.syms.get(p)?;
            cur = match prog.lookup_in_container(cur, s, true) {
                Some(d) => d,
                None => prog.lookup_in_container(cur, s, false)?,
            };
        }
        Some(cur)
    }

    pub fn ref_ty(&self, m: bool, t: TyId) -> TyId {
        self.tcx.tys.intern(TyKind::Ref(m, t, crate::types::RegionId::ERASED))
    }

    pub fn unit(&self) -> TyId {
        self.tcx.tys.unit
    }

    pub fn box_inner(&self, t: TyId) -> Option<TyId> {
        match self.tcx.tys.kind(t) {
            TyKind::Adt(d, a, _) if Some(*d) == self.box_def && !a.is_empty() => Some(a[0]),
            _ => None,
        }
    }

    /// The pointee of a builtin deref (references, raw pointers, Box).
    pub fn builtin_deref(&self, t: TyId) -> Option<TyId> {
        match self.tcx.tys.kind(t) {
            TyKind::Ref(_, i, _) | TyKind::Ptr(_, i) => Some(*i),
            _ => self.box_inner(t),
        }
    }

    pub fn adt_name(&self, d: DefId) -> &str {
        self.prog.name(d)
    }

    /// Field `fi` of variant `vi` of an ADT (or tuple element `fi`), substituted.
    pub fn field_ty(&self, t: TyId, vi: u32, fi: u32) -> Option<TyId> {
        match self.tcx.tys.kind(t) {
            TyKind::Tuple(v) => v.get(fi as usize).copied(),
            TyKind::Adt(d, args, _) => {
                let adt = self.tcx.adts.get(d)?;
                adt.variants.get(vi as usize)?.fields.get(fi as usize)?;
                Some(self.tcx.field_ty(self.prog, self.cx.typing_env, *d, vi, fi, args))
            }
            TyKind::Closure(_, _, _, up, _) => self.field_ty(*up, 0, fi),
            _ => None,
        }
    }

    /// Whether a value of `t` holds a raw pointer (`*T`, or a struct around one: NonNull,
    /// Vec's buffer, Rc, ...) inline or inside a Box: memory reached through it is not part of
    /// any place the checker sees, so a field view must treat such a field as the whole value.
    /// References end the walk (what they point to is a place of its own).
    pub fn holds_raw_ptr(&self, t: TyId) -> bool {
        self.holds_raw_ptr_d(t, 0)
    }

    /// Whether every raw pointer in a value of `t` sits inside a std type that owns the memory
    /// it points to (Vec<u32>, String, Box<Vec<T>>, Rc<RefCell<T>>, user structs of those): a
    /// `*mut T` field of a user type (pointing anywhere) is not.
    pub fn owning(&self, t: TyId) -> bool {
        self.owning_d(t, 0)
    }

    fn owning_d(&self, t: TyId, depth: u32) -> bool {
        if depth > 12 {
            return false;
        }
        if !self.holds_raw_ptr(t) {
            return true;
        }
        match self.tcx.tys.kind(t) {
            TyKind::Adt(d, args, _) if self.is_std_def(*d) => args.iter().all(|a| self.owning_d(*a, depth + 1)),
            TyKind::Adt(d, _, _) => {
                let nv = self.tcx.adts.get(d).map_or(0, |a| a.variants.len());
                (0..nv as u32).all(|vi| (0..self.n_fields(t, vi) as u32).all(|fi| self.field_ty(t, vi, fi).map_or(true, |ft| self.owning_d(ft, depth + 1))))
            }
            TyKind::Tuple(v) => v.iter().all(|a| self.owning_d(*a, depth + 1)),
            TyKind::Array(e, _) | TyKind::Slice(e) => self.owning_d(*e, depth + 1),
            TyKind::Closure(_, _, _, up, _) => self.owning_d(*up, depth + 1),
            _ => false,
        }
    }

    fn holds_raw_ptr_d(&self, t: TyId, depth: u32) -> bool {
        if depth > 12 {
            return true;
        }
        if let Some(b) = self.rawptr_memo.borrow().get(&t) {
            return *b;
        }
        // cycles (a recursive type through Box) answer false while being computed
        self.rawptr_memo.borrow_mut().insert(t, false);
        let r = match self.tcx.tys.kind(t) {
            TyKind::Ptr(..) => true,
            TyKind::Tuple(v) => v.iter().any(|x| self.holds_raw_ptr_d(*x, depth + 1)),
            TyKind::Array(e, _) | TyKind::Slice(e) => self.holds_raw_ptr_d(*e, depth + 1),
            TyKind::Closure(_, _, _, up, _) => self.holds_raw_ptr_d(*up, depth + 1),
            TyKind::Adt(d, _, _) => {
                if let Some(inner) = self.box_inner(t) {
                    self.holds_raw_ptr_d(inner, depth + 1)
                } else {
                    let nv = self.tcx.adts.get(d).map_or(0, |a| a.variants.len());
                    (0..nv as u32).any(|vi| (0..self.n_fields(t, vi) as u32).any(|fi| self.field_ty(t, vi, fi).map_or(false, |ft| self.holds_raw_ptr_d(ft, depth + 1))))
                }
            }
            _ => false,
        };
        self.rawptr_memo.borrow_mut().insert(t, r);
        r
    }

    pub fn n_fields(&self, t: TyId, vi: u32) -> usize {
        match self.tcx.tys.kind(t) {
            TyKind::Tuple(v) => v.len(),
            TyKind::Adt(d, _, _) => self.tcx.adts.get(d).and_then(|a| a.variants.get(vi as usize)).map_or(0, |v| v.fields.len()),
            _ => 0,
        }
    }

    pub fn field_name(&self, t: TyId, vi: u32, fi: u32) -> String {
        match self.tcx.tys.kind(t) {
            TyKind::Adt(d, _, _) => match self.tcx.adts.get(d).and_then(|a| a.variants.get(vi as usize)).and_then(|v| v.fields.get(fi as usize)) {
                Some(f) => self.prog.syms.str(f.name).to_string(),
                None => fi.to_string(),
            },
            _ => fi.to_string(),
        }
    }

    pub fn is_enum(&self, t: TyId) -> bool {
        matches!(self.tcx.tys.kind(t), TyKind::Adt(d, _, _) if self.tcx.adts.get(d).map_or(false, |a| a.is_enum))
    }

    pub fn is_union(&self, t: TyId) -> bool {
        matches!(self.tcx.tys.kind(t), TyKind::Adt(d, _, _) if self.tcx.adts.get(d).map_or(false, |a| a.is_union))
    }

    pub fn is_packed(&self, t: TyId) -> bool {
        matches!(self.tcx.tys.kind(t), TyKind::Adt(d, _, _) if self.tcx.adts.get(d).map_or(false, |a| a.repr_packed != 0))
    }

    /// Borrowck retains undecided properties as obligations in its explicit environment.
    pub fn select_trait(&self, td: crate::program::DefId, ty: TyId, args: &[TyId]) -> SelectionResult {
        let result = self.tcx.select_trait(&self.cx, td, ty, args);
        if let SelectionResult::Ambiguous(cause) = result {
            let goal = crate::solve::select::trait_goal(&self.cx, td, ty, args);
            let mut pending = self.pending_traits.borrow_mut();
            let owner = self.obligation_owner.get();
            if !pending.iter().any(|(g, d, _)| *g == goal && *d == owner) { pending.push((goal, owner, crate::solve::goal::Certainty::Maybe(cause))); }
        }
        result
    }

    pub fn resolve_trait_method(&self, def: DefId, args: &[TyId]) -> (DefId, Vec<TyId>) {
        match self.tcx.resolve_trait_method(&self.cx, self.prog, def, args) {
            crate::tcx::MethodResolution::Resolved(def, args) => (def, args),
            crate::tcx::MethodResolution::Ambiguous(goal, cause) => {
                self.pending_traits.borrow_mut().push((goal, self.obligation_owner.get(), crate::solve::goal::Certainty::Maybe(cause)));
                // Generic MIR keeps the trait call; the verdict retains its unresolved goal.
                (def, args.to_vec())
            }
            crate::tcx::MethodResolution::NoSolution(goal) => panic!("borrowck method has no solution: {goal:?}"),
        }
    }

    /// rustc type_is_copy_modulo_regions: only a proven Copy goal permits a copy.
    pub fn is_copy(&self, t: TyId) -> bool {
        if let Some(value) = self.copy_memo.borrow().get(&t) { return *value; }
        let result = match self.copy_trait {
            Some(td) => self.select_trait(td, t, &[]),
            None => return matches!(self.kind(t), TyKind::Int(_) | TyKind::Float(_) | TyKind::Bool | TyKind::Char | TyKind::Ref(false, _, _) | TyKind::Ptr(..) | TyKind::FnPtr(..) | TyKind::FnDef(..)),
        };
        let value = match result {
            SelectionResult::Ok(_) => true,
            SelectionResult::NoSolution => false,
            SelectionResult::Ambiguous(_) => return false,
        };
        self.copy_memo.borrow_mut().insert(t, value);
        value
    }


    pub fn has_drop_impl(&self, t: TyId) -> bool {
        matches!(self.tcx.tys.kind(t), TyKind::Adt(d, ..) if self.tcx.adt_destructor(*d).is_some())
    }

    pub fn needs_drop(&self, t: TyId) -> bool {
        self.tcx.needs_drop(self.prog, self.cx.typing_env, t)
    }

    /// Dynamically sized: str, slices, dyn, and structs / tuples ending in one.
    pub fn is_unsized(&self, t: TyId) -> bool {
        match self.kind(t) {
            TyKind::Str | TyKind::Slice(_) | TyKind::Dyn(..) => true,
            TyKind::Tuple(v) => v.last().map_or(false, |x| self.is_unsized(*x)),
            TyKind::Adt(d, _, _) => match self.tcx.adts.get(&d) {
                Some(a) if !a.is_enum && !a.is_union => {
                    let n = self.n_fields(t, 0);
                    n > 0 && self.field_ty(t, 0, n as u32 - 1).map_or(false, |ft| ft != t && self.is_unsized(ft))
                }
                _ => false,
            },
            _ => false,
        }
    }

    pub fn ty_str(&self, t: TyId) -> String {
        crate::typeck::ty_to_string(false, self.prog, self.tcx, t)
    }

    pub fn def_kind(&self, d: DefId) -> DefKind {
        self.prog.def(d).kind
    }

    pub fn crate_of(&self, d: DefId) -> u32 {
        self.prog.def(d).krate
    }
}
