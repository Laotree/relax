//! Feature gates of a checked crate on a stable compiler (rustc 1.97.1): E0658 for unstable
//! syntax and attributes used without `#![feature(..)]` (rustc_ast_passes/src/feature_gate.rs
//! `PostExpansionVisitor`, rustc_feature builtin_attrs.rs, the `cfg` gates of
//! rustc_attr_parsing/src/attributes/cfg.rs), E0554 (`#![feature]` on a stable compiler), E0557
//! (a removed feature), E0734 (stability attributes outside the standard library).
//!
//! A check-time diagnostic only: `check_crate` runs for the crates whose errors are reported
//! (compiler/src/check.rs) and for no other; std itself uses features and is never walked.
//! The walk follows rustc's: a node whose `cfg` is false is not visited, `cfg_attr` is expanded
//! first, and what a macro expansion wrote is not judged (an expansion's tokens carry no
//! `allow_internal_unstable` information, so only source-written tokens are).

use crate::ast::*;
use crate::cfg::{self, Src};
use crate::features::{Features, GATED_ATTRS, GATED_CFGS};
use crate::lexer::T;
use crate::program::{DefKind, Program};

/// Where an item sits (rustc's `AssocCtxt` / foreign items).
#[derive(Clone, Copy, PartialEq, Eq)]
enum Ctx {
    Free,
    Trait,
    Impl,
    Foreign,
}

pub fn check_crate(prog: &Program, krate: u32) -> Vec<String> {
    let info = &prog.crates[krate as usize];
    let feats = info.features(prog);
    let root_file = prog.mods[info.root_mod as usize].file;
    let mut w = Gates::new(prog, krate, root_file, feats);
    w.crate_features();
    w.root_attrs();
    let pf = &prog.files[root_file as usize];
    let items: Vec<ItemId> = pf.ast.root_items.iter().copied().collect();
    w.items(&items, Ctx::Free);
    w.errors
}

struct Gates<'a> {
    prog: &'a Program,
    krate: u32,
    file: u32,
    pf: &'a crate::parser::ParsedFile,
    ast: &'a Ast,
    src: Src<'a>,
    cfg: &'a cfg::CfgSet,
    feats: &'a Features,
    /// the innermost position recorded so far (types and patterns keep none of their own)
    cur_pos: u32,
    errors: Vec<String>,
}

impl<'a> Gates<'a> {
    fn new(prog: &'a Program, krate: u32, file: u32, feats: &'a Features) -> Gates<'a> {
        let pf = &*prog.files[file as usize];
        Gates { prog, krate, file, pf, ast: &pf.ast, src: prog.src(file), cfg: &prog.crates[krate as usize].cfg, feats, cur_pos: 0, errors: Vec::new() }
    }

    /// A walker over another file of the crate (an out-of-line module), sharing nothing.
    fn in_file(&self, file: u32) -> Gates<'a> {
        Gates::new(self.prog, self.krate, file, self.feats)
    }

    fn is_source(&self, pos: u32) -> bool {
        pos < self.pf.src_len
    }

    fn tok_pos(&self, i: usize) -> u32 {
        self.src.tok(i).lo
    }

    fn tok_is(&self, i: usize, s: &[u8]) -> bool {
        cfg::tok_str(self.src, i) == s
    }

    /// rustc `gate!`: E0658 unless the crate enabled `feature`.
    fn gate(&mut self, feature: &str, pos: u32, msg: &str) {
        if self.feats.has(feature) || !self.is_source(pos) {
            return;
        }
        self.errors.push(self.prog.record_error(self.file, pos, "typeck", format!("E0658: {}", msg)));
    }

    fn uncoded(&mut self, pos: u32, msg: &str) {
        if !self.is_source(pos) { return; }
        self.errors.push(self.prog.record_uncoded_error(self.file, pos, "typeck", msg.to_string()));
    }

    fn coded(&mut self, code: &str, pos: u32, msg: &str) {
        if !self.is_source(pos) { return; }
        self.errors.push(self.prog.record_error(self.file, pos, "typeck", format!("{}: {}", code, msg)));
    }

    // ---------------------------------------------------------------- the crate

    /// rustc_expand config.rs `features` (E0557) and feature_gate.rs `maybe_stage_features`
    /// (E0554: this is a stable compiler).
    fn crate_features(&mut self) {
        let Some(first) = self.feats.first_attr else { return };
        let removed: Vec<(u32, String)> = self.feats.declared.iter().filter(|d| d.removed).map(|d| (d.pos, d.name.clone())).collect();
        for (pos, name) in removed {
            self.coded("E0557", pos, &format!("feature has been removed: `{}`", name));
        }
        if self.feats.declared.iter().any(|d| !d.removed) || !self.feats.declared.is_empty() {
            self.coded("E0554", first, "`#![feature]` may not be used on the stable release channel");
        }
    }

    fn root_attrs(&mut self) {
        let attrs: Vec<Attr> = self.ast.root_attrs.iter().copied().collect();
        self.attr_list(&attrs);
    }

    // ---------------------------------------------------------------- attributes

    /// The attributes of a node: `cfg_attr` expanded (its predicate's cfg gates checked), the
    /// node's `cfg` predicates gated and judged. None: the node is cfg'd out (rustc strips it
    /// before the feature-gate walk, so its other attributes are never looked at).
    fn attrs(&mut self, list: List<Attr>) -> Option<Vec<Attr>> {
        if list.is_empty() { return Some(Vec::new()); }
        let raw: Vec<Attr> = self.ast.list(list).to_vec();
        self.attr_list(&raw)
    }

    fn attr_list(&mut self, raw: &[Attr]) -> Option<Vec<Attr>> {
        let mut flat = Vec::with_capacity(raw.len());
        self.expand(raw, &mut flat);
        let mut active = true;
        for a in &flat {
            if self.attr_is(a, b"cfg") {
                self.cfg_gates(a.toks.lo as usize + 2, a.toks.hi as usize - 1);
                if !cfg::active(self.src, std::slice::from_ref(a), self.cfg) { active = false; }
            }
        }
        if !active { return None; }
        for a in &flat { self.check_attr(a); }
        Some(flat)
    }

    /// `cfg_attr(pred, attrs)` expanded, checking `pred`'s cfg gates on the way.
    fn expand(&mut self, raw: &[Attr], out: &mut Vec<Attr>) {
        for a in raw {
            let lo = a.toks.lo as usize;
            let hi = a.toks.hi as usize;
            if hi > lo + 2 && self.attr_is(a, b"cfg_attr") && self.src.tok(lo + 1).kind == T::OpenParen {
                let end = cfg::cfg_attr_pred_end(self.src, a);
                self.cfg_gates(lo + 2, end);
                if cfg::cfg_attr_holds(self.src, a, self.cfg) {
                    let parts = cfg::cfg_attr_parts(self.src, a, end);
                    self.expand(&parts, out);
                }
            } else {
                out.push(*a);
            }
        }
    }

    fn attr_is(&self, a: &Attr, name: &[u8]) -> bool {
        let lo = a.toks.lo as usize;
        a.toks.hi as usize > lo && self.tok_is(lo, name)
    }

    /// rustc_attr_parsing cfg.rs `try_gate_cfg` over the predicate in tokens [lo, hi): a gated
    /// name (`cfg(version)`, `cfg(ub_checks)`, ..) and the compact `target(..)` form.
    fn cfg_gates(&mut self, lo: usize, hi: usize) {
        let mut i = lo;
        while i < hi {
            let t = self.src.tok(i);
            if t.kind == T::Ident {
                let name = String::from_utf8_lossy(cfg::tok_str(self.src, i)).into_owned();
                let call = i + 1 < hi && self.src.tok(i + 1).kind == T::OpenParen;
                let pos = t.lo;
                if call && name == "target" {
                    self.gate("cfg_target_compact", pos, "compact `cfg(target(..))` is experimental and subject to change");
                } else if !call || name == "version" {
                    if let Some(&(cfg_name, feature)) = GATED_CFGS.iter().find(|(n, _)| *n == name) {
                        self.gate(feature, pos, &format!("`cfg({})` is experimental and subject to change", cfg_name));
                    }
                }
            }
            i += 1;
        }
    }

    /// feature_gate.rs `visit_attribute` and the stability-attribute check E0734.
    fn check_attr(&mut self, a: &Attr) {
        let (lo, hi) = (a.toks.lo as usize, a.toks.hi as usize);
        if hi <= lo { return; }
        let wrapped = self.tok_is(lo, b"unsafe") && hi > lo + 1 && self.src.tok(lo + 1).kind == T::OpenParen;
        let first = if wrapped { lo + 2 } else { lo };
        if first >= hi || !matches!(self.src.tok(first).kind, T::Ident | T::KwBox | T::KwTry) { return; }
        // a single-segment name: `name`, `name(..)` or `name = ..`
        if first + 1 < hi && self.src.tok(first + 1).kind == T::PathSep { return; }
        let name = String::from_utf8_lossy(cfg::tok_str(self.src, first)).into_owned();
        let pos = self.tok_pos(lo);
        if let Ok(i) = GATED_ATTRS.binary_search_by(|(n, _, _)| (*n).cmp(name.as_str())) {
            let (_, feature, msg) = GATED_ATTRS[i];
            self.gate(feature, pos, msg);
        }
        match name.as_str() {
            "stable" | "unstable" | "rustc_const_stable" | "rustc_const_unstable" | "rustc_default_body_unstable"
            | "unstable_feature_bound" | "unstable_removed" | "rustc_allow_const_fn_unstable" | "allow_internal_unstable" => {
                if !self.feats.has("staged_api") && name != "allow_internal_unstable" && name != "rustc_allow_const_fn_unstable" {
                    self.coded("E0734", pos, "stability attributes may not be used outside of the standard library");
                }
            }
            "doc" => self.doc_gates(first + 1, hi, pos),
            "used" => self.used_gates(first + 1, hi, pos),
            _ => {}
        }
    }

    /// The top-level items of the parenthesized list opening at token `open` (as ranges).
    fn list_items(&self, open: usize, hi: usize) -> Vec<(usize, usize)> {
        let mut out = Vec::new();
        if open >= hi || self.src.tok(open).kind != T::OpenParen { return out; }
        let mut depth = 0i32;
        let mut start = open + 1;
        let mut i = open;
        while i < hi {
            match self.src.tok(i).kind {
                T::OpenParen | T::OpenBracket | T::OpenBrace => depth += 1,
                T::CloseParen | T::CloseBracket | T::CloseBrace => {
                    depth -= 1;
                    if depth == 0 {
                        if i > start { out.push((start, i)); }
                        break;
                    }
                }
                T::Comma if depth == 1 => {
                    if i > start { out.push((start, i)); }
                    start = i + 1;
                }
                _ => {}
            }
            i += 1;
        }
        out
    }

    /// The unstable flavors of `#[doc(..)]` (feature_gate.rs `gate_doc`).
    fn doc_gates(&mut self, open: usize, hi: usize, pos: u32) {
        for (lo, _) in self.list_items(open, hi) {
            let name = String::from_utf8_lossy(cfg::tok_str(self.src, lo)).into_owned();
            let (feature, how) = match name.as_str() {
                "cfg" | "auto_cfg" => ("doc_cfg", "experimental"),
                "masked" => ("doc_masked", "experimental"),
                "notable_trait" => ("doc_notable_trait", "experimental"),
                "attribute" | "keyword" | "fake_variadic" | "search_unbox" => ("rustdoc_internals", "meant for internal use only"),
                _ => continue,
            };
            self.gate(feature, pos, &format!("`#[doc({})]` is {}", name, how));
        }
    }

    /// `#[used(linker)]` / `#[used(compiler)]` (rustc_attr_parsing attributes/codegen_attrs.rs).
    fn used_gates(&mut self, open: usize, hi: usize, pos: u32) {
        for (lo, _) in self.list_items(open, hi) {
            let name = String::from_utf8_lossy(cfg::tok_str(self.src, lo)).into_owned();
            if matches!(name.as_str(), "linker" | "compiler") {
                self.gate("used_with_arg", pos, &format!("`#[used({})]` is currently unstable", name));
            }
        }
    }

    // ---------------------------------------------------------------- items

    fn items(&mut self, items: &[ItemId], ctx: Ctx) {
        for &it in items { self.item(it, ctx); }
    }

    fn item(&mut self, id: ItemId, ctx: Ctx) {
        let ast = self.ast;
        let item = *ast.item(id);
        let Some(attrs) = self.attrs(item.attrs) else { return };
        let pos = item.lo;
        let outer = std::mem::replace(&mut self.cur_pos, pos);
        self.item_kind(id, &item, &attrs, ctx);
        self.cur_pos = outer;
    }

    fn item_kind(&mut self, id: ItemId, item: &Item, attrs: &[Attr], ctx: Ctx) {
        let ast = self.ast;
        let pos = item.lo;
        match item.kind {
            ItemKind::Use(_) | ItemKind::ExternCrate(_) | ItemKind::MacroRules(_) | ItemKind::Mac(_) => {}
            ItemKind::Fn(sig, _, _) => {
                let sig = *ast.fn_sig(sig);
                if sig.variadic && ctx != Ctx::Foreign {
                    self.gate("c_variadic", pos, "C-variadic functions are unstable");
                }
                if ctx == Ctx::Foreign { self.llvm_link_name(attrs, pos); }
                self.fn_sig(&sig);
            }
            ItemKind::Struct(r) => {
                let s = *ast.row(r);
                self.repr_simd(attrs);
                self.generics(&s.generics);
                self.variant_data(&s.data);
            }
            ItemKind::Union(r) => {
                let u = *ast.row(r);
                self.repr_simd(attrs);
                self.generics(&u.generics);
                self.fields(u.fields);
            }
            ItemKind::Enum(r) => {
                let e = *ast.row(r);
                self.repr_simd(attrs);
                self.generics(&e.generics);
                for v in ast.list(e.variants).to_vec() {
                    let Some(_) = self.attrs(v.attrs) else { continue };
                    self.variant_data(&v.data);
                    if let Some(d) = v.disc { self.expr(d); }
                }
            }
            ItemKind::TypeAlias(r) => {
                let t = *ast.row(r);
                self.generics(&t.generics);
                self.bounds(t.bounds);
                if ctx == Ctx::Foreign {
                    self.gate("extern_types", pos, "extern types are experimental");
                }
                if let Some(ty) = t.ty {
                    if ctx == Ctx::Trait {
                        self.gate("associated_type_defaults", pos, "associated type defaults are unstable");
                    }
                    match ctx {
                        Ctx::Free => self.impl_trait_in_alias(ty, false),
                        Ctx::Trait | Ctx::Impl => self.impl_trait_in_alias(ty, true),
                        Ctx::Foreign => {}
                    }
                    self.ty(ty);
                }
            }
            ItemKind::Const(ty, _) => {
                // (the initializer is a body owner: walked with the bodies)
                if let Some(t) = ty.get() { self.ty(t); }
            }
            ItemKind::Static(_, ty, _) => self.ty(ty),
            ItemKind::Trait(r) => {
                let t = *ast.row(r);
                if t.auto { self.gate("auto_traits", pos, "auto traits are experimental and possibly buggy"); }
                self.generics(&t.generics);
                self.bounds(t.supers);
                let items = ast.list(t.items).to_vec();
                self.items(&items, Ctx::Trait);
            }
            ItemKind::TraitAlias(r) => {
                let t = *ast.row(r);
                self.gate("trait_alias", pos, "trait aliases are experimental");
                self.generics(&t.generics);
                self.bounds(t.bounds);
            }
            ItemKind::Impl(r) => {
                let im = *ast.row(r);
                if im.negative { self.gate("negative_impls", pos, "negative impls are experimental"); }
                self.generics(&im.generics);
                if let Some(p) = im.trait_ { self.path(&p); }
                self.ty(im.self_ty);
                let items = ast.list(im.items).to_vec();
                self.items(&items, Ctx::Impl);
            }
            ItemKind::Mod(Some(list)) => {
                let items = ast.list(list).to_vec();
                self.items(&items, Ctx::Free);
            }
            ItemKind::Mod(None) => {
                let Some(&d) = self.prog.item_defs.get(&(self.file, id.0)) else { return };
                let def = self.prog.def(d);
                if def.kind != DefKind::Mod { return; }
                let file = self.prog.mods[def.sub as usize].file;
                if file == self.file { return; }
                let mut sub = self.in_file(file);
                sub.root_attrs();
                let items: Vec<ItemId> = sub.ast.root_items.iter().copied().collect();
                sub.items(&items, Ctx::Free);
                self.errors.append(&mut sub.errors);
            }
            ItemKind::ForeignMod(r) => {
                let f = *ast.row(r);
                let items = ast.list(f.items).to_vec();
                self.items(&items, Ctx::Foreign);
            }
        }
    }

    /// `#[repr(simd)]` on a struct, enum or union.
    fn repr_simd(&mut self, attrs: &[Attr]) {
        for a in attrs {
            if !self.attr_is(a, b"repr") { continue; }
            let (lo, hi) = (a.toks.lo as usize, a.toks.hi as usize);
            for (i, _) in self.list_items(lo + 1, hi) {
                if self.tok_is(i, b"simd") {
                    let pos = self.tok_pos(lo);
                    self.gate("repr_simd", pos, "SIMD types are experimental and possibly buggy");
                }
            }
        }
    }

    /// A foreign fn or static linking to `llvm.*` (`#[link_name = "llvm.x"]`).
    fn llvm_link_name(&mut self, attrs: &[Attr], pos: u32) {
        for a in attrs {
            if !self.attr_is(a, b"link_name") { continue; }
            let lo = a.toks.lo as usize;
            if a.toks.hi as usize > lo + 2 && self.src.tok(lo + 1).kind == T::Eq {
                let v = cfg::tok_str(self.src, lo + 2);
                if v.starts_with(b"\"llvm.") {
                    self.gate("link_llvm_intrinsics", pos, "linking to LLVM intrinsics is experimental");
                }
            }
        }
    }

    /// feature_gate.rs `check_impl_trait`: `impl Trait` inside `type Alias = ..;`.
    fn impl_trait_in_alias(&mut self, ty: TyId, assoc: bool) {
        let mut found = Vec::new();
        self.impl_traits(ty, &mut found);
        for pos in found {
            if assoc {
                self.gate("impl_trait_in_assoc_type", pos, "`impl Trait` in associated types is unstable");
            } else {
                self.gate("type_alias_impl_trait", pos, "`impl Trait` in type aliases is unstable");
            }
        }
    }

    /// The `impl Trait` types inside `ty` (not through anonymous constants). Types keep no
    /// position: the position is the item's first mention of the keyword.
    fn impl_traits(&self, ty: TyId, out: &mut Vec<u32>) {
        let ast = self.ast;
        match *ast.ty(ty) {
            Ty::ImplTrait(_) => out.push(self.ty_pos(ty)),
            Ty::Ref(_, _, t) | Ty::Ptr(_, t) | Ty::Slice(t) | Ty::Paren(t) | Ty::Array(t, _) => self.impl_traits(t, out),
            Ty::Tuple(l) => for &t in ast.list(l) { self.impl_traits(t, out) },
            Ty::Path(p) => {
                for seg in ast.segs(p.segs) {
                    if let Some(GenericArgs::Angle(l)) = ast.gargs(seg.args()) {
                        for ga in ast.list(*l) {
                            match *ga {
                                GenericArg::Type(t) | GenericArg::Binding(_, _, t) => self.impl_traits(t, out),
                                _ => {}
                            }
                        }
                    }
                }
            }
            Ty::Fn(f) => {
                let f = *ast.fn_ptr(f);
                for &t in ast.list(f.params) { self.impl_traits(t, out) }
                if let Some(r) = f.ret { self.impl_traits(r, out) }
            }
            _ => {}
        }
    }

    /// Types keep no position of their own: a gate on a type is reported at the innermost
    /// item or expression that holds it.
    fn ty_pos(&self, _ty: TyId) -> u32 {
        self.cur_pos
    }

    // ---------------------------------------------------------------- signatures

    fn fn_sig(&mut self, sig: &FnSig) {
        self.generics(&sig.generics);
        if let SelfParam::Typed(_, t) = sig.self_param.unwrap_or(SelfParam::Value(false)) { self.ty(t); }
        for p in self.ast.list(sig.params).to_vec() {
            if self.attrs(p.attrs).is_none() { continue; }
            self.pat(p.pat);
            self.ty(p.ty);
        }
        if let Some(r) = sig.ret { self.ret_ty(r); }
    }

    /// A return type (`-> !` needs no gate).
    fn ret_ty(&mut self, t: TyId) {
        if !matches!(self.ast.ty(t), Ty::Never) { self.ty(t); }
    }

    fn generics(&mut self, g: &Generics) {
        for p in self.ast.list(g.params).to_vec() {
            if self.attrs(p.attrs).is_none() { continue; }
            match p.kind {
                GenericParamKind::Lifetime(_) => {}
                GenericParamKind::Type(b, d) => {
                    self.bounds(b);
                    if let Some(t) = d { self.ty(t); }
                }
                GenericParamKind::Const(t, d) => {
                    self.ty(t);
                    if let Some(e) = d { self.expr(e); }
                }
            }
        }
        for w in self.ast.list(g.where_).to_vec() {
            match w {
                WherePred::Bound { hrtb, ty, bounds } => {
                    self.late_bound_defs(hrtb);
                    self.ty(ty);
                    self.bounds(bounds);
                }
                WherePred::Lifetime(..) => {}
            }
        }
    }

    /// feature_gate.rs `check_late_bound_lifetime_defs`: `for<..>` binders hold lifetimes only.
    fn late_bound_defs(&mut self, params: List<GenericParam>) {
        let pos = self.ast.list(params).iter().find(|p| !matches!(p.kind, GenericParamKind::Lifetime(_))).map(|p| p.name.lo);
        if let Some(pos) = pos {
            self.gate("non_lifetime_binders", pos, "only lifetime parameters can be used in this context");
        }
    }

    fn bounds(&mut self, b: List<Bound>) {
        for bound in self.ast.list(b).to_vec() {
            if let Bound::Trait { hrtb, path, .. } = bound {
                self.late_bound_defs(hrtb);
                self.path(&path);
            }
        }
    }

    fn fields(&mut self, l: List<FieldDef>) {
        for f in self.ast.list(l).to_vec() {
            if self.attrs(f.attrs).is_none() { continue; }
            self.ty(f.ty);
            if let Some(d) = f.default { self.expr(d); }
        }
    }

    fn variant_data(&mut self, d: &VariantData) {
        match *d {
            VariantData::Unit => {}
            VariantData::Tuple(l) | VariantData::Struct(l) => self.fields(l),
        }
    }

    // ---------------------------------------------------------------- types and paths

    fn path(&mut self, p: &Path) {
        if let Some(q) = self.ast.qself(p).copied() {
            self.ty(q.ty);
            if let Some(tp) = q.trait_path { self.path(&tp); }
        }
        for seg in self.ast.segs(p.segs).to_vec() {
            self.generic_args(seg.args());
        }
    }

    fn generic_args(&mut self, id: GenericArgsId) {
        let Some(ga) = self.ast.gargs(id).copied() else { return };
        match ga {
            GenericArgs::Angle(l) => {
                for a in self.ast.list(l).to_vec() {
                    match a {
                        GenericArg::Lifetime(_) => {}
                        GenericArg::Type(t) => self.ty(t),
                        GenericArg::Const(e) => self.expr(e),
                        GenericArg::Binding(_, ga, t) => {
                            self.generic_args(ga);
                            self.ty(t);
                        }
                        GenericArg::Constraint(_, b) => self.bounds(b),
                    }
                }
            }
            GenericArgs::Paren(tys, ret) => {
                for &t in self.ast.list(tys).to_vec().iter() { self.ty(t); }
                // `Fn() -> !`: the one return position that gates the never type
                if let Some(r) = ret { self.ty(r); }
            }
        }
    }

    fn ty(&mut self, t: TyId) {
        let ast = self.ast;
        match *ast.ty(t) {
            Ty::Path(p) => self.path(&p),
            Ty::Ref(_, _, x) | Ty::Ptr(_, x) | Ty::Slice(x) | Ty::Paren(x) => self.ty(x),
            Ty::Array(x, e) => {
                self.ty(x);
                self.expr(e);
            }
            Ty::Tuple(l) => for &x in ast.list(l) { self.ty(x) },
            Ty::Fn(f) => {
                let f = *ast.fn_ptr(f);
                self.late_bound_defs(f.hrtb);
                for &x in ast.list(f.params) { self.ty(x) }
                if let Some(r) = f.ret { self.ret_ty(r); }
            }
            Ty::Never => {
                let pos = self.ty_pos(t);
                self.gate("never_type", pos, "the `!` type is experimental");
            }
            Ty::ImplTrait(b) | Ty::DynTrait(b, _) => self.bounds(b),
            Ty::Infer | Ty::Mac(_) | Ty::ImplicitSelf | Ty::CVarArgs => {}
        }
    }

    // ---------------------------------------------------------------- patterns

    fn pat(&mut self, p: PatId) {
        let ast = self.ast;
        match *ast.pat(p) {
            Pat::Wild | Pat::Rest | Pat::Mac(_) => {}
            Pat::Ident { sub, .. } => if let Some(s) = sub { self.pat(s) },
            Pat::Lit(e) => self.expr(e),
            Pat::Range(a, b, _) => {
                if let Some(e) = a { self.expr(e) }
                if let Some(e) = b { self.expr(e) }
            }
            Pat::Path(path) => self.path(&path),
            Pat::TupleStruct(path, l) => {
                self.path(&path);
                for &x in ast.list(l) { self.pat(x) }
            }
            Pat::Struct(path, l, _) => {
                self.path(&path);
                for f in ast.list(l).to_vec() {
                    if self.attrs(f.attrs).is_none() { continue; }
                    self.pat(f.pat);
                }
            }
            Pat::Tuple(l) | Pat::Or(l) => for &x in ast.list(l) { self.pat(x) },
            Pat::Slice(l) => {
                for &x in ast.list(l) {
                    // `[a, X.., b]`: a half-open range in a slice
                    let inner = match *ast.pat(x) {
                        Pat::Ident { sub: Some(s), .. } => s,
                        _ => x,
                    };
                    if matches!(*ast.pat(inner), Pat::Range(Some(_), None, _)) {
                        let pos = self.cur_pos;
                        self.gate("half_open_range_patterns_in_slices", pos, "`X..` patterns in slices are experimental");
                    }
                    self.pat(x);
                }
            }
            Pat::Ref(_, x) | Pat::Paren(x) => self.pat(x),
            Pat::Box(x) => {
                let pos = self.cur_pos;
                self.gate("box_patterns", pos, "box pattern syntax is experimental");
                self.pat(x);
            }
        }
    }

    // ---------------------------------------------------------------- bodies

    /// A body owner's body: a fn's block or a const / static initializer.
    pub fn body(&mut self, owner: crate::program::DefId) {
        let def = self.prog.def(owner);
        let item = *self.ast.item(def.item);
        let outer = std::mem::replace(&mut self.cur_pos, item.lo);
        match item.kind {
            ItemKind::Fn(_, Some(b), _) => self.block(b),
            ItemKind::Const(_, e) | ItemKind::Static(_, _, e) => if let Some(e) = e.get() { self.expr(e) },
            _ => {}
        }
        self.cur_pos = outer;
    }

    fn block(&mut self, b: BlockId) {
        let ast = self.ast;
        if !ast.has_block(b) { return; }
        let blk = *ast.block(b);
        let _ = self.attrs(blk.attrs);
        for s in ast.list(blk.stmts).to_vec() {
            match s {
                Stmt::Let(r) => {
                    let l = *ast.row(r);
                    if self.attrs(l.attrs).is_none() { continue; }
                    self.pat(l.pat);
                    if let Some(t) = l.ty { self.ty(t); }
                    if let Some(e) = l.init { self.expr(e); }
                    if let Some(eb) = l.else_ { self.block(eb); }
                }
                Stmt::Item(i) => self.item(i, Ctx::Free),
                Stmt::Expr(e, _) => self.expr(e),
                Stmt::Attrs(r) => {
                    let a = *ast.row(r);
                    if self.attrs(a.attrs).is_none() { continue; }
                    self.expr(a.expr);
                }
                Stmt::Empty => {}
            }
        }
    }

    fn expr(&mut self, e: ExprId) {
        let ast = self.ast;
        if !ast.has_expr(e) { return; }
        let ex = *ast.expr(e);
        let outer = std::mem::replace(&mut self.cur_pos, ex.lo);
        match ex.kind {
            ExprKind::Lit(k) => {
                if matches!(k, LitKind::Int | LitKind::Float) {
                    let text = self.pf.bytes(ex.lo, ex.hi);
                    if text.ends_with(b"f16") { self.gate("f16", ex.lo, "the type `f16` is unstable"); }
                    if text.ends_with(b"f128") { self.gate("f128", ex.lo, "the type `f128` is unstable"); }
                }
            }
            ExprKind::Path(p) => self.path(&p),
            ExprKind::Unary(_, a) | ExprKind::Field(a, _) | ExprKind::TupleField(a, _) | ExprKind::AddrOf(_, _, a)
            | ExprKind::Try(a) | ExprKind::Await(a) | ExprKind::Paren(a) | ExprKind::Box(a) | ExprKind::Let(_, a) => {
                if let ExprKind::Let(p, _) = ex.kind { self.pat(p); }
                self.expr(a);
            }
            ExprKind::Cast(a, t) => {
                self.expr(a);
                self.ty(t);
            }
            ExprKind::Binary(_, a, b) | ExprKind::Assign(a, b) | ExprKind::AssignOp(_, a, b) | ExprKind::Index(a, b) | ExprKind::Repeat(a, b) => {
                self.expr(a);
                self.expr(b);
            }
            ExprKind::Call(f, args) => {
                self.expr(f);
                for &a in ast.list(args).to_vec().iter() { self.expr(a) }
            }
            ExprKind::MethodCall(recv, r) => {
                self.expr(recv);
                let m = *ast.row(r);
                self.generic_args(m.turbofish);
                for &a in ast.list(m.args).to_vec().iter() { self.expr(a) }
            }
            ExprKind::Block(b, _) | ExprKind::Unsafe(b) | ExprKind::Async(_, b) | ExprKind::ConstBlock(b) | ExprKind::Loop(b, _) => self.block(b),
            ExprKind::If(c, b, el) => {
                self.expr(c);
                self.block(b);
                if let Some(x) = el.get() { self.expr(x) }
            }
            ExprKind::Match(s, arms) => {
                self.expr(s);
                for arm in ast.list(arms).to_vec() {
                    if self.attrs(arm.attrs).is_none() { continue; }
                    self.pat(arm.pat);
                    if let Some(g) = arm.guard { self.expr(g) }
                    self.expr(arm.body);
                }
            }
            ExprKind::While(r) => {
                let w = *ast.row(r);
                self.expr(w.cond);
                self.block(w.body);
            }
            ExprKind::For(r) => {
                let f = *ast.row(r);
                self.pat(f.pat);
                self.expr(f.iter);
                self.block(f.body);
            }
            ExprKind::Break(_, v) => if let Some(x) = v.get() { self.expr(x) },
            ExprKind::Return(v) | ExprKind::Yield(v) => if let Some(x) = v.get() { self.expr(x) },
            ExprKind::Continue(_) | ExprKind::Underscore | ExprKind::Mac(_) => {}
            ExprKind::Closure(r) => {
                let c = *ast.row(r);
                for p in ast.list(c.params).to_vec() {
                    if self.attrs(p.attrs).is_none() { continue; }
                    self.pat(p.pat);
                    if let Some(t) = p.ty { self.ty(t) }
                }
                if let Some(t) = c.ret { self.ret_ty(t) }
                self.expr(c.body);
            }
            ExprKind::Tuple(l) | ExprKind::Array(l) => for &x in ast.list(l).to_vec().iter() { self.expr(x) },
            ExprKind::Struct(r) => {
                let s = *ast.row(r);
                self.path(&s.path);
                for f in ast.list(s.fields).to_vec() {
                    if self.attrs(f.attrs).is_none() { continue; }
                    self.expr(f.expr);
                }
                if let Some(b) = s.base.get() { self.expr(b) }
            }
            ExprKind::Range(a, b, _) => {
                if let Some(x) = a.get() { self.expr(x) }
                if let Some(x) = b.get() { self.expr(x) }
            }
        }
        self.cur_pos = outer;
    }
}

/// The bodies of a checked crate's owners (fn bodies and const / static initializers) and the
/// items nested in them, once the bodies are loaded.
pub fn check_bodies(prog: &Program, krate: u32) -> Vec<String> {
    let info = &prog.crates[krate as usize];
    let feats = info.features(prog);
    let mut out = Vec::new();
    for i in 0..prog.defs.len() {
        let d = crate::program::DefId(i as u32);
        let def = prog.def(d);
        if def.krate != krate || !matches!(def.kind, DefKind::Fn | DefKind::AssocFn | DefKind::Const | DefKind::Static | DefKind::AssocConst) { continue; }
        if prog.item_defs.get(&(def.file, def.item.0)) != Some(&d) { continue; }
        let mut w = Gates::new(prog, krate, def.file, feats);
        w.body(d);
        out.append(&mut w.errors);
    }
    out
}
