//! `#[derive(Debug, Default, Hash, PartialOrd, Ord)]` expanded by the parser into ordinary
//! `impl` items (S2 std), the way rustc's built-in derives work. PartialEq / Clone stay
//! compiler glue (lower.rs: lower_derived_eq / lower_derived_clone); Copy / Eq are markers.
//!
//! Child module of `parser`.

use super::{PErr, PResult, Parser};
use crate::ast::*;
use crate::lexer::{Tok, T};

const CORE: &str = "::__relax_crate_core";
/// a `>` without a token of its own (see Parser::closes)
const GT: usize = usize::MAX;

/// Derives this module expands (the rest stay `tcx.derived` markers / glue).
pub const EXPANDED: &[&str] = &["Debug", "Default", "Hash", "PartialOrd", "Ord"];

/// The trait surface of compiler-owned derives, including marker/glue derives.
/// Hosted derives with the same spelling must still use their actual output.
pub fn trait_path(name: &str) -> Option<&'static str> {
    Some(match name {
        "Debug" => "fmt::Debug", "Default" => "default::Default", "Hash" => "hash::Hash",
        "PartialOrd" => "cmp::PartialOrd", "Ord" => "cmp::Ord", "PartialEq" => "cmp::PartialEq",
        "Eq" => "cmp::Eq", "Copy" => "marker::Copy", "Clone" => "clone::Clone",
        _ => return None,
    })
}

struct Shape {
    /// variant name (None: the struct itself)
    name: Option<String>,
    /// named fields (Some) or tuple fields (None names)
    fields: Vec<Option<String>>,
    kind: u8, // 0 unit, 1 tuple, 2 struct
    default_attr: bool,
}

/// Name of the anonymous const holding the declared default of field `field` of struct `ty`
/// (or of `ty`'s variant `variant`): `field: T = expr` (default_field_values).
pub fn default_const_name(ty: &str, variant: Option<&str>, field: &str) -> String {
    match variant {
        Some(v) => format!("__relax_default_{}_{}_{}", ty, v, field),
        None => format!("__relax_default_{}_{}", ty, field),
    }
}

/// Name of the anonymous const holding variant `vi`'s discriminant of enum `name`.
pub fn disc_const_name(name: &str, vi: usize) -> String {
    format!("__relax_disc_{}_{}", name, vi)
}

/// Only plain structs take `#[rust(expr)]` defaults (enum variants' fields never grow live).
fn variant_is_none_live(groups: &[(Option<String>, Vec<FieldDef>)]) -> bool {
    groups.len() == 1 && groups[0].0.is_none()
}

impl<'a> Parser<'a> {
    /// After an enum: every discriminant expression that is more than a literal also becomes a
    /// const item of the repr type (rustc: discriminants are anonymous consts), so one the
    /// signature-time evaluator cannot read (`= four_char("dev#")`) is evaluated like any const
    /// (CTFE through the JIT, tcx re-collects the enum).
    pub(super) fn enum_disc_consts(&mut self, id: ItemId) -> PResult<()> {
        let it = self.ast.item(id).clone();
        let vars = match &it.kind {
            ItemKind::Enum(_, v) => v.clone(),
            _ => return Ok(()),
        };
        let mut repr = "isize".to_string();
        for a in self.ast.list(it.attrs) {
            let (lo, hi) = (a.toks.lo as usize, a.toks.hi as usize);
            if hi <= lo || self.tok_text(self.toks[lo]) != b"repr" {
                continue;
            }
            for i in lo + 1..hi {
                let n = self.tok_text(self.toks[i]);
                if [&b"u8"[..], b"u16", b"u32", b"u64", b"u128", b"usize", b"i8", b"i16", b"i32", b"i64", b"i128", b"isize"].contains(&n) {
                    repr = String::from_utf8_lossy(n).into_owned();
                }
            }
        }
        let name = String::from_utf8_lossy(self.bytes(it.name.lo, it.name.hi)).into_owned();
        let mut text = String::new();
        for (vi, v) in self.ast.list(vars).iter().enumerate() {
            let e = match v.disc {
                Some(e) => e,
                None => continue,
            };
            let mut x = e;
            while let ExprKind::Paren(y) | ExprKind::Unary(UnOp::Neg, y) = &self.ast.expr(x).kind {
                x = *y;
            }
            if matches!(self.ast.expr(x).kind, ExprKind::Lit(_)) {
                continue;
            }
            let ex = self.ast.expr(e);
            let src = String::from_utf8_lossy(self.bytes(ex.lo, ex.hi)).into_owned();
            text.push_str(&format!("#[allow(non_upper_case_globals)] const {}: {} = {};\n", disc_const_name(&name, vi), repr, src));
        }
        if text.is_empty() {
            return Ok(());
        }
        let g = super::fmtmac::Gen::from_text(text);
        let start = self.splice_expansion("discriminant", &g, it.name.lo)?;
        let items = self.in_expansion(start, |p| p.items_until(T::Eof))?;
        self.extra_items.extend(items);
        Ok(())
    }

    /// After a struct or enum: every field default value (`field: T = expr`) becomes an
    /// anonymous const of the field's type (rustc: default field values are anonymous consts),
    /// read by `S { a: 1, .. }` for the omitted fields. A generic type's defaults get none
    /// (a const item cannot take the type's parameters): such a `..` is a typeck error.
    pub(super) fn default_consts(&mut self, id: ItemId) -> PResult<()> {
        let it = self.ast.item(id).clone();
        let mut groups: Vec<(Option<String>, Vec<FieldDef>)> = Vec::new();
        match &it.kind {
            ItemKind::Struct(g, VariantData::Struct(f)) if g.params.is_empty() => groups.push((None, self.ast.list(*f).to_vec())),
            ItemKind::Enum(g, vars) if g.params.is_empty() => {
                for v in self.ast.list(*vars) {
                    if let VariantData::Struct(f) = &v.data {
                        groups.push((Some(String::from_utf8_lossy(self.bytes(v.name.lo, v.name.hi)).into_owned()), self.ast.list(*f).to_vec()));
                    }
                }
            }
            _ => return Ok(()),
        }
        let name = String::from_utf8_lossy(self.bytes(it.name.lo, it.name.hi)).trim_start_matches("r#").to_string();
        let mut text = String::new();
        // live sessions (M10): a struct field's `#[rust(expr)]` initial value (makepad's) is its
        // default too, for running values when an edit adds the field (lower.rs ext_project)
        let live = variant_is_none_live(&groups) && self.session.options.live;
        for (variant, fields) in &groups {
            for f in fields {
                let Some(fname) = f.name else { continue };
                let src = match f.default {
                    Some(e) => {
                        let ex = self.ast.expr(e);
                        String::from_utf8_lossy(self.bytes(ex.lo, ex.hi)).into_owned()
                    }
                    None if live => match self.rust_attr_expr(self.ast.list(f.attrs)) {
                        Some(x) => x,
                        None => continue,
                    },
                    None => continue,
                };
                let fname = String::from_utf8_lossy(self.bytes(fname.lo, fname.hi)).trim_start_matches("r#").to_string();
                let ty = String::from_utf8_lossy(self.bytes(f.ty_span.0, f.ty_span.1)).into_owned();
                text.push_str(&format!("#[allow(non_upper_case_globals)] const {}: {} = {};\n", default_const_name(&name, variant.as_deref(), &fname), ty, src));
            }
        }
        if text.is_empty() {
            return Ok(());
        }
        let g = super::fmtmac::Gen::from_text(text);
        let start = self.splice_expansion("field default", &g, it.name.lo)?;
        let items = self.in_expansion(start, |p| p.items_until(T::Eof))?;
        self.extra_items.extend(items);
        Ok(())
    }

    /// The expression of a field attribute `#[rust(expr)]` (makepad's initial value), as text.
    fn rust_attr_expr(&self, attrs: &[Attr]) -> Option<String> {
        for a in attrs {
            let (lo, hi) = (a.toks.lo as usize, a.toks.hi as usize);
            if hi < lo + 3 || self.tok_text(self.toks[lo]) != b"rust" || self.tok_text(self.toks[lo + 1]) != b"(" {
                continue;
            }
            let (s, e) = (self.toks[lo + 2].lo, self.toks[hi - 2].hi);
            if self.tok_text(self.toks[hi - 1]) != b")" || e <= s {
                continue;
            }
            return Some(String::from_utf8_lossy(self.bytes(s, e)).into_owned());
        }
        None
    }

    /// After an item: its expandable derives become impl items in `extra_items`.
    pub(super) fn derive_after(&mut self, id: ItemId, tok_lo: usize) -> PResult<()> {
        let _timing = crate::parse_work::time(2);
        let s2 = match &self.macros {
            Some(m) => m.table.s2_fmt,
            None => false,
        };
        if !s2 {
            return Ok(());
        }
        let it = self.ast.item(id).clone();
        if !matches!(it.kind, ItemKind::Struct(..) | ItemKind::Enum(..)) {
            return Ok(());
        }
        let mut wanted: Vec<&'static str> = Vec::new();
        for a in self.ast.list(it.attrs) {
            let (lo, hi) = (a.toks.lo as usize, a.toks.hi as usize);
            if hi <= lo || self.tok_text(self.toks[lo]) != b"derive" {
                continue;
            }
            for i in lo + 1..hi {
                let t = self.toks[i];
                if t.kind != T::Ident {
                    continue;
                }
                // last segment of a path (`fmt::Debug`): followed by `,` or `)`
                if i + 1 < hi && self.toks[i + 1].kind == T::PathSep {
                    continue;
                }
                let n = self.tok_text(t);
                if let Some(e) = EXPANDED.iter().find(|x| x.as_bytes() == n) {
                    if !wanted.contains(e) {
                        wanted.push(e);
                    }
                }
            }
        }
        if wanted.is_empty() {
            return Ok(());
        }
        let _profile = crate::load_profile::span(self.session.runtime.profile, "derive-builtin", &wanted.join(","));
        let lo = self.ast.list(it.attrs).iter().map(|a| self.toks[a.toks.lo as usize].lo).min().unwrap_or(it.lo).min(it.lo);
        let key = crate::parse_work::key(self, "native-derive", lo, it.hi, false);
        if let Some(x) = crate::parse_work::get(&key) {
            return self.install_derive_text(x.text, it.name.lo);
        }
        let name = String::from_utf8_lossy(self.bytes(it.name.lo, it.name.hi)).into_owned();
        let (gparams, where_text) = self.derive_generics(tok_lo, &it);
        // field types naming a param's associated type (`x: T::Wide`): rustc's derive bounds
        // them too (`where T::Wide: Debug`, deriving/generic find_type_parameters)
        let mut assoc_tys: Vec<String> = Vec::new();
        {
            let tparams: Vec<&str> = gparams.iter().filter(|g| g.0 == 1).map(|g| g.1.as_str()).collect();
            let mut i = tok_lo;
            while i < self.toks.len() && self.toks[i].hi <= it.hi {
                let t = self.toks[i];
                if t.kind == T::Ident && t.lo > it.name.hi && i + 2 < self.toks.len() && self.toks[i + 1].kind == T::PathSep && self.toks[i + 2].kind == T::Ident && (i == 0 || self.toks[i - 1].kind != T::PathSep) {
                    let n = String::from_utf8_lossy(self.tok_text(t)).into_owned();
                    if tparams.contains(&n.as_str()) {
                        let mut path = n;
                        let mut j = i + 1;
                        while j + 1 < self.toks.len() && self.toks[j].kind == T::PathSep && self.toks[j + 1].kind == T::Ident {
                            path.push_str("::");
                            path.push_str(&String::from_utf8_lossy(self.tok_text(self.toks[j + 1])));
                            j += 2;
                        }
                        // (a path call `T::new(..)` is no type)
                        if !(j < self.toks.len() && self.toks[j].kind == T::OpenParen) && !assoc_tys.contains(&path) {
                            assoc_tys.push(path);
                        }
                        i = j;
                        continue;
                    }
                }
                i += 1;
            }
        }
        let shapes = self.derive_shapes(&it);
        let is_enum = matches!(it.kind, ItemKind::Enum(..));
        // the discriminant type (`#[repr(u8)]` ..; isize by default): derived orderings compare
        // discriminant values as this type (rustc's derive uses discriminant_value)
        let mut disc_ty = "isize".to_string();
        for a in self.ast.list(it.attrs) {
            let (lo, hi) = (a.toks.lo as usize, a.toks.hi as usize);
            if hi <= lo || self.tok_text(self.toks[lo]) != b"repr" {
                continue;
            }
            for i in lo + 1..hi {
                let n = self.tok_text(self.toks[i]);
                if [&b"u8"[..], b"u16", b"u32", b"u64", b"u128", b"usize", b"i8", b"i16", b"i32", b"i64", b"i128", b"isize"].contains(&n) {
                    disc_ty = String::from_utf8_lossy(n).into_owned();
                }
            }
        }
        let mut text = String::new();
        for tr in wanted {
            let _profile = crate::load_profile::span(self.session.runtime.profile, "derive-builtin-generate", tr);
            let path = format!("{CORE}::{}", trait_path(tr).expect("compiler derive trait"));
            let body = match tr {
                "Debug" => gen_debug(&name, is_enum, &shapes),
                "Default" => match gen_default(&name, is_enum, &shapes) {
                    Some(b) => b,
                    None => return Err(PErr { pos: it.name.lo, msg: "derive(Default) on an enum needs one `#[default]` unit variant".to_string() }),
                },
                "Hash" => gen_hash(&name, is_enum, &shapes),
                "PartialOrd" => gen_ord(&name, is_enum, &shapes, true, &disc_ty),
                _ => gen_ord(&name, is_enum, &shapes, false, &disc_ty),
            };
            // impl<params + bound> Trait for Name<args> where ..
            let mut ig = Vec::new();
            let mut ta = Vec::new();
            for (kind, n, bounds) in &gparams {
                match kind {
                    0 => {
                        ig.push(format!("{}{}", n, if bounds.is_empty() { String::new() } else { format!(": {}", bounds) }));
                        ta.push(n.clone());
                    }
                    // (`#[derive(Default)]` on an enum takes its `#[default]` unit variant: no
                    // `T: Default` bounds, rustc deriving/default.rs skip_path_as_bound)
                    1 if tr == "Default" && is_enum => {
                        ig.push(if bounds.is_empty() { n.clone() } else { format!("{}: {}", n, bounds) });
                        ta.push(n.clone());
                    }
                    1 => {
                        let b = if bounds.is_empty() { path.clone() } else { format!("{} + {}", bounds, path) };
                        ig.push(format!("{}: {}", n, b));
                        ta.push(n.clone());
                    }
                    _ => {
                        ig.push(format!("const {}: {}", n, bounds));
                        ta.push(n.clone());
                    }
                }
            }
            let g = if ig.is_empty() { String::new() } else { format!("<{}>", ig.join(", ")) };
            let a = if ta.is_empty() { String::new() } else { format!("<{}>", ta.join(", ")) };
            let mut wt = where_text.trim().trim_end_matches(',').to_string();
            for at in assoc_tys.iter().filter(|_| !(tr == "Default" && is_enum)) {
                wt = if wt.is_empty() { format!("where {}: {}", at, path) } else { format!("{}, {}: {}", wt, at, path) };
            }
            text.push_str(&format!("impl{} {} for {}{} {} {{ {} }}\n", g, path, name, a, wt, body));
        }
        if let Some(t) = crate::preload::relax_trace() {
            if t.split(',').any(|p| p.strip_prefix("derive:").map_or(false, |n| name.contains(n))) {
                eprintln!("derive {} => {}", name, text);
            }
        }
        crate::parse_work::put(key, &crate::builtins::Expansion { text: text.clone(), toks: Vec::new(), origins: Vec::new() });
        self.install_derive_text(text, it.name.lo)
    }

    fn install_derive_text(&mut self, text: String, call: u32) -> PResult<()> {
        let source = self.source_span(call);
        let g = super::fmtmac::Gen::from_text(text);
        let start = self.splice_expansion("derive", &g, call)?;
        self.token_origins.extend(self.toks[start..].iter().filter(|t| t.kind != T::Eof)
            .map(|t| crate::source::TokenOrigin { lo: t.lo, hi: t.hi, source }));
        let items = self.in_expansion(start, |p| p.items_until(T::Eof))?;
        self.extra_items.extend(items);
        Ok(())
    }

    /// The item's generic params as (kind 0 lifetime / 1 type / 2 const, name, bounds or
    /// const type text) and its where clause text, from its tokens.
    fn derive_generics(&self, tok_lo: usize, it: &Item) -> (Vec<(u8, String, String)>, String) {
        let mut out = Vec::new();
        // the name token, then `<`
        let mut i = tok_lo;
        while i < self.toks.len() && !(self.toks[i].lo == it.name.lo && self.toks[i].hi == it.name.hi) {
            i += 1;
        }
        i += 1;
        let mut end_generics = i;
        if i < self.toks.len() && self.toks[i].kind == T::Lt {
            // split params at top-level commas up to the matching `>`
            let mut depth = 1i32;
            let mut j = i + 1;
            let mut cur: Vec<usize> = Vec::new();
            let mut params: Vec<Vec<usize>> = Vec::new();
            while j < self.toks.len() {
                let k = self.toks[j].kind;
                let before = depth;
                match k {
                    T::Lt => depth += 1,
                    T::Shl => depth += 2,
                    T::Gt | T::Shr => depth -= self.closes(j),
                    T::OpenParen | T::OpenBracket | T::OpenBrace => depth += 100,
                    T::CloseParen | T::CloseBracket | T::CloseBrace => depth -= 100,
                    _ => {}
                }
                if depth <= 0 {
                    // `u16>>`: the first `>` (no token of its own) closes inside the param
                    for _ in 1..before.max(1) {
                        cur.push(GT);
                    }
                    break;
                }
                if k == T::Comma && depth == 1 {
                    params.push(std::mem::take(&mut cur));
                } else {
                    cur.push(j);
                }
                j += 1;
            }
            if !cur.is_empty() {
                params.push(cur);
            }
            end_generics = j + 1;
            for p in params {
                // drop attributes and defaults
                let mut toks: Vec<usize> = Vec::new();
                let mut k = 0;
                let mut ad = 0i32;
                while k < p.len() {
                    if p[k] == GT {
                        ad -= 1;
                        toks.push(GT);
                        k += 1;
                        continue;
                    }
                    let t = self.toks[p[k]];
                    match t.kind {
                        T::Lt => ad += 1,
                        T::Gt | T::Shr => ad -= self.closes(p[k]),
                        T::Shl => ad += 2,
                        _ => {}
                    }
                    if t.kind == T::Pound {
                        // #[..]
                        let mut d = 0;
                        k += 1;
                        while k < p.len() {
                            match self.toks[p[k]].kind {
                                T::OpenBracket => d += 1,
                                T::CloseBracket => {
                                    d -= 1;
                                    if d == 0 {
                                        k += 1;
                                        break;
                                    }
                                }
                                _ => {}
                            }
                            k += 1;
                        }
                        continue;
                    }
                    if t.kind == T::Eq && ad == 0 {
                        break;
                    }
                    toks.push(p[k]);
                    k += 1;
                }
                if toks.is_empty() {
                    continue;
                }
                if toks[0] == GT {
                    continue;
                }
                let first = self.toks[toks[0]];
                let txt = |s: &Self, v: &[usize]| -> String {
                    let mut r = String::new();
                    for (n, &x) in v.iter().enumerate() {
                        if n > 0 {
                            r.push(' ');
                        }
                        if x == GT {
                            r.push('>');
                        } else if s.toks[x].kind == T::Gt && s.closes(x) == 2 {
                            r.push_str("> >");
                        } else {
                            r.push_str(&String::from_utf8_lossy(s.tok_text(s.toks[x])));
                        }
                    }
                    r
                };
                if first.kind == T::Lifetime {
                    let n = txt(self, &toks[..1]);
                    let b = if toks.len() > 2 { txt(self, &toks[2..]) } else { String::new() };
                    out.push((0, n, b));
                } else if first.kind == T::KwConst {
                    let n = if toks.len() > 1 { txt(self, &toks[1..2]) } else { String::new() };
                    let ty = if toks.len() > 3 { txt(self, &toks[3..]) } else { String::new() };
                    out.push((2, n, ty));
                } else {
                    let n = txt(self, &toks[..1]);
                    let b = if toks.len() > 2 { txt(self, &toks[2..]) } else { String::new() };
                    out.push((1, n, b));
                }
            }
        }
        // where clause: from `where` at depth 0 to the body `{` or `;` (tuple structs: after `( .. )`)
        let mut w = String::new();
        let mut j = end_generics;
        let mut depth = 0i32;
        while j < self.toks.len() {
            let k = self.toks[j].kind;
            if depth == 0 && k == T::KwWhere {
                let mut e = j;
                let mut d2 = 0i32;
                while e < self.toks.len() {
                    let ke = self.toks[e].kind;
                    match ke {
                        T::Lt => d2 += 1,
                        T::Gt | T::Shr => d2 -= self.closes(e),
                        T::Shl => d2 += 2,
                        T::OpenParen | T::OpenBracket => d2 += 100,
                        T::CloseParen | T::CloseBracket => d2 -= 100,
                        _ => {}
                    }
                    if d2 <= 0 && (ke == T::OpenBrace || ke == T::Semi) {
                        break;
                    }
                    if !w.is_empty() {
                        w.push(' ');
                    }
                    w.push_str(&String::from_utf8_lossy(self.tok_text(self.toks[e])));
                    e += 1;
                }
                break;
            }
            match k {
                T::OpenParen | T::OpenBracket => depth += 1,
                T::CloseParen | T::CloseBracket => depth -= 1,
                T::OpenBrace | T::Semi if depth == 0 => break,
                _ => {}
            }
            j += 1;
        }
        (out, w)
    }

    /// How many `>` token `i` closes: the parser splits `>>` in place (the token becomes the
    /// second `>`), so a `>` right after a `>` byte no token covers counts twice.
    fn closes(&self, i: usize) -> i32 {
        let t = self.toks[i];
        if t.kind == T::Shr {
            return 2;
        }
        let prev_hi = if i > 0 { self.toks[i - 1].hi } else { 0 };
        if t.lo > prev_hi && self.bytes(t.lo - 1, t.lo) == b">" {
            2
        } else {
            1
        }
    }

    /// Is a field / variant with these attributes present for this target (`#[cfg(..)]`)?
    /// Without a build context (tools that parse without a target) everything counts.
    pub(super) fn cfg_present(&self, attrs: &[Attr]) -> bool {
        let c = match &self.bctx {
            Some(c) if !attrs.is_empty() => c,
            _ => return true,
        };
        // the attribute tokens may sit in macro-expansion text (positions past `src`): copy them
        // into a small source of their own for the cfg evaluator
        let mut src: Vec<u8> = Vec::new();
        let mut toks: Vec<Tok> = Vec::new();
        let mut local: Vec<Attr> = Vec::new();
        for a in attrs {
            let lo = toks.len() as u32;
            for i in a.toks.lo..a.toks.hi {
                let t = self.toks[i as usize];
                let b = self.tok_text(t);
                let p = src.len() as u32;
                src.extend_from_slice(b);
                src.push(b' ');
                toks.push(Tok { kind: t.kind, lo: p, hi: p + b.len() as u32 });
            }
            let mut na = a.clone();
            na.toks = TokRange { lo, hi: toks.len() as u32 };
            local.push(na);
        }
        crate::cfg::active(crate::cfg::Src { src: &src, toks: &toks, ext: &[], ptoks: &[], parts: None }, &local, &c.cfg)
    }

    fn derive_shapes(&self, it: &Item) -> Vec<Shape> {
        let shape_of = |s: &Self, d: &VariantData, name: Option<String>, attrs: &[Attr]| -> Shape {
            let default_attr = attrs.iter().any(|a| a.toks.hi > a.toks.lo && s.tok_text(s.toks[a.toks.lo as usize]) == b"default");
            match d {
                VariantData::Unit => Shape { name, fields: Vec::new(), kind: 0, default_attr },
                VariantData::Tuple(f) => Shape { name, fields: s.ast.list(*f).iter().filter(|x| s.cfg_present(s.ast.list(x.attrs))).map(|_| None).collect(), kind: 1, default_attr },
                VariantData::Struct(f) => Shape {
                    name,
                    fields: s.ast.list(*f).iter().filter(|x| s.cfg_present(s.ast.list(x.attrs))).map(|x| x.name.map(|n| String::from_utf8_lossy(s.bytes(n.lo, n.hi)).into_owned())).collect(),
                    kind: 2,
                    default_attr,
                },
            }
        };
        match &it.kind {
            ItemKind::Struct(_, d) => vec![shape_of(self, d, None, &[])],
            ItemKind::Enum(_, vs) => self.ast.list(*vs)
                .iter()
                .filter(|v| self.cfg_present(self.ast.list(v.attrs)))
                .map(|v| shape_of(self, &v.data, Some(String::from_utf8_lossy(self.bytes(v.name.lo, v.name.hi)).into_owned()), self.ast.list(v.attrs)))
                .collect(),
            _ => Vec::new(),
        }
    }
}

/// `Name { a: p0, b: p1 }` / `Name(p0, p1)` / `Name` with binding prefix `p`.
fn pat(ty: &str, s: &Shape, p: &str) -> String {
    let path = match &s.name {
        Some(v) => format!("{}::{}", ty, v),
        None => ty.to_string(),
    };
    match s.kind {
        0 => path,
        1 => {
            let b: Vec<String> = (0..s.fields.len()).map(|i| format!("{}{}", p, i)).collect();
            format!("{}({})", path, b.join(", "))
        }
        _ => {
            let b: Vec<String> = s.fields.iter().enumerate().map(|(i, n)| format!("{}: {}{}", n.as_deref().unwrap_or("_"), p, i)).collect();
            format!("{} {{ {} }}", path, b.join(", "))
        }
    }
}

fn field_name(n: &Option<String>) -> String {
    let n = n.as_deref().unwrap_or("");
    n.strip_prefix("r#").unwrap_or(n).to_string()
}

fn gen_debug(ty: &str, is_enum: bool, shapes: &[Shape]) -> String {
    let mut arms = String::new();
    for s in shapes {
        let shown = s.name.clone().unwrap_or_else(|| ty.to_string());
        let e = match s.kind {
            0 => format!("f.write_str({:?})", shown),
            1 => {
                let mut x = format!("f.debug_tuple({:?})", shown);
                for i in 0..s.fields.len() {
                    x.push_str(&format!(".field(__s{})", i));
                }
                x + ".finish()"
            }
            _ => {
                let mut x = format!("f.debug_struct({:?})", shown);
                for (i, n) in s.fields.iter().enumerate() {
                    x.push_str(&format!(".field({:?}, __s{})", field_name(n), i));
                }
                x + ".finish()"
            }
        };
        arms.push_str(&format!("{} => {}, ", pat("Self", s, "__s"), e));
    }
    let m = if is_enum && shapes.is_empty() { "match *self {}".to_string() } else { format!("match self {{ {} }}", arms) };
    format!("fn fmt(&self, f: &mut {c}::fmt::Formatter<'_>) -> {c}::fmt::Result {{ {m} }}", c = CORE, m = m)
}

fn gen_default(ty: &str, is_enum: bool, shapes: &[Shape]) -> Option<String> {
    let s = if is_enum { shapes.iter().find(|s| s.default_attr)? } else { shapes.first()? };
    let path = match &s.name {
        Some(v) => format!("{}::{}", ty, v),
        None => ty.to_string(),
    };
    let d = format!("{}::default::Default::default()", CORE);
    let e = match s.kind {
        0 => path,
        1 => format!("{}({})", path, vec![d.as_str(); s.fields.len()].join(", ")),
        _ => {
            let f: Vec<String> = s.fields.iter().map(|n| format!("{}: {}", n.as_deref().unwrap_or("_"), d)).collect();
            format!("{} {{ {} }}", path, f.join(", "))
        }
    };
    Some(format!("fn default() -> Self {{ {} }}", e))
}

fn gen_hash(_ty: &str, is_enum: bool, shapes: &[Shape]) -> String {
    let mut arms = String::new();
    for (vi, s) in shapes.iter().enumerate() {
        let mut body = String::new();
        if is_enum && shapes.len() > 1 {
            body.push_str(&format!("{}::hash::Hash::hash(&({}isize), state); ", CORE, vi));
        }
        for i in 0..s.fields.len() {
            body.push_str(&format!("{}::hash::Hash::hash(__s{}, state); ", CORE, i));
        }
        arms.push_str(&format!("{} => {{ {} }} ", pat("Self", s, "__s"), body));
    }
    let m = if is_enum && shapes.is_empty() { "match *self {}".to_string() } else { format!("match self {{ {} }}", arms) };
    format!("fn hash<__H: {c}::hash::Hasher>(&self, state: &mut __H) {{ {m} }}", c = CORE, m = m)
}

/// PartialOrd::partial_cmp (`partial`) or Ord::cmp: lexicographic over variants then fields.
fn gen_ord(_ty: &str, is_enum: bool, shapes: &[Shape], partial: bool, disc_ty: &str) -> String {
    let (m, ret, eq) = if partial {
        (
            "partial_cmp",
            format!("{}::option::Option<{}::cmp::Ordering>", CORE, CORE),
            format!("{}::option::Option::Some({}::cmp::Ordering::Equal)", CORE, CORE),
        )
    } else {
        ("cmp", format!("{}::cmp::Ordering", CORE), format!("{}::cmp::Ordering::Equal", CORE))
    };
    let tr = if partial { "PartialOrd" } else { "Ord" };
    let mut body = String::new();
    if is_enum && shapes.len() > 1 {
        // variants order by their discriminant values (explicit `= n` included), compared as
        // the discriminant type
        body.push_str(&format!(
            "let __si = unsafe {{ {c}::intrinsics_mem::discriminant_value(self) }} as {d}; let __oi = unsafe {{ {c}::intrinsics_mem::discriminant_value(other) }} as {d}; if __si != __oi {{ return {c}::cmp::{tr}::{m}(&__si, &__oi); }} ",
            c = CORE,
            d = disc_ty,
            tr = tr,
            m = m
        ));
    }
    let mut arms = String::new();
    for s in shapes {
        let mut b = String::new();
        for i in 0..s.fields.len() {
            b.push_str(&format!(
                "match {c}::cmp::{tr}::{m}(__s{i}, __o{i}) {{ {eq} => {{}} __c => return __c, }} ",
                c = CORE,
                tr = tr,
                m = m,
                i = i,
                eq = eq
            ));
        }
        b.push_str(&eq);
        arms.push_str(&format!("({}, {}) => {{ {} }} ", pat("Self", s, "__s"), pat("Self", s, "__o"), b));
    }
    if is_enum && shapes.len() > 1 {
        arms.push_str(&format!("_ => {}, ", eq));
    }
    if is_enum && shapes.is_empty() {
        return format!("fn {m}(&self, other: &Self) -> {r} {{ match *self {{}} }}", m = m, r = ret);
    }
    body.push_str(&format!("match (self, other) {{ {} }}", arms));
    format!("fn {m}(&self, other: &Self) -> {r} {{ {b} }}", m = m, r = ret, b = body)
}
