//! Lints of rustc_lint / rustc_resolve that need more than the syntax of one node: they use the
//! lifetime resolution (`mismatched_lifetime_syntaxes`, `elided_lifetimes_in_paths`), the
//! macro definitions, or the source text between tokens. Check-only.

use crate::ast::*;
use crate::lint::{self, Level, Lint};
use crate::lint_early::W;
use crate::program::{DefId, DefKind, Program};
use crate::tcx::lifetime_resolve::{LifetimeRes, LifetimeResolution};
use crate::tcx::Tcx;
use std::sync::Arc;

pub const MISMATCHED_LIFETIME_SYNTAXES: Lint = lint::lint("mismatched_lifetime_syntaxes", Level::Warn, &[]);
pub const ELIDED_LIFETIMES_IN_PATHS: Lint = lint::lint("elided_lifetimes_in_paths", Level::Allow, &["rust_2018_idioms"]);

/// The lifetime resolution of a definition's signature and body.
pub(crate) fn names(prog: &Program, tcx: &Tcx, d: DefId) -> Arc<LifetimeResolution> { tcx.resolve_lifetime_names(prog, d) }

// ---------------------------------------------------------------- mismatched_lifetime_syntaxes

#[derive(Clone, Copy, PartialEq, Eq)]
enum Syntax { Implicit, Anonymous, Bound }

#[derive(Clone, Copy, PartialEq, Eq)]
enum Source { Reference, Path, Outlives, Precise }

#[derive(Clone, Copy, PartialEq, Eq)]
enum Cat { Hidden, Elided, Named }

#[derive(Clone, Copy)]
struct Info { res: LifetimeRes, cat: Cat, pos: u32 }

struct Collector<'a, 'b> {
    w: &'a W<'b>,
    names: &'a LifetimeResolution,
    out: Vec<Info>,
    /// argument position: `impl Trait` is an anonymous type parameter there, its bounds are not
    /// part of the type
    input: bool,
}

impl Collector<'_, '_> {
    fn push(&mut self, res: Option<LifetimeRes>, syntax: Syntax, source: Source, pos: u32) {
        let Some(res) = res else { return };
        // lifetimes that failed to resolve are reported elsewhere
        if matches!(res, LifetimeRes::Error | LifetimeRes::Infer) { return; }
        let cat = match (syntax, source) {
            (Syntax::Implicit, Source::Reference) | (Syntax::Anonymous, _) => Cat::Elided,
            (Syntax::Implicit, Source::Path) => Cat::Hidden,
            (Syntax::Bound, _) => Cat::Named,
            // `+ '_` is elided, `+ 'a` named; an implicit one cannot be written there
            (Syntax::Implicit, _) => return,
        };
        self.out.push(Info { res, cat, pos });
    }

    fn written(&mut self, lt: Ident, source: Source) {
        let syntax = if self.w.pf.text(lt) == "'_" { Syntax::Anonymous } else { Syntax::Bound };
        let res = self.names.named(lt.lo, lt.hi);
        self.push(res, syntax, source, lt.lo);
    }

    fn ty(&mut self, t: TyId) {
        let ast = self.w.ast;
        match *ast.ty(t) {
            Ty::Ref(lt, _, inner) => {
                match lt {
                    Some(l) => self.written(l, Source::Reference),
                    None => {
                        let pos = self.w.ty_start(t).unwrap_or(self.w.cur);
                        self.push(self.names.reference(t.0), Syntax::Implicit, Source::Reference, pos);
                    }
                }
                self.ty(inner);
            }
            Ty::Ptr(_, x) | Ty::Slice(x) | Ty::Array(x, _) | Ty::Paren(x) => self.ty(x),
            Ty::Tuple(l) => for &x in ast.list(l) { self.ty(x); },
            Ty::Fn(f) => {
                let f = *ast.fn_ptr(f);
                for &x in ast.list(f.params) { self.ty(x); }
                if let Some(r) = f.ret { self.ty(r); }
            }
            Ty::Path(p) => self.path(&p, t),
            Ty::ImplTrait(b) => if !self.input { self.bounds(b, t) },
            Ty::DynTrait(b, _) => self.bounds(b, t),
            Ty::Never | Ty::Infer | Ty::Mac(_) | Ty::ImplicitSelf | Ty::CVarArgs => {}
        }
    }

    fn bounds(&mut self, l: List<Bound>, owner: TyId) {
        let ast = self.w.ast;
        // the trait bounds first, the lifetime bound after them (intravisit TraitObject)
        for b in ast.list(l) {
            if let Bound::Trait { path, .. } = *b { self.path(&path, owner); }
        }
        for b in ast.list(l) {
            match *b {
                Bound::Lifetime(lt) => self.written(lt, Source::Outlives),
                Bound::Use(args) => {
                    if let Some(GenericArgs::Angle(l)) = ast.gargs(args) {
                        for a in ast.list(*l) { if let GenericArg::Lifetime(lt) = *a { self.written(lt, Source::Precise); } }
                    }
                }
                Bound::Trait { .. } => {}
            }
        }
    }

    fn path(&mut self, p: &Path, owner: TyId) {
        let ast = self.w.ast;
        if p.has_qself() {
            if let Some(q) = ast.qself(p) {
                self.ty(q.ty);
                if let Some(tp) = q.trait_path { self.path(&tp, owner); }
            }
        }
        for (i, seg) in ast.segs(p.segs).iter().enumerate() {
            // the hidden lifetimes come first in the lowered arguments
            let mut k = 0;
            while let Some(res) = self.names.path(p.segs.lo + i as u32, k) {
                let pos = self.w.ty_start(owner).unwrap_or(seg.name.lo);
                self.push(Some(res), Syntax::Implicit, Source::Path, pos);
                k += 1;
            }
            match ast.gargs(seg.args()) {
                Some(GenericArgs::Angle(l)) => {
                    for a in ast.list(*l) { if let GenericArg::Lifetime(lt) = *a { self.written(lt, Source::Path); } }
                    for a in ast.list(*l) { if let GenericArg::Type(t) = *a { self.ty(t); } }
                    for a in ast.list(*l) {
                        match *a {
                            GenericArg::Binding(_, _, t) => self.ty(t),
                            GenericArg::Constraint(_, b) => self.bounds(b, owner),
                            _ => {}
                        }
                    }
                }
                Some(GenericArgs::Paren(tys, ret)) => {
                    for &t in ast.list(*tys) { self.ty(t); }
                    if let Some(r) = ret { self.ty(*r); }
                }
                None => {}
            }
        }
    }
}

/// The position of the first token of a fn's parameter list (a `&self` receiver is the first
/// parameter).
fn params_start(w: &W, item: &Item) -> u32 {
    let pf = w.pf;
    let mut at = item.name.hi;
    let mut depth = 0i32;
    let n = pf.src_len;
    // generics: skip to the matching `>`
    loop {
        let b = pf.bytes(at.min(n), (at + 1).min(n));
        if b.is_empty() { return item.lo; }
        match b[0] {
            b'<' => depth += 1,
            b'>' => { depth -= 1; if depth <= 0 { at += 1; break; } }
            b'-' if pf.bytes(at + 1, (at + 2).min(n)) == b">" => at += 1,
            b'(' if depth == 0 => break,
            _ => {}
        }
        at += 1;
    }
    loop {
        let b = pf.bytes(at.min(n), (at + 1).min(n));
        if b.is_empty() { return item.lo; }
        if b[0] == b'(' { at += 1; break; }
        at += 1;
    }
    while let [c, ..] = pf.bytes(at.min(n), (at + 1).min(n)) {
        if matches!(c, b' ' | b'\t' | b'\n' | b'\r') { at += 1; } else { break; }
    }
    at
}

/// rustc_lint `LifetimeSyntax::check_fn_like`.
fn mismatched_lifetime_syntaxes(prog: &Program, tcx: &Tcx, d: DefId) {
    let def = prog.def(d);
    let pf = &prog.files[def.file as usize];
    let ast = &pf.ast;
    let item = *ast.item(def.item);
    let ItemKind::Fn(sig, _, _) = item.kind else { return };
    let sig = *ast.fn_sig(sig);
    // no output, or no input: nothing can disagree
    let Some(ret) = sig.ret else { return };
    if sig.self_param.is_none_or(|s| matches!(s, SelfParam::Value(_))) && ast.list(sig.params).is_empty() { return; }
    let names = names(prog, tcx, d);
    let mut w = W::new(prog, def.file, d);
    w.cur = item.lo;
    let mut outputs = Collector { w: &w, names: &names, out: Vec::new(), input: false };
    outputs.ty(ret);
    let outputs = outputs.out;
    if outputs.is_empty() { return; }
    let mut inputs = Collector { w: &w, names: &names, out: Vec::new(), input: true };
    match sig.self_param {
        Some(SelfParam::Ref(lt, _)) => match lt {
            Some(l) => inputs.written(l, Source::Reference),
            None => {
                let pos = params_start(&w, &item);
                inputs.push(names.self_reference(), Syntax::Implicit, Source::Reference, pos);
            }
        },
        Some(SelfParam::Typed(_, t)) => inputs.ty(t),
        _ => {}
    }
    for p in ast.list(sig.params) { inputs.ty(p.ty); }
    let inputs = inputs.out;
    // the groups, in the order of the output's lifetimes
    let mut keys: Vec<LifetimeRes> = Vec::new();
    for o in &outputs { if !keys.contains(&o.res) { keys.push(o.res); } }
    for key in keys {
        let ins: Vec<&Info> = inputs.iter().filter(|i| i.res == key).collect();
        let outs: Vec<&Info> = outputs.iter().filter(|i| i.res == key).collect();
        let Some(first) = ins.first() else { continue };
        if ins.iter().chain(outs.iter()).all(|i| i.cat == first.cat) { continue; }
        let count = |c: Cat| ins.iter().chain(outs.iter()).filter(|i| i.cat == c).count();
        let (hidden, elided, named) = (count(Cat::Hidden), count(Cat::Elided), count(Cat::Named));
        let msg = if named == 0 { "hiding a lifetime that's elided elsewhere is confusing" }
            else if elided == 0 { "hiding a lifetime that's named elsewhere is confusing" }
            else if hidden == 0 { "eliding a lifetime that's named elsewhere is confusing" }
            else { "hiding or eliding a lifetime that's named elsewhere is confusing" };
        // the primary spans: the hidden then the elided ones of the inputs, then of the outputs
        let pos = [&ins, &outs].iter().find_map(|side| {
            [Cat::Hidden, Cat::Elided].iter().find_map(|c| side.iter().find(|i| i.cat == *c).map(|i| i.pos))
        }).unwrap_or(item.lo);
        if lint::external(prog, def.file, pos) { continue; }
        lint::emit(prog, d, &MISMATCHED_LIFETIME_SYNTAXES, def.file, pos, msg);
    }
}

// ---------------------------------------------------------------- entry points

/// The definition-level passes of this file over one definition.
pub fn check_def_item(prog: &Program, tcx: &Tcx, d: DefId) {
    if matches!(prog.def(d).kind, DefKind::Fn | DefKind::AssocFn | DefKind::ForeignFn) {
        mismatched_lifetime_syntaxes(prog, tcx, d);
    }
}

// ---------------------------------------------------------------- attribute meta items

/// One item of an attribute's argument list (rustc_attr_parsing `MetaItemOrLitParser`).
#[derive(Debug)]
enum Meta {
    Lit { pos: u32, tok: Vec<u8> },
    Item { pos: u32, path: Vec<Vec<u8>>, args: Args },
}

#[derive(Debug)]
enum Args {
    None,
    List { pos: u32, items: Vec<Meta> },
    /// `= value`: the value's first token
    Value { pos: u32, tok: Vec<u8> },
}

impl Meta {
    fn pos(&self) -> u32 { match self { Meta::Lit { pos, .. } | Meta::Item { pos, .. } => *pos } }
}

fn is_literal_token(t: &[u8]) -> bool {
    match t.first() {
        Some(b'"') | Some(b'\'') | Some(b'0'..=b'9') => true,
        Some(b'b') | Some(b'r') | Some(b'c') => matches!(t.get(1), Some(b'"') | Some(b'\'') | Some(b'#')),
        _ => t == b"true" || t == b"false",
    }
}

/// Tokens `lo..hi` split into meta items at top-level commas.
fn parse_meta_items(pf: &crate::parser::ParsedFile, lo: usize, hi: usize) -> Vec<Meta> {
    let tok = |i: usize| pf.tok(i as u32);
    let text = |i: usize| { let t = tok(i); pf.bytes(t.lo, t.hi).to_vec() };
    let mut out = Vec::new();
    let mut i = lo;
    while i < hi {
        let first = text(i);
        let pos = tok(i).lo;
        if is_literal_token(&first) {
            out.push(Meta::Lit { pos, tok: first });
            i += 1;
        } else {
            let mut path = Vec::new();
            // `a::b::c` (a leading `::` is kept as an empty segment)
            loop {
                if i < hi && text(i) == b"::" { i += 1; continue; }
                if i < hi && !matches!(text(i).as_slice(), b"," | b"(" | b"=" | b")") { path.push(text(i)); i += 1; } else { break; }
                if i < hi && text(i) == b"::" { i += 1; } else { break; }
            }
            let args = if i < hi && text(i) == b"(" {
                let open = i;
                let mut depth = 0i32;
                while i < hi {
                    match text(i).as_slice() { b"(" | b"[" | b"{" => depth += 1, b")" | b"]" | b"}" => { depth -= 1; if depth == 0 { break; } } _ => {} }
                    i += 1;
                }
                let items = parse_meta_items(pf, open + 1, i.min(hi));
                i += 1;
                Args::List { pos: tok(open).lo, items }
            } else if i < hi && text(i) == b"=" {
                let vpos = if i + 1 < hi { tok(i + 1).lo } else { tok(i).lo };
                let v = if i + 1 < hi { text(i + 1) } else { Vec::new() };
                i += 2;
                // an expression value spans to the next comma
                let mut depth = 0i32;
                while i < hi {
                    match text(i).as_slice() { b"(" | b"[" | b"{" => depth += 1, b")" | b"]" | b"}" => depth -= 1, b"," if depth == 0 => break, _ => {} }
                    i += 1;
                }
                Args::Value { pos: vpos, tok: v }
            } else { Args::None };
            out.push(Meta::Item { pos, path, args });
        }
        // skip to after the next top-level comma
        let mut depth = 0i32;
        while i < hi {
            match text(i).as_slice() { b"(" | b"[" | b"{" => depth += 1, b")" | b"]" | b"}" => depth -= 1, b"," if depth == 0 => { i += 1; break; } _ => {} }
            i += 1;
        }
    }
    out
}

/// A string literal token's value; None when the token is no string.
fn string_value(t: &[u8]) -> Option<String> {
    let (body, raw) = match t {
        [b'"', rest @ .., b'"'] => (rest, false),
        [b'r', rest @ ..] => {
            let hashes = rest.iter().take_while(|&&c| c == b'#').count();
            let inner = &rest[hashes..];
            if inner.len() < 2 + hashes || inner[0] != b'"' { return None; }
            (&inner[1..inner.len() - 1 - hashes], true)
        }
        _ => return None,
    };
    let s = String::from_utf8_lossy(body).into_owned();
    if raw { return Some(s); }
    let mut out = String::new();
    let mut it = s.chars().peekable();
    while let Some(c) = it.next() {
        if c != '\\' { out.push(c); continue; }
        match it.next() {
            Some('n') => out.push('\n'),
            Some('r') => out.push('\r'),
            Some('t') => out.push('\t'),
            Some('0') => out.push('\0'),
            Some('\\') => out.push('\\'),
            Some('"') => out.push('"'),
            Some('\'') => out.push('\''),
            Some('x') => {
                let h: String = it.by_ref().take(2).collect();
                if let Some(c) = u32::from_str_radix(&h, 16).ok().and_then(char::from_u32) { out.push(c); }
            }
            Some('u') => {
                let mut h = String::new();
                if it.peek() == Some(&'{') { it.next(); while let Some(c) = it.next() { if c == '}' { break; } if c != '_' { h.push(c); } } }
                if let Some(c) = u32::from_str_radix(&h, 16).ok().and_then(char::from_u32) { out.push(c); }
            }
            Some('\n') => { while it.peek().is_some_and(|c| c.is_whitespace()) { it.next(); } }
            Some(c) => out.push(c),
            None => {}
        }
    }
    Some(out)
}

pub const INVALID_DOC_ATTRIBUTES: Lint = lint::lint("invalid_doc_attributes", Level::Warn, &[]);
pub const UNKNOWN_DIAGNOSTIC_ATTRIBUTES: Lint = lint::lint("unknown_diagnostic_attributes", Level::Warn, &["unknown_or_malformed_diagnostic_attributes"]);
pub const UNUSED_ATTRIBUTES: Lint = crate::lint_early::UNUSED_ATTRIBUTES;
/// A malformed attribute that rustc rejects outright (no lint of its own): never allowed.
pub const MALFORMED_ATTRIBUTE: Lint = lint::lint("malformed_attribute", Level::Forbid, &[]);

/// Whether `#![feature(name)]` is written in the crate root of `krate`.
fn feature_enabled(prog: &Program, krate: u32, name: &str) -> bool {
    let rm = prog.crates[krate as usize].root_mod;
    let file = prog.mods[rm as usize].file;
    prog.files[file as usize].ast.root_attrs.iter().any(|a| {
        lint::attr_path(prog, file, a) == b"feature" && lint::attr_args(prog, file, a).iter().any(|w| w == name)
    })
}

/// The attributes of one node, outer then inner, each with the file it was written in.
pub(crate) struct AttrNode<'a> {
    pub d: DefId,
    /// attributes of enclosing nodes between `d` and this node (for items without a definition: its own)
    pub inner: &'a [Attr],
    pub attrs: &'a [(u32, Attr)],
    /// the crate root's attributes
    pub is_crate: bool,
    /// an `extern crate` / module / crate (the targets of `#[macro_use]`)
    pub macro_use_target: bool,
}

const DIAGNOSTIC_ATTRIBUTES: &[(&str, Option<&str>)] = &[
    ("on_unimplemented", None), ("do_not_recommend", None), ("on_move", Some("diagnostic_on_move")),
    ("on_const", Some("diagnostic_on_const")), ("on_unknown", Some("diagnostic_on_unknown")),
    ("on_unmatch_args", Some("diagnostic_on_unmatch_args")),
];

/// `OnDuplicate::Warn` / `WarnButFutureError` of the single-attribute parsers of
/// rustc_attr_parsing: the second use of such an attribute on one node is unused.
const WARN_ON_DUPLICATE: &[&str] = &["cold", "export_name", "track_caller", "no_mangle", "crate_name", "recursion_limit",
    "type_length_limit", "no_std", "no_main", "windows_subsystem", "no_builtins", "diagnostic::do_not_recommend", "inline",
    "link_name", "link_section", "automatically_derived", "macro_escape", "macro_export", "must_use", "no_implicit_prelude",
    "no_link", "non_exhaustive", "path", "ignore", "should_panic"];

const CRATE_LEVEL_DOC: &[&str] = &["html_favicon_url", "html_logo_url", "html_no_source", "html_playground_url", "html_root_url",
    "issue_tracker_base_url", "rust_logo"];
const NOT_CRATE_LEVEL_DOC: &[&str] = &["alias", "keyword", "attribute", "fake_variadic", "search_unbox"];
const DOC_NO_ARGS: &[&str] = &["hidden", "masked", "notable_trait", "inline", "no_inline", "html_no_source", "fake_variadic", "search_unbox", "rust_logo"];

fn joined(path: &[Vec<u8>]) -> String {
    path.iter().map(|s| String::from_utf8_lossy(s).into_owned()).collect::<Vec<_>>().join("::")
}

/// Checks of rustc_attr_parsing / rustc_passes check_attr that read an attribute's arguments:
/// the `diagnostic` namespace, `doc` attributes, empty lint attributes, duplicate attributes,
/// `#[macro_use]` lists.
pub(crate) fn attr_checks(prog: &Program, n: &AttrNode) {
    let d = n.d;
    let krate = prog.def(d).krate;
    // duplicates: the first use of each attribute name is the one in force
    let mut seen: Vec<(Vec<u8>, u32)> = Vec::new();
    // `#[macro_use]` state: Some(first position) once all macros are used; the specific lists seen so far
    let mut use_all: Option<u32> = None;
    let mut specific: Vec<u32> = Vec::new();
    for &(file, a) in n.attrs {
        let pf = &prog.files[file as usize];
        let apos = crate::lint_early::attr_pos(pf, &a);
        let (lo, hi) = (a.toks.lo as usize, a.toks.hi as usize);
        let metas = parse_meta_items(pf, lo, hi);
        let Some(Meta::Item { path, args, .. }) = metas.first() else { continue };
        let emit = |lint: &Lint, pos: u32, msg: &str| {
            if !lint::external(prog, file, pos) { lint::emit_in(prog, d, n.inner, lint, file, pos, msg); }
        };
        let word = if path.len() == 1 { Some(String::from_utf8_lossy(&path[0]).into_owned()) } else { None };
        let full = joined(path);
        // ---- the diagnostic namespace
        if path.len() >= 2 && path[0] == b"diagnostic" {
            let name = String::from_utf8_lossy(&path[1]).into_owned();
            if !DIAGNOSTIC_ATTRIBUTES.iter().any(|(k, f)| *k == name && f.is_none_or(|f| feature_enabled(prog, krate, f))) {
                // the position of the name after `diagnostic::`
                let mut i = lo;
                while i < hi && pf.bytes(pf.tok(i as u32).lo, pf.tok(i as u32).hi) != b"::" { i += 1; }
                emit(&UNKNOWN_DIAGNOSTIC_ATTRIBUTES, pf.tok((i + 1).min(hi - 1) as u32).lo, "unknown diagnostic attribute");
            }
        }
        // ---- lint attributes: empty lists, `reason` only, crate-level-only lints
        if matches!(word.as_deref(), Some("allow" | "warn" | "deny" | "forbid" | "expect")) {
            let name = word.clone().unwrap();
            if let Args::List { items, .. } = args {
                let note = if items.is_empty() { Some(format!("attribute `{}` with an empty list has no effect", name)) }
                    else if let [Meta::Item { path, args: Args::Value { .. }, .. }] = &items[..] {
                        if path.len() == 1 && path[0] == b"reason" { Some(format!("attribute `{}` without any lints has no effect", name)) } else { None }
                    } else { None };
                if note.is_some() { emit(&UNUSED_ATTRIBUTES, apos, "unused attribute"); }
                else {
                    let names = |ls: &[&str]| items.iter().any(|m| matches!(m, Meta::Item { path, .. } if path.len() == 1 && ls.iter().any(|l| path[0] == l.as_bytes())));
                    if names(&["linker_messages", "linker_info"]) {
                        if !n.is_crate {
                            if a.inner { emit(&UNUSED_ATTRIBUTES, apos, "crate-level attribute should be in the root module"); }
                            else { emit(&UNUSED_ATTRIBUTES, apos, "crate-level attribute should be an inner attribute"); }
                        } else if never_needs_link(prog, krate) {
                            emit(&UNUSED_ATTRIBUTES, apos, "unused attribute");
                        }
                    } else if n.is_crate && names(&["dead_code_pub_in_binary"]) && !is_executable_crate(prog, krate) {
                        emit(&UNUSED_ATTRIBUTES, apos, "unused attribute");
                    }
                }
            }
        }
        // ---- duplicates
        let dup_name = if path.len() == 2 && path[0] == b"diagnostic" { Some(full.clone()) } else { word.clone() };
        if let Some(name) = &dup_name {
            if WARN_ON_DUPLICATE.contains(&name.as_str()) {
                if seen.iter().any(|(s, _)| s == name.as_bytes()) { emit(&UNUSED_ATTRIBUTES, apos, "unused attribute"); }
                else { seen.push((name.as_bytes().to_vec(), apos)); }
            }
            if name == "macro_use" && n.macro_use_target {
                match args {
                    Args::None => {
                        if use_all.is_some() { emit(&UNUSED_ATTRIBUTES, apos, "unused attribute"); }
                        else {
                            use_all = Some(apos);
                            for p in specific.drain(..) { emit(&UNUSED_ATTRIBUTES, p, "unused attribute"); }
                        }
                    }
                    Args::List { items, .. } => {
                        if items.is_empty() { continue; }
                        if use_all.is_some() { emit(&UNUSED_ATTRIBUTES, apos, "unused attribute"); }
                        else {
                            specific.push(apos);
                            for m in items {
                                let ok = matches!(m, Meta::Item { path, args: Args::None, .. } if path.len() == 1 && is_ident(&path[0]));
                                if !ok { emit(&MALFORMED_ATTRIBUTE, apos, "E0539: malformed `macro_use` attribute input"); }
                            }
                        }
                    }
                    Args::Value { .. } => emit(&MALFORMED_ATTRIBUTE, apos, "E0539: malformed `macro_use` attribute input"),
                }
            }
        }
        // ---- doc attributes
        if word.as_deref() == Some("doc") {
            doc_attr(prog, n, file, apos, args, &emit);
        }
    }
}

fn is_ident(t: &[u8]) -> bool {
    t.first().is_some_and(|c| c.is_ascii_alphabetic() || *c == b'_') && t.iter().all(|c| c.is_ascii_alphanumeric() || *c == b'_')
}

/// The crate types written as `#![crate_type = ".."]` of a crate (none: it is built as given).
fn declared_crate_types(prog: &Program, krate: u32) -> Vec<String> {
    let rm = prog.crates[krate as usize].root_mod;
    let file = prog.mods[rm as usize].file;
    prog.files[file as usize].ast.root_attrs.iter().filter(|a| lint::attr_path(prog, file, a) == b"crate_type")
        .filter_map(|a| lint::attr_text(prog, file, a).split('"').nth(1).map(str::to_string)).collect()
}

/// rustc check_attr: every crate type is `rlib` or `staticlib`.
fn never_needs_link(prog: &Program, krate: u32) -> bool {
    let t = declared_crate_types(prog, krate);
    !t.is_empty() && t.iter().all(|k| k == "lib" || k == "rlib" || k == "staticlib")
}

fn is_executable_crate(prog: &Program, krate: u32) -> bool {
    let t = declared_crate_types(prog, krate);
    t.is_empty() || t.iter().any(|k| k == "bin")
}

/// rustc_attr_parsing `DocParser`.
fn doc_attr(prog: &Program, n: &AttrNode, file: u32, apos: u32, args: &Args, emit: &dyn Fn(&Lint, u32, &str)) {
    let _ = prog;
    let invalid = |pos: u32, msg: &str| emit(&INVALID_DOC_ATTRIBUTES, pos, msg);
    let hard = |pos: u32, msg: &str| emit(&MALFORMED_ATTRIBUTE, pos, msg);
    match args {
        Args::None => {}
        Args::Value { pos, tok } => {
            if string_value(tok).is_none() { invalid(*pos, "malformed `doc` attribute input"); }
        }
        Args::List { items, .. } => {
            let mut aliases: Vec<String> = Vec::new();
            let mut add_alias = |alias: String, pos: u32| {
                if alias.is_empty() { hard(pos, "`#[doc(alias = \"...\")]` attribute cannot have empty value"); return; }
                if let Some(c) = alias.chars().find(|&c| c == '"' || c == '\'' || (c.is_whitespace() && c != ' ')) {
                    hard(pos, &format!("{:?} character isn't allowed in `#[doc(alias = \"...\")]`", c));
                    return;
                }
                if alias.starts_with(' ') || alias.ends_with(' ') { hard(pos, "`#[doc(alias = \"...\")]` cannot start or end with ' '"); return; }
                if n.is_crate { hard(pos, "`#![doc(alias = \"...\")]` isn't allowed as a crate-level attribute"); return; }
                if aliases.contains(&alias) { emit(&UNUSED_ATTRIBUTES, pos, "doc alias is duplicated"); }
                aliases.push(alias);
            };
            for m in items {
                match m {
                    Meta::Lit { pos, .. } => invalid(*pos, "expected this to be of the form `... = \"...\"`"),
                    Meta::Item { pos, path, args } => {
                        let word = if path.len() == 1 { Some(String::from_utf8_lossy(&path[0]).into_owned()) } else { None };
                        let Some(name) = word else {
                            invalid(*pos, &format!("unknown `doc` attribute `{}`", joined(path)));
                            continue;
                        };
                        if name == "alias" {
                            match args {
                                Args::None => hard(*pos, "doc alias attribute expects a string `#[doc(alias = \"a\")]` or a list of strings `#[doc(alias(\"a\", \"b\"))]`"),
                                Args::Value { pos, tok } => match string_value(tok) { Some(s) => add_alias(s, *pos), None => hard(apos, "E0539: malformed `doc` attribute input") },
                                Args::List { items, .. } => for i in items {
                                    match i {
                                        Meta::Lit { pos, tok } => match string_value(tok) { Some(s) => add_alias(s, *pos), None => hard(apos, "E0539: malformed `doc` attribute input") },
                                        Meta::Item { .. } => hard(apos, "E0539: malformed `doc` attribute input"),
                                    }
                                },
                            }
                            continue;
                        }
                        if CRATE_LEVEL_DOC.contains(&name.as_str()) && !n.is_crate { invalid(*pos, "this attribute can only be applied at the crate level"); continue; }
                        if DOC_NO_ARGS.contains(&name.as_str()) && !matches!(args, Args::None) { invalid(*pos, "didn't expect any arguments here"); continue; }
                        if NOT_CRATE_LEVEL_DOC.contains(&name.as_str()) && n.is_crate { hard(*pos, &format!("`#![doc({} = \"...\")]` isn't allowed as a crate-level attribute", name)); continue; }
                        match name.as_str() {
                            "hidden" | "masked" | "notable_trait" | "inline" | "no_inline" | "html_no_source" | "fake_variadic" | "search_unbox" | "rust_logo"
                            | "cfg" | "auto_cfg" | "keyword" | "attribute" | "html_favicon_url" | "html_logo_url" | "html_playground_url"
                            | "html_root_url" | "issue_tracker_base_url" => {}
                            "test" => match args {
                                Args::List { items, .. } => for t in items {
                                    match t {
                                        Meta::Lit { pos, .. } => invalid(*pos, "malformed `doc` attribute input"),
                                        Meta::Item { pos, path, .. } => {
                                            if path.len() != 1 { invalid(*pos, "`#![doc(test(...)]` does not take a literal"); continue; }
                                            let tn = String::from_utf8_lossy(&path[0]).into_owned();
                                            if tn != "no_crate_inject" && tn != "attr" { invalid(*pos, &format!("unknown `doc(test)` attribute `{}`", tn)); }
                                        }
                                    }
                                },
                                _ => invalid(*pos, "`#[doc(test(...)]` takes a list of attributes"),
                            },
                            "spotlight" | "passes" | "no_default_passes" | "plugins" => invalid(*pos, &format!("unknown `doc` attribute `{}`", name)),
                            "include" if matches!(args, Args::Value { .. }) => invalid(*pos, "unknown `doc` attribute `include`"),
                            _ => invalid(*pos, &format!("unknown `doc` attribute `{}`", name)),
                        }
                    }
                }
            }
        }
    }
    let _ = file;
}

// ---------------------------------------------------------------- items without a definition

/// The attribute checks of the `use` and `extern crate` items of every module of the checked
/// crates (they own no definition: the module's scope gives their lint levels).
pub fn check_module_items(prog: &Program, own: &[bool]) {
    for i in 0..prog.defs.len() {
        let def = prog.defs[i];
        if def.kind != DefKind::Mod || !own.get(def.krate as usize).copied().unwrap_or(false) { continue; }
        if prog.block_owner.get(&def.sub).is_some() { continue; }
        let d = DefId(i as u32);
        let m = &prog.mods[def.sub as usize];
        let is_root = def.parent == crate::program::NO_DEF;
        let (file, items): (u32, Vec<ItemId>) = if is_root || m.file != def.file {
            (m.file, prog.files[m.file as usize].ast.root_items.iter().copied().collect())
        } else {
            let ast = &prog.files[def.file as usize].ast;
            match ast.item(def.item).kind {
                ItemKind::Mod(Some(l)) => (def.file, ast.list(l).to_vec()),
                _ => continue,
            }
        };
        let ast = &prog.files[file as usize].ast;
        for it in items {
            let item = ast.item(it);
            if !matches!(item.kind, ItemKind::Use(_) | ItemKind::ExternCrate(_)) { continue; }
            let attrs: Vec<(u32, Attr)> = ast.list(item.attrs).iter().map(|a| (file, *a)).collect();
            if attrs.is_empty() { continue; }
            let own_attrs: Vec<Attr> = ast.list(item.attrs).to_vec();
            attr_checks(prog, &AttrNode { d, inner: &own_attrs, attrs: &attrs, is_crate: false, macro_use_target: matches!(item.kind, ItemKind::ExternCrate(_)) });
        }
    }
}
