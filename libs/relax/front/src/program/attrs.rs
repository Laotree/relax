//! Attribute resolution (rustc_resolve macros.rs `early_resolve_ident_in_lexical_scope` for
//! attributes): `#[name]` must be a built-in attribute, a registered tool's, a derive helper or
//! an attribute macro in scope; `#[a::b]` resolves `a` as a tool or a module path.
use super::*;
use crate::builtin_attrs::{is_builtin_attr, BUILTIN_TOOLS};
use crate::lexer::T;

/// The std derives, which have no helper attributes.
const STD_DERIVES: &[&str] = &["Clone", "Copy", "Debug", "Default", "Eq", "Hash", "Ord", "PartialEq", "PartialOrd"];

impl Program {
    /// E0433 / "cannot find attribute" for the attributes of the own crates' files.
    pub fn attribute_errors(&self, own: &[bool]) -> Vec<String> {
        let mut out = Vec::new();
        for (fi, f) in self.files.iter().enumerate() {
            let krate = self.file_crate.get(fi).copied().unwrap_or(u32::MAX);
            if !own.get(krate as usize).copied().unwrap_or(false) || f.token_input || fi == 0 {
                continue;
            }
            let module = match self.mods.iter().position(|m| m.file == fi as u32 && m.krate == krate) {
                Some(m) => m as u32,
                None => continue,
            };
            let text = |i: u32| f.tok_text(i).trim_start_matches("r#");
            let ranges: Vec<Attr> = f.ast.root_attrs.iter().chain(f.ast.attrs.iter()).copied().collect();
            // registered tools; derive helpers of non-std derives are not tracked: such a file
            // keeps its inert attributes
            let mut tools: Vec<&str> = Vec::new();
            let mut helpers = false;
            for a in &ranges {
                let (lo, hi) = (a.toks.lo, a.toks.hi);
                if hi <= lo || hi as usize > f.toks.len() {
                    continue;
                }
                match text(lo) {
                    "register_tool" => {
                        for i in lo + 1..hi {
                            if f.tok(i).kind == T::Ident {
                                tools.push(text(i));
                            }
                        }
                    }
                    "derive" => {
                        for i in lo + 1..hi {
                            if f.tok(i).kind == T::Ident && !STD_DERIVES.contains(&text(i)) && f.tok(i + 1).kind != T::PathSep {
                                // (`std::fmt::Debug` and the like name their last segment)
                                if f.tok(i.wrapping_sub(1)).kind != T::PathSep || !matches!(text(i), "Debug") {
                                    helpers = true;
                                }
                            }
                        }
                    }
                    _ => {}
                }
            }
            if helpers {
                continue;
            }
            for a in &ranges {
                let (lo, hi) = (a.toks.lo, a.toks.hi);
                if hi <= lo || hi as usize > f.toks.len() {
                    continue;
                }
                // the path: idents joined by `::`
                let mut segs: Vec<&str> = Vec::new();
                let mut i = lo;
                // `#[unsafe(name ..)]`
                if f.tok(i).kind == T::KwUnsafe && f.tok(i + 1).kind == T::OpenParen {
                    i += 2;
                }
                let first_i = i;
                let mut global = false;
                while i < hi {
                    match f.tok(i).kind {
                        T::Ident | T::RawIdent | T::KwCrate | T::KwSelfValue | T::KwSuper | T::KwSelfType => segs.push(text(i)),
                        T::PathSep => {
                            if i == first_i {
                                global = true;
                            }
                        }
                        _ => break,
                    }
                    i += 1;
                }
                if segs.is_empty() {
                    continue;
                }
                let pos = f.tok(first_i).lo;
                let tool = |n: &str| BUILTIN_TOOLS.contains(&n) || tools.contains(&n);
                let msg = if segs.len() == 1 && !global {
                    let n = segs[0];
                    if is_builtin_attr(n) || crate::macro_reg::has_attr(n) {
                        continue;
                    }
                    format!("cannot find attribute `{n}` in this scope")
                } else {
                    if !global && tool(segs[0]) {
                        continue;
                    }
                    let first = segs[0];
                    let kind = |k: &str| match k { "crate" => SegKind::Crate, "self" => SegKind::SelfValue, "super" => SegKind::Super, _ => SegKind::Ident };
                    let path: Vec<(SegKind, Sym)> = match segs.iter().map(|s| self.syms.get(s).map(|y| (kind(s), y))).collect::<Option<Vec<_>>>() {
                        Some(p) => p,
                        None => {
                            // a name never interned anywhere resolves nowhere
                            out.push(self.record_error(fi as u32, pos, "resolve", format!("E0433: failed to resolve: use of unresolved module or unlinked crate `{first}`")));
                            continue;
                        }
                    };
                    let edition = self.crates[krate as usize].edition;
                    let mut cur = None;
                    let mut fail = None;
                    for k in 1..=path.len() {
                        match self.resolve_mod_path(module, global, &path[..k], edition < 2018, false) {
                            Some(d) => cur = Some(d),
                            None => {
                                fail = Some(k - 1);
                                break;
                            }
                        }
                    }
                    match fail {
                        None => continue,
                        Some(0) => format!("E0433: failed to resolve: use of unresolved module or unlinked crate `{first}`"),
                        Some(k) => {
                            // a macro of another crate's module, or of this one: not a type-namespace item
                            let container = cur.unwrap_or(NO_DEF);
                            if container == NO_DEF || self.def(container).krate != krate {
                                continue;
                            }
                            if self.def(container).kind == DefKind::Mod && self.lookup_macro_in_container(container, path[k].1) {
                                continue;
                            }
                            format!("E0433: failed to resolve: could not find `{}` in `{}`", segs[k], segs[k - 1])
                        }
                    }
                };
                out.push(self.record_error(fi as u32, pos, "resolve", msg));
            }
        }
        out
    }
}
