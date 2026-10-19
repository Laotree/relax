//! Privacy of paths (rustc_resolve `PrivacyError`, reported as E0603): a path segment looked
//! up in a module must name a binding the path's module can see. Item bindings carry their
//! written visibility (`pub(crate)`, `pub(super)`, `pub(in path)`); an import binding is `pub`
//! or private to its module.
use super::*;

pub struct PrivacyError {
    pub name: Sym,
    pub def: DefId,
    pub import: bool,
    pub ext: bool,
}

impl Program {
    /// Visibility of module `m`'s binding `name` -> `d`, the item's written visibility when the
    /// item is a plain item of `m` in the same crate.
    pub(super) fn precise_vis(&self, m: u32, name: Sym, ns_type: bool, d: DefId) -> BindVis {
        let md = &self.mods[m as usize];
        if !md.import_pub.contains_key(&(name, ns_type)) {
            let def = self.def(d);
            if def.krate == md.krate && def.scope == m && def.item.0 != u32::MAX {
                if let Some(it) = self.files.get(def.file as usize).and_then(|f| f.ast.items.get(def.item.0 as usize)) {
                    return self.vis_module(def.file, def.scope, &it.vis);
                }
            }
        }
        self.binding_vis(m, name, ns_type, d)
    }

    /// The first segment of `segs[1..]` (looked up in a module) that names a binding module
    /// `from` cannot see. `last_ns`: the namespace of the final segment (None: either, as in a
    /// `use`, where an inaccessible binding counts only when no namespace has an accessible one).
    pub fn path_privacy(&self, from: u32, global: bool, segs: &[(SegKind, Sym)], last_ns: Option<bool>, from_root: bool, in_use: bool) -> Option<PrivacyError> {
        if segs.len() < 2 || !self.own_crates.get(self.mods[from as usize].krate as usize).copied().unwrap_or(false) {
            return None;
        }
        let mut cur = self.resolve_mod_path(from, global, &segs[..1], from_root, in_use)?;
        for i in 1..segs.len() {
            let (kind, name) = segs[i];
            let d = self.def(cur);
            if d.kind != DefKind::Mod {
                return None;
            }
            match kind {
                SegKind::SelfValue => continue,
                SegKind::Super => {
                    let p = self.mods[d.sub as usize].parent_mod?;
                    cur = self.mods[p as usize].def;
                    continue;
                }
                SegKind::Ident => {}
                _ => return None,
            }
            let m = d.sub;
            let last = i + 1 == segs.len();
            let nss: &[bool] = if !last { &[true] } else {
                match last_ns { Some(true) => &[true], Some(false) => &[false], None => &[true, false] }
            };
            let mut next = None;
            let mut hidden = None;
            let mut visible = false;
            for &ns in nss {
                let mut q = GlobQuery { precise: true, ..Default::default() };
                let Some((fd, v)) = self.lookup_in_module_vis(m, name, ns, &mut q) else { continue };
                if self.vis_visible(v, from) {
                    visible = true;
                    if next.is_none() || ns { next = Some(fd); }
                } else if hidden.is_none() {
                    hidden = Some((fd, ns));
                }
            }
            if !visible {
                if let Some((fd, ns)) = hidden {
                    let flags = self.mods[m as usize].import_pub.get(&(name, ns)).copied();
                    return Some(PrivacyError { name, def: fd, import: flags.is_some(), ext: flags.map_or(false, |f| f & IMPORT_EXTERN != 0) });
                }
            }
            cur = next?;
        }
        None
    }

    /// rustc's `Res::descr` of what a path names.
    pub fn def_descr(&self, d: DefId) -> &'static str {
        match self.def(d).kind {
            DefKind::Mod => "module",
            DefKind::Fn | DefKind::AssocFn | DefKind::ForeignFn => "function",
            DefKind::Struct => "struct",
            DefKind::Union => "union",
            DefKind::Enum => "enum",
            DefKind::Variant => "variant",
            DefKind::Const | DefKind::AssocConst => "constant",
            DefKind::Static | DefKind::ForeignStatic => "static",
            DefKind::Trait => "trait",
            DefKind::TypeAlias | DefKind::AssocTy | DefKind::ForeignTy => "type alias",
            DefKind::MacroRules => "macro",
            _ => "item",
        }
    }

    /// "E0603: function `f` is private" / "module import `n` is private".
    pub fn privacy_message(&self, e: &PrivacyError) -> String {
        let n = self.syms.str(e.name);
        if e.ext {
            format!("E0603: crate import `{n}` is private")
        } else if e.import {
            format!("E0603: {} import `{n}` is private", self.def_descr(e.def))
        } else {
            format!("E0603: {} `{n}` is private", self.def_descr(e.def))
        }
    }

    /// E0603 for the `use` declarations of the own crates (`own[krate]`).
    pub fn import_privacy_errors(&self, own: &[bool]) -> Vec<String> {
        let mut out = Vec::new();
        for im in &self.imports {
            let krate = self.mods[im.module as usize].krate;
            if !own.get(krate as usize).copied().unwrap_or(false) || im.bound & 4 != 0 {
                continue;
            }
            let edition = self.crates[krate as usize].edition;
            let mut segs: &[(SegKind, Sym)] = &im.segs;
            let mut ns = if im.glob { Some(true) } else { None };
            if segs.last().map_or(false, |s| s.0 == SegKind::SelfValue) && segs.len() > 1 {
                segs = &segs[..segs.len() - 1];
                ns = Some(true);
            }
            if let Some(e) = self.path_privacy(im.module, im.global, segs, ns, edition < 2018, true) {
                out.push(self.record_error(im.file, im.pos, "resolve", self.privacy_message(&e)));
            }
        }
        out
    }
}
