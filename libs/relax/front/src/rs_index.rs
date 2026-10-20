//! Names defined by a Rust module before macro expansion.
use crate::lexer::{Tok, T};
use crate::pm_tokens::{Span as TokSpan, TokenStream, TokenTree};

#[derive(Clone, Debug, Default)]
pub struct NameIndex {
    pub items: Vec<IndexItem>,
    pub impls: Vec<IndexImpl>,
    pub macros: Vec<IndexMacro>,
    pub uses: Vec<IndexUse>,
    pub modules: Vec<IndexMod>,
    /// Inner `#![cfg(...)]` and `#![cfg_attr(...)]` attributes on this module.
    /// Outer attributes are retained on the individual entries below.
    pub cfgs: Vec<TokenStream>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ItemKind {
    Struct,
    Enum,
    Union,
    Trait,
    Fn,
    Const,
    Static,
    Type,
    Mod,
    Macro,
    UseReexport,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub enum Vis {
    #[default]
    Private,
    Public,
    /// The restriction inside `pub(...)`, in token spelling.
    Restricted(String),
}

#[derive(Clone, Debug)]
pub struct IndexItem {
    pub name: String,
    pub kind: ItemKind,
    pub vis: Vis,
    /// The name token's origin (or the `*` for a glob reexport).
    pub span: TokSpan,
    /// Complete outer cfg/cfg_attr attributes, in their authored order.
    pub cfg: Option<TokenStream>,
}

#[derive(Clone, Debug)]
pub struct IndexImpl {
    pub trait_path: Option<String>,
    /// The qualified path, with each generic argument replaced by `_`.
    /// Non-path self types retain their shape, e.g. `&[_]` or `(_,_)`.
    pub self_path: String,
    pub span: TokSpan,
    pub cfg: Option<TokenStream>,
}

#[derive(Clone, Debug)]
pub struct IndexMacro {
    pub name: String,
    pub macro_export: bool,
    /// Zero-based position among retained module items, before use-tree expansion.
    pub order: usize,
    pub span: TokSpan,
    pub cfg: Option<TokenStream>,
}

#[derive(Clone, Debug)]
pub struct IndexUse {
    /// One leaf of a use tree, including `::*` for a glob.
    pub path: String,
    pub alias: Option<String>,
    pub glob: bool,
    pub vis: Vis,
    pub order: usize,
    pub span: TokSpan,
    pub cfg: Option<TokenStream>,
}

#[derive(Clone, Debug)]
pub struct IndexMod {
    pub name: String,
    /// The string literal spelling from `#[path = ...]`, including its quotes.
    pub path: Option<String>,
    pub inline: Option<Box<NameIndex>>,
    pub vis: Vis,
    pub order: usize,
    pub span: TokSpan,
    pub cfg: Option<TokenStream>,
}

fn tokens_equal(a: &TokenStream, b: &TokenStream) -> bool {
    a.trees.len() == b.trees.len()
        && a.trees.iter().zip(&b.trees).all(|(a, b)| {
            a.span() == b.span()
                && match (a, b) {
                    (TokenTree::Ident(a), TokenTree::Ident(b)) => a.name == b.name && a.raw == b.raw,
                    (TokenTree::Literal(a), TokenTree::Literal(b)) => a.text == b.text,
                    (TokenTree::Punct(a), TokenTree::Punct(b)) => {
                        a.as_char() == b.as_char() && a.spacing() == b.spacing()
                    }
                    (TokenTree::Group(a), TokenTree::Group(b)) => {
                        a.delimiter() == b.delimiter() && tokens_equal(&a.stream, &b.stream)
                    }
                    _ => false,
                }
        })
}

fn cfg_equal(a: &Option<TokenStream>, b: &Option<TokenStream>) -> bool {
    match (a, b) {
        (None, None) => true,
        (Some(a), Some(b)) => tokens_equal(a, b),
        _ => false,
    }
}

macro_rules! entry_eq {
    ($ty:ident, $($field:ident),+ $(,)?) => {
        impl PartialEq for $ty {
            fn eq(&self, other: &Self) -> bool {
                $(self.$field == other.$field &&)+ cfg_equal(&self.cfg, &other.cfg)
            }
        }
        impl Eq for $ty {}
    };
}
entry_eq!(IndexItem, name, kind, vis, span);
entry_eq!(IndexImpl, trait_path, self_path, span);
entry_eq!(IndexMacro, name, macro_export, order, span);
entry_eq!(IndexUse, path, alias, glob, vis, order, span);
entry_eq!(IndexMod, name, path, inline, vis, order, span);

impl PartialEq for NameIndex {
    fn eq(&self, other: &Self) -> bool {
        self.items == other.items
            && self.impls == other.impls
            && self.macros == other.macros
            && self.uses == other.uses
            && self.modules == other.modules
            && self.cfgs.len() == other.cfgs.len()
            && self.cfgs.iter().zip(&other.cfgs).all(|(a, b)| tokens_equal(a, b))
    }
}
impl Eq for NameIndex {}

/// Index Rust tokens without expanding macros or inspecting bodies (`toks`: the module's
/// tokens, comments and doc comments dropped; None when the delimiters do not pair).
/// Lists preserve output order; grouped uses are expanded left to right.
/// Configuration tokens and all origin spans are preserved verbatim.
pub fn of_tokens(src: &[u8], toks: &[Tok]) -> Option<NameIndex> {
    let cx = Cx::build(src, toks)?;
    let mut index = NameIndex::default();
    let mut order = 0;
    index_items(&cx, &cx.top, &mut index, &mut order, &None);
    if std::env::var_os("MAKEPAD_RUN_VERIFY_INDEX").is_some() {
        verify_old(src, toks, &index);
    }
    Some(index)
}

/// TEMPORARY: the pm-tree walker's index of the same tokens, compared.
fn verify_old(src: &[u8], tokens: &[Tok], got: &NameIndex) {
    let kept;
    let tokens = if tokens.iter().any(|t| t.kind == T::DocComment) {
        kept = tokens.iter().copied().filter(|t| t.kind != T::DocComment).collect::<Vec<_>>();
        &kept[..]
    } else { tokens };
    let src = &blanked(src, tokens);
    let stream = crate::pm_tokens::from_toks(src, tokens, &|lo, hi| crate::pm_tokens::Span { lo, hi, ..crate::pm_tokens::Span::DUMMY }).expect("old index trees");
    let old = crate::rs_index_old::of_tokens(&stream);
    let (a, b) = (format!("{:?}", old), format!("{:?}", got));
    if a != b {
        let at = a.bytes().zip(b.bytes()).position(|(x, y)| x != y).unwrap_or(a.len().min(b.len()));
        if let Some(dir) = std::env::var_os("MAKEPAD_RUN_VERIFY_INDEX").filter(|d| !d.is_empty() && d != "1") {
            let dir = std::path::Path::new(&dir);
            let _ = std::fs::write(dir.join("idx.src"), src);
            let _ = std::fs::write(dir.join("idx.toks"), tokens.iter().flat_map(|t| { let (k, lo, hi) = (t.kind as u8, t.lo, t.hi); let mut v = vec![k]; v.extend_from_slice(&lo.to_le_bytes()); v.extend_from_slice(&hi.to_le_bytes()); v }).collect::<Vec<u8>>());
        }
        let lo = old_first_diff_pos(&a, at).saturating_sub(300);
        eprintln!("SURFACE near {lo}: {}", String::from_utf8_lossy(&src[lo.min(src.len())..(lo + 900).min(src.len())]));
        crate::tokbuf::verify_fail(&format!("name index differs from the tree walker's at byte {at}: old ...{} new ...{}", &a[at.saturating_sub(120)..(at + 200).min(a.len())], &b[at.saturating_sub(120)..(at + 200).min(b.len())]));
    }
}

/// What a token tree is. `Raw`: a raw identifier (`r#type`).
#[derive(Clone, Copy, PartialEq, Eq)]
enum K {
    Ident,
    Raw,
    Punct,
    Lit,
    Paren,
    Bracket,
    Brace,
}

/// A token tree over the flat tokens, 16 bytes, no text of its own: `tok` is its token (a
/// group's opening one), `off` the byte offset of its name / character in that token, `aux` a
/// group's id.
#[derive(Clone, Copy)]
struct Node {
    kind: K,
    tok: u32,
    off: u32,
    aux: u32,
}

struct Group {
    kids: Vec<Node>,
    close: u32,
}

/// The token trees of a token array (a punctuation character, a lifetime's `'` and name, an
/// `@id` pair are each their own tree, as `pm_tokens::from_toks` makes them).
struct Cx<'a> {
    src: &'a [u8],
    toks: &'a [Tok],
    groups: Vec<Group>,
    top: Vec<Node>,
}

impl<'a> Cx<'a> {
    fn build(src: &'a [u8], toks: &'a [Tok]) -> Option<Cx<'a>> {
        let mut groups: Vec<Group> = Vec::new();
        let mut stack: Vec<(u32, Vec<Node>)> = Vec::new();
        let mut cur: Vec<Node> = Vec::with_capacity(toks.len() / 2);
        for (i, t) in toks.iter().enumerate() {
            let i = i as u32;
            let node = |kind: K, off: u32| Node { kind, tok: i, off, aux: 0 };
            match t.kind {
                T::Eof => break,
                T::Comment | T::DocComment => {}
                T::AtId => {
                    cur.push(node(K::Punct, 0));
                    cur.push(node(K::Ident, 1));
                }
                T::OpenParen | T::OpenBracket | T::OpenBrace => {
                    stack.push((i, std::mem::take(&mut cur)));
                }
                T::CloseParen | T::CloseBracket | T::CloseBrace => {
                    let (open, outer) = stack.pop()?;
                    let kind = match (toks[open as usize].kind, t.kind) {
                        (T::OpenParen, T::CloseParen) => K::Paren,
                        (T::OpenBracket, T::CloseBracket) => K::Bracket,
                        (T::OpenBrace, T::CloseBrace) => K::Brace,
                        _ => return None,
                    };
                    let kids = std::mem::replace(&mut cur, outer);
                    groups.push(Group { kids, close: i });
                    cur.push(Node { kind, tok: open, off: 0, aux: groups.len() as u32 - 1 });
                }
                T::Ident => cur.push(node(K::Ident, 0)),
                T::RawIdent => cur.push(node(K::Raw, 2)),
                T::Lifetime => {
                    cur.push(node(K::Punct, 0));
                    cur.push(node(K::Ident, 1));
                }
                T::RawBody => return None,
                k if (T::KwAs as u8..=T::KwTry as u8).contains(&(k as u8)) => cur.push(node(K::Ident, 0)),
                T::Int | T::Float | T::Str | T::ByteStr | T::CStr | T::RawStr | T::Char | T::Byte | T::Colour | T::Duration => cur.push(node(K::Lit, 0)),
                _ => {
                    let text = &src[t.lo as usize..t.hi as usize];
                    if text.is_ascii() {
                        for j in 0..text.len() as u32 {
                            cur.push(node(K::Punct, j));
                        }
                    } else {
                        for (j, _) in std::str::from_utf8(text).unwrap_or("?").char_indices() {
                            cur.push(node(K::Punct, j as u32));
                        }
                    }
                }
            }
        }
        if !stack.is_empty() {
            return None;
        }
        Some(Cx { src, toks, groups, top: cur })
    }

    fn tok(&self, n: &Node) -> Tok {
        self.toks[n.tok as usize]
    }

    /// An identifier's name (or a literal's text).
    fn text(&self, n: &Node) -> &str {
        let t = self.tok(n);
        std::str::from_utf8(&self.src[(t.lo + n.off) as usize..t.hi as usize]).unwrap_or("?")
    }

    fn ch(&self, n: &Node) -> char {
        let t = self.tok(n);
        let at = (t.lo + n.off) as usize;
        let b = self.src[at];
        if b < 0x80 {
            b as char
        } else {
            std::str::from_utf8(&self.src[at..t.hi as usize]).ok().and_then(|s| s.chars().next()).unwrap_or('?')
        }
    }

    fn span(&self, n: &Node) -> TokSpan {
        let t = self.tok(n);
        let (lo, hi) = match n.kind {
            K::Paren | K::Bracket | K::Brace => (t.lo, self.toks[self.groups[n.aux as usize].close as usize].hi),
            K::Punct => (t.lo + n.off, t.lo + n.off + self.ch(n).len_utf8() as u32),
            K::Raw => (t.lo, t.hi),
            _ => (t.lo + n.off, t.hi),
        };
        TokSpan { lo, hi, ..TokSpan::DUMMY }
    }

    fn kids(&self, n: &Node) -> &[Node] {
        &self.groups[n.aux as usize].kids
    }

    /// The trees `nodes[from..to]` (consecutive siblings) as a token stream.
    fn stream(&self, nodes: &[Node]) -> TokenStream {
        let (Some(first), Some(last)) = (nodes.first(), nodes.last()) else { return TokenStream::new() };
        let a = first.tok as usize;
        let b = match last.kind {
            K::Paren | K::Bracket | K::Brace => self.groups[last.aux as usize].close as usize,
            _ => last.tok as usize,
        };
        crate::pm_tokens::from_toks(self.src, &self.toks[a..=b], &|lo, hi| TokSpan { lo, hi, ..TokSpan::DUMMY }).expect("balanced trees")
    }

    /// The printed spelling of a tree (`TokenTree::to_string`).
    fn spelling(&self, n: &Node) -> String {
        match n.kind {
            K::Raw => format!("r#{}", self.text(n)),
            K::Punct => self.ch(n).to_string(),
            K::Ident | K::Lit => self.text(n).to_owned(),
            _ => self.stream(std::slice::from_ref(n)).to_string(),
        }
    }
}

fn ident<'a>(cx: &'a Cx, token: Option<&Node>) -> &'a str {
    match token {
        Some(n) if matches!(n.kind, K::Ident | K::Raw) => cx.text(n),
        _ => "",
    }
}

fn word(cx: &Cx, token: Option<&Node>, expected: &str) -> bool {
    matches!(token, Some(n) if n.kind == K::Ident && cx.text(n) == expected)
}

fn punct(cx: &Cx, token: Option<&Node>, expected: char) -> bool {
    matches!(token, Some(n) if n.kind == K::Punct && cx.ch(n) == expected)
}

fn group<'a>(cx: &'a Cx, token: Option<&Node>, kind: K) -> Option<&'a [Node]> {
    match token {
        Some(n) if n.kind == kind => Some(cx.kids(n)),
        _ => None,
    }
}

fn is_group(n: &Node) -> bool {
    matches!(n.kind, K::Paren | K::Bracket | K::Brace)
}

#[derive(Default)]
struct Attributes {
    cfg: Option<TokenStream>,
    path: Option<String>,
    macro_export: bool,
}

fn attributes(cx: &Cx, tokens: &[Node], at: &mut usize, index: &mut NameIndex) -> Attributes {
    let mut attrs = Attributes::default();
    while punct(cx, tokens.get(*at), '#') {
        let start = *at;
        let inner = punct(cx, tokens.get(start + 1), '!');
        let end = start + if inner { 3 } else { 2 };
        let Some(body) = group(cx, tokens.get(end - 1), K::Bracket) else { break };
        match ident(cx, body.first()) {
            "cfg" | "cfg_attr" => {
                let cfg = cx.stream(&tokens[start..end]);
                if inner {
                    index.cfgs.push(cfg);
                } else {
                    attrs.cfg.get_or_insert_with(TokenStream::new).trees.extend(cfg.trees);
                }
            }
            "macro_export" if !inner => attrs.macro_export = true,
            "path" if !inner && punct(cx, body.get(1), '=') => {
                if let Some(n) = body.get(2).filter(|n| n.kind == K::Lit) {
                    attrs.path = Some(cx.text(n).to_owned());
                }
            }
            _ => {}
        }
        *at = end;
    }
    attrs
}

fn visibility(cx: &Cx, tokens: &[Node], at: &mut usize) -> Vis {
    if !word(cx, tokens.get(*at), "pub") { return Vis::Private; }
    *at += 1;
    if let Some(n) = tokens.get(*at).filter(|n| n.kind == K::Paren) {
        *at += 1;
        Vis::Restricted(cx.stream(cx.kids(n)).to_string())
    } else {
        Vis::Public
    }
}

fn combine_cfg(inherited: &Option<TokenStream>, cfg: Option<TokenStream>) -> Option<TokenStream> {
    match (inherited, cfg) {
        (None, cfg) => cfg,
        (Some(inherited), cfg) => {
            let mut inherited = inherited.clone();
            if let Some(cfg) = cfg { inherited.trees.extend(cfg.trees); }
            Some(inherited)
        }
    }
}

fn index_items(cx: &Cx, tokens: &[Node], index: &mut NameIndex, order: &mut usize, inherited: &Option<TokenStream>) {
    let mut at = 0;
    'items: while at < tokens.len() {
        if punct(cx, tokens.get(at), ';') { at += 1; continue; }
        let mut attrs = attributes(cx, tokens, &mut at, index);
        attrs.cfg = combine_cfg(inherited, attrs.cfg);
        if at == tokens.len() { break; }
        let vis = visibility(cx, tokens, &mut at);
        // Item modifiers, including foreign ABI strings. `const` followed by
        // an identifier is a declaration, whereas `const unsafe fn` is not.
        loop {
            let modifier = ["unsafe", "async", "default", "auto", "safe"].iter()
                .any(|m| word(cx, tokens.get(at), m));
            if modifier || word(cx, tokens.get(at), "const")
                && ["fn", "unsafe", "async", "extern"].iter().any(|m| word(cx, tokens.get(at + 1), m)) {
                at += 1;
            } else if word(cx, tokens.get(at), "extern") && !word(cx, tokens.get(at + 1), "crate") {
                at += 1;
                if matches!(tokens.get(at), Some(n) if n.kind == K::Lit) { at += 1; }
                if let Some(foreign) = group(cx, tokens.get(at), K::Brace) {
                    index_items(cx, foreign, index, order, &attrs.cfg);
                    at += 1;
                    continue 'items;
                }
            } else { break; }
        }
        if at >= tokens.len() { break; }
        let start = at;
        let keyword = ident(cx, tokens.get(at));
        let ordinal = *order;
        *order += 1;
        if word(cx, tokens.get(at), "impl") {
            let end = header_end(cx, tokens, at + 1);
            index.impls.push(implementation(cx, &tokens[at + 1..end], cx.span(&tokens[at]), attrs.cfg));
            at = (end + 1).min(tokens.len());
            continue;
        }
        if word(cx, tokens.get(at), "use") {
            let end = semicolon(cx, tokens, at + 1);
            use_tree(cx, &tokens[at + 1..end], "", &vis, ordinal, &attrs.cfg, index);
            at = (end + 1).min(tokens.len());
            continue;
        }
        if word(cx, tokens.get(at), "macro_rules") && punct(cx, tokens.get(at + 1), '!') {
            at += 2;
            if let Some(name) = tokens.get(at).filter(|n| matches!(n.kind, K::Ident | K::Raw)) {
                let text = cx.text(name).to_owned();
                index.macros.push(IndexMacro { name: text.clone(), macro_export: attrs.macro_export,
                    order: ordinal, span: cx.span(name), cfg: attrs.cfg.clone() });
                index.items.push(IndexItem { name: text, kind: ItemKind::Macro,
                    vis, span: cx.span(name), cfg: attrs.cfg });
            }
            at = macro_end(cx, tokens, at + 1);
            continue;
        }
        if word(cx, tokens.get(at), "extern") && word(cx, tokens.get(at + 1), "crate") {
            let end = semicolon(cx, tokens, at + 2);
            let name = if word(cx, tokens.get(at + 3), "as") { at + 4 } else { at + 2 };
            if let Some(name) = tokens.get(name).filter(|n| matches!(n.kind, K::Ident | K::Raw)) {
                index.items.push(IndexItem { name: cx.text(name).to_owned(), kind: ItemKind::Mod,
                    vis, span: cx.span(name), cfg: attrs.cfg });
            }
            at = (end + 1).min(tokens.len());
            continue;
        }
        let kind = match keyword {
            "struct" => Some(ItemKind::Struct), "enum" => Some(ItemKind::Enum),
            "union" => Some(ItemKind::Union), "trait" => Some(ItemKind::Trait),
            "fn" => Some(ItemKind::Fn), "const" => Some(ItemKind::Const),
            "static" => Some(ItemKind::Static), "type" => Some(ItemKind::Type),
            "mod" => Some(ItemKind::Mod), "macro" => Some(ItemKind::Macro),
            _ => None,
        }.filter(|_| !matches!(tokens.get(at), Some(n) if n.kind == K::Raw));
        if let Some(kind) = kind {
            // Impl blocks in anonymous const initializers are globally observable
            // (derive macros use this scope to avoid import-resolution cycles).
            // Block-local names themselves are not module declarations.
            if matches!(kind, ItemKind::Const | ItemKind::Static) {
                let end = semicolon(cx, tokens, at + 1);
                for token in &tokens[at + 1..end] {
                    if let Some(body) = group(cx, Some(token), K::Brace) {
                        let mut nested = NameIndex::default();
                        index_items(cx, body, &mut nested, &mut 0, &attrs.cfg);
                        let locals = nested.items.iter().filter(|item| matches!(item.kind,
                            ItemKind::Struct | ItemKind::Enum | ItemKind::Union | ItemKind::Trait | ItemKind::Type))
                            .map(|item| item.name.as_str()).collect::<Vec<_>>();
                        index.impls.extend(nested.impls.iter().filter(|head| {
                            let local = |path: &str| locals.contains(&path.split([':', '<']).next().unwrap_or(path));
                            !local(&head.self_path) && !head.trait_path.as_deref().is_some_and(local)
                        }).cloned().map(|mut head| {
                            // These imports belong to the const block, so they
                            // cannot be published as module bindings. Resolve
                            // them before lifting its observable impl heads.
                            let resolve = |path: &mut String| {
                                for import in &nested.uses {
                                    let name = import.alias.as_deref().unwrap_or_else(|| import.path.rsplit("::").next().unwrap_or(""));
                                    if path == name { *path = import.path.clone(); break; }
                                    if let Some(rest) = path.strip_prefix(&format!("{name}::")) {
                                        *path = format!("{}::{rest}", import.path); break;
                                    }
                                }
                            };
                            resolve(&mut head.self_path);
                            if let Some(path) = &mut head.trait_path { resolve(path); }
                            head
                        }));
                    }
                }
            }
            at += 1;
            if kind == ItemKind::Static && word(cx, tokens.get(at), "mut") { at += 1; }
            if let Some(name) = tokens.get(at).filter(|n| matches!(n.kind, K::Ident | K::Raw)) {
                let text = cx.text(name).to_owned();
                index.items.push(IndexItem { name: text.clone(), kind, vis: vis.clone(),
                    span: cx.span(name), cfg: attrs.cfg.clone() });
                if kind == ItemKind::Mod {
                    let inline = group(cx, tokens.get(at + 1), K::Brace).map(|body| {
                        let mut nested = NameIndex::default();
                        let mut order = 0;
                        index_items(cx, body, &mut nested, &mut order, &None);
                        Box::new(nested)
                    });
                    index.modules.push(IndexMod { name: text, path: attrs.path, inline,
                        vis, order: ordinal, span: cx.span(name), cfg: attrs.cfg });
                }
            }
            at = match kind {
                ItemKind::Const | ItemKind::Static | ItemKind::Type => (semicolon(cx, tokens, at + 1) + 1).min(tokens.len()),
                ItemKind::Macro => macro_end(cx, tokens, at + 1),
                _ => (header_end(cx, tokens, at + 1) + 1).min(tokens.len()),
            };
        } else {
            // A macro invocation can expand to anything. Its argument group
            // does not itself declare names in this module.
            at = macro_end(cx, tokens, start);
        }
    }
}

fn semicolon(cx: &Cx, tokens: &[Node], start: usize) -> usize {
    (start..tokens.len()).find(|&at| punct(cx, tokens.get(at), ';')).unwrap_or(tokens.len())
}

fn header_end(cx: &Cx, tokens: &[Node], start: usize) -> usize {
    let mut angles = 0usize;
    for at in start..tokens.len() {
        if punct(cx, tokens.get(at), ';') { return at; }
        if punct(cx, tokens.get(at), '<') { angles += 1; }
        if punct(cx, tokens.get(at), '>') && !punct(cx, at.checked_sub(1).and_then(|i| tokens.get(i)), '-') {
            angles = angles.saturating_sub(1);
        }
        if angles == 0 && group(cx, tokens.get(at), K::Brace).is_some()
            && !punct(cx, at.checked_sub(1).and_then(|i| tokens.get(i)), '!') { return at; }
    }
    tokens.len()
}

fn macro_end(cx: &Cx, tokens: &[Node], start: usize) -> usize {
    for at in start..tokens.len() {
        if punct(cx, tokens.get(at), ';') { return at + 1; }
        if let Some(body) = tokens.get(at).filter(|n| is_group(n)) {
            // macro 2.0 has a parameter group followed by a body group.
            let next = if body.kind == K::Paren
                && group(cx, tokens.get(at + 1), K::Brace).is_some() { at + 2 } else { at + 1 };
            return next + usize::from(punct(cx, tokens.get(next), ';'));
        }
    }
    tokens.len()
}

fn use_tree(cx: &Cx, tokens: &[Node], prefix: &str, vis: &Vis, order: usize, cfg: &Option<TokenStream>, index: &mut NameIndex) {
    let mut start = 0;
    for end in 0..=tokens.len() {
        if end != tokens.len() && !punct(cx, tokens.get(end), ',') { continue; }
        let branch = &tokens[start..end];
        start = end + 1;
        if branch.is_empty() { continue; }
        let mut path = prefix.to_owned();
        let mut alias = None;
        let mut span = cx.span(&branch[0]);
        let mut glob = false;
        let mut nested = false;
        let mut at = 0;
        while at < branch.len() {
            if let Some(body) = group(cx, branch.get(at), K::Brace) {
                use_tree(cx, body, &path, vis, order, cfg, index);
                nested = true;
                break;
            }
            if word(cx, branch.get(at), "as") {
                if let Some(name) = branch.get(at + 1) {
                    alias = Some(ident(cx, Some(name)).to_owned());
                    span = cx.span(name);
                }
                break;
            }
            if word(cx, branch.get(at), "self") && !path.is_empty() && at + 1 == branch.len()
                || word(cx, branch.get(at), "self") && !path.is_empty() && word(cx, branch.get(at + 1), "as") {
                path = path.trim_end_matches("::").to_owned();
            } else {
                path.push_str(&cx.spelling(&branch[at]));
            }
            if !punct(cx, branch.get(at), ':') { span = cx.span(&branch[at]); }
            glob |= punct(cx, branch.get(at), '*');
            at += 1;
        }
        if nested { continue; }
        if *vis != Vis::Private {
            let name = alias.clone().unwrap_or_else(|| path.rsplit("::").next().unwrap_or("").trim_start_matches("r#").into());
            index.items.push(IndexItem { name, kind: ItemKind::UseReexport, vis: vis.clone(), span, cfg: cfg.clone() });
        }
        index.uses.push(IndexUse { path, alias, glob, vis: vis.clone(), order, span, cfg: cfg.clone() });
    }
}

fn implementation(cx: &Cx, tokens: &[Node], span: TokSpan, cfg: Option<TokenStream>) -> IndexImpl {
    let mut start = 0;
    if punct(cx, tokens.first(), '<') { start = angle_end(cx, tokens, 0).min(tokens.len()); }
    let mut end = tokens.len();
    let mut split = None;
    let mut at = start;
    while at < end {
        if word(cx, tokens.get(at), "where") { end = at; break; }
        if word(cx, tokens.get(at), "for") { split = Some(at); }
        if punct(cx, tokens.get(at), '<') { at = angle_end(cx, tokens, at); }
        else { at += 1; }
    }
    let (trait_path, self_type) = if let Some(split) = split {
        (Some(erased_path(cx, &tokens[start..split], false)), &tokens[split + 1..end])
    } else { (None, &tokens[start..end]) };
    IndexImpl { trait_path, self_path: erased_path(cx, self_type, false), span, cfg }
}

fn angle_end(cx: &Cx, tokens: &[Node], open: usize) -> usize {
    let mut depth = 0usize;
    for at in open..tokens.len() {
        if punct(cx, tokens.get(at), '<') { depth += 1; }
        if punct(cx, tokens.get(at), '>') && !punct(cx, at.checked_sub(1).and_then(|i| tokens.get(i)), '-') {
            depth = depth.saturating_sub(1);
            if depth == 0 { return at + 1; }
        }
    }
    tokens.len()
}

fn erased_path(cx: &Cx, tokens: &[Node], last: bool) -> String {
    if last {
        // Keep references/pointers when shortening a qualified self type.
        let mut prefix = 0;
        while punct(cx, tokens.get(prefix), '&') || punct(cx, tokens.get(prefix), '*') {
            prefix += 1;
            if punct(cx, tokens.get(prefix), '\'') { prefix += 2; }
            if word(cx, tokens.get(prefix), "mut") || word(cx, tokens.get(prefix), "const") { prefix += 1; }
        }
        let mut segment = prefix;
        let mut at = prefix;
        while at < tokens.len() {
            if punct(cx, tokens.get(at), '<') {
                at = angle_end(cx, tokens, at);
            } else if punct(cx, tokens.get(at), ':') && punct(cx, tokens.get(at + 1), ':') {
                if !punct(cx, tokens.get(at + 2), '<') { segment = at + 2; }
                at += 2;
            } else { at += 1; }
        }
        if segment > prefix {
            let mut result = erased_path(cx, &tokens[..prefix], false);
            append_spelling(&mut result, &erased_path(cx, &tokens[segment..], false));
            return result;
        }
    }
    let mut out = String::new();
    let mut at = 0;
    while at < tokens.len() {
        if punct(cx, tokens.get(at), '<') {
            let end = angle_end(cx, tokens, at);
            let mut count = 0;
            let mut value = false;
            let mut arg = at + 1;
            while arg + 1 < end {
                if punct(cx, tokens.get(arg), ',') { count += usize::from(value); value = false; }
                else {
                    value = true;
                    if punct(cx, tokens.get(arg), '<') { arg = angle_end(cx, tokens, arg); continue; }
                }
                arg += 1;
            }
            count += usize::from(value);
            out.push('<');
            out.push_str(&vec!["_"; count].join(","));
            out.push('>');
            at = end;
        } else if let Some(value) = tokens.get(at).filter(|n| is_group(n)) {
            let kids = cx.kids(value);
            match value.kind {
                K::Paren => {
                    let count = if kids.is_empty() { 0 } else {
                        kids.iter().filter(|t| punct(cx, Some(t), ',')).count()
                            + usize::from(!punct(cx, kids.last(), ','))
                    };
                    out.push('(');
                    out.push_str(&vec!["_"; count].join(","));
                    if count == 1 { out.push(','); }
                    out.push(')');
                }
                K::Bracket => out.push_str(if kids.iter().any(|t| punct(cx, Some(t), ';')) { "[_;_]" } else { "[_]" }),
                _ => out.push('_'),
            }
            at += 1;
        } else {
            append_spelling(&mut out, &cx.spelling(&tokens[at]));
            at += 1;
        }
    }
    out
}

fn append_spelling(out: &mut String, text: &str) {
    let word = |c: char| c.is_alphanumeric() || c == '_';
    if out.chars().last().is_some_and(word) && text.chars().next().is_some_and(word) {
        out.push(' ');
    }
    out.push_str(text);
}

/// TEMPORARY: the old walker's comment blanking, without its bug for out-of-order tokens (a gap
/// between two tokens that are not neighbours in the text blanked the tokens in between).
fn blanked(src: &[u8], tokens: &[Tok]) -> Vec<u8> {
    let mut starts: Vec<u32> = tokens.iter().map(|t| t.lo).collect();
    starts.sort_unstable();
    let mut copy = src.to_vec();
    for w in tokens.windows(2) {
        let (lo, hi) = (w[0].hi as usize, w[1].lo as usize);
        if lo < hi && src[lo..hi].contains(&b'/') && starts.partition_point(|&s| (s as usize) < hi) == starts.partition_point(|&s| (s as usize) < lo + 1) {
            copy[lo..hi].fill(b' ');
        }
    }
    copy
}

/// TEMPORARY: the source position of the last `lo:` before byte `at` of a Debug string.
fn old_first_diff_pos(a: &str, at: usize) -> usize {
    let head = &a[..at.min(a.len())];
    head.rfind("lo: ").and_then(|i| head[i + 4..].split(',').next()?.trim().parse().ok()).unwrap_or(0)
}

#[cfg(test)]
mod old_vs_new {
    use super::*;
    fn walk(dir: &std::path::Path, out: &mut Vec<std::path::PathBuf>) {
        for e in std::fs::read_dir(dir).unwrap().flatten() {
            let p = e.path();
            if p.is_dir() { walk(&p, out) } else if p.extension().is_some_and(|x| x == "rs") { out.push(p) }
        }
    }
    #[test]
    fn std_files_index_like_the_tree_walker() {
        let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../compiler/std");
        let mut files = Vec::new();
        walk(&root, &mut files);
        let mut bad = 0;
        for f in &files {
            let src = std::fs::read(f).unwrap();
            let mut toks = Vec::new();
            if crate::lexer::lex(&src, 2021, &mut toks).is_err() { continue; }
            let Some(new) = of_tokens(&src, &toks) else { continue };
            let kept: Vec<Tok> = toks.iter().copied().filter(|t| t.kind != T::DocComment).collect();
            let copy = blanked(&src, &kept);
            let stream = crate::pm_tokens::from_toks(&copy, &kept, &|lo, hi| crate::pm_tokens::Span { lo, hi, ..crate::pm_tokens::Span::DUMMY }).unwrap();
            let old = crate::rs_index_old::of_tokens(&stream);
            let (a, b) = (format!("{:?}", old), format!("{:?}", new));
            if a != b {
                bad += 1;
                let at = a.bytes().zip(b.bytes()).position(|(x, y)| x != y).unwrap_or(a.len().min(b.len()));
                eprintln!("DIFF {} at {at}: old ...{} new ...{}", f.display(), &a[at.saturating_sub(200)..(at + 300).min(a.len())], &b[at.saturating_sub(200)..(at + 300).min(b.len())]);
                if bad > 3 { break; }
            }
        }
        assert_eq!(bad, 0);
    }

    #[test]
    fn dumped_surface() {
        let dir = std::path::Path::new("/private/tmp/claude-501/-Users-admin-makepad/b522d0ea-01b5-4b34-9114-217a9e69d7e3/scratchpad/idx");
        let Ok(src) = std::fs::read(dir.join("idx.src")) else { return };
        let raw = std::fs::read(dir.join("idx.toks")).unwrap();
        let toks: Vec<Tok> = raw.chunks(9).map(|c| Tok { kind: unsafe { std::mem::transmute::<u8, T>(c[0]) }, lo: u32::from_le_bytes(c[1..5].try_into().unwrap()), hi: u32::from_le_bytes(c[5..9].try_into().unwrap()) }).collect();
        let new = of_tokens(&src, &toks).unwrap();
        let kept: Vec<Tok> = toks.iter().copied().filter(|t| t.kind != T::DocComment).collect();
        let copy = blanked(&src, &kept);
        let stream = crate::pm_tokens::from_toks(&copy, &kept, &|lo, hi| crate::pm_tokens::Span { lo, hi, ..crate::pm_tokens::Span::DUMMY }).unwrap();
        let old = crate::rs_index_old::of_tokens(&stream);
        assert_eq!(format!("{:?}", old), format!("{:?}", new), "dumped surface");
        let kinds: Vec<(T, u32, u32)> = toks.iter().map(|t| (t.kind, t.lo, t.hi)).collect();
        // tokens around 41591
        let at = toks.iter().position(|t| t.lo >= 41591).unwrap();
        eprintln!("TOKS {:?}", &kinds[at.saturating_sub(3)..(at + 12).min(kinds.len())]);
        eprintln!("TEXT {}", String::from_utf8_lossy(&src[41500..41800.min(src.len())]));
        eprintln!("TEXT2 {}", String::from_utf8_lossy(&src[42100..42300.min(src.len())]));
    }
}
