//! Content-validated Rust outlines. Tokens retain source offsets; no expression,
//! function body, macro expansion or derive is parsed to build an outline.
use crate::cfg::CfgSet;
use crate::crate_image::{Codec, Decode};
use crate::lexer::{Tok, T};
use crate::rs_index::NameIndex;
use std::path::PathBuf;
use std::sync::Arc;

pub struct Outline {
    pub tokens: Arc<Vec<Tok>>,
    pub active: Vec<Tok>,
    pub declarations: Vec<Tok>,
    pub index: NameIndex,
}

impl Outline {
    pub fn build(src: &[u8], edition: u16, cfg: &CfgSet) -> Option<Self> {
        let mut tokens = Vec::with_capacity(src.len() / 4);
        crate::lexer::lex(src, edition, &mut tokens).ok()?;
        // Validate delimiters before the cfg walker, whose inputs normally come
        // from a successfully lowered file. Collection reports malformed input.
        let _ = matching(&tokens)?;
        let active = crate::preload::configured_tokens(src, &tokens, cfg);
        let mut declarations = Vec::new();
        surface(&active, &matching(&active)?, 0, active.len(), &mut declarations);
        let index = index(src, &declarations)?;
        Some(Self { tokens: Arc::new(tokens), active, declarations, index })
    }
}

pub(crate) fn expanded_index(src: &[u8], tokens: &[Tok]) -> Option<NameIndex> {
    let mut declarations = Vec::new();
    surface(tokens, &matching(tokens)?, 0, tokens.len(), &mut declarations);
    index(src, &declarations)
}

fn index(src: &[u8], tokens: &[Tok]) -> Option<NameIndex> {
    // The name index reads no doc comments (an explicit #[doc = ...] attribute is a
    // token, not a comment): blank every comment between tokens and drop doc-comment
    // tokens, so building the token trees does not turn each doc line into an
    // attribute (positions are unchanged).
    let kept;
    let tokens = if tokens.iter().any(|t| t.kind == T::DocComment) {
        kept = tokens.iter().copied().filter(|t| t.kind != T::DocComment).collect::<Vec<_>>();
        &kept[..]
    } else { tokens };
    let mut copy = None::<Vec<u8>>;
    for w in tokens.windows(2) {
        let (lo, hi) = (w[0].hi as usize, w[1].lo as usize);
        if lo < hi && src[lo..hi].contains(&b'/') { copy.get_or_insert_with(|| src.to_vec())[lo..hi].fill(b' '); }
    }
    let src = copy.as_deref().unwrap_or(src);
    let stream = crate::pm_tokens::from_toks(src, tokens, &|lo, hi| crate::pm_tokens::Span {
        lo, hi, ..crate::pm_tokens::Span::DUMMY
    }).ok()?;
    Some(crate::rs_index::of_tokens(&stream))
}

fn matching(tokens: &[Tok]) -> Option<Vec<usize>> {
    let mut ends = vec![0; tokens.len()];
    let mut stack = Vec::new();
    for (i, t) in tokens.iter().enumerate() {
        match t.kind {
            T::OpenBrace | T::OpenParen | T::OpenBracket => stack.push((i, t.kind)),
            T::CloseBrace | T::CloseParen | T::CloseBracket => {
                let (open, kind) = stack.pop()?;
                if !matches!((kind, t.kind), (T::OpenBrace, T::CloseBrace)
                    | (T::OpenParen, T::CloseParen) | (T::OpenBracket, T::CloseBracket)) { return None; }
                ends[open] = i;
            }
            _ => {}
        }
    }
    stack.is_empty().then_some(ends)
}

// Keep declaration headers, imports, attributes and inline module/foreign
// scopes. A brace group belonging to an item body is represented by its original
// delimiters. Macro definitions' order and attributes survive; their transcribers
// remain in `active` for the existing textual macro scanner and demand analysis.
fn surface(tokens: &[Tok], ends: &[usize], mut at: usize, hi: usize, out: &mut Vec<Tok>) {
    let mut module = false;
    let mut foreign = false;
    let mut import = false;
    let mut initializer = false;
    while at < hi {
        let t = tokens[at];
        match t.kind {
            T::KwMod => module = true,
            T::KwExtern => foreign = true,
            T::KwFn | T::KwCrate => { foreign = false; initializer = false; }
            T::KwConst | T::KwStatic => initializer = true,
            T::KwUse => import = true,
            T::Semi => { module = false; foreign = false; import = false; initializer = false; }
            T::OpenParen | T::OpenBracket => {
                let end = ends[at];
                out.extend_from_slice(&tokens[at..=end]);
                at = end + 1;
                continue;
            }
            T::OpenBrace => {
                let end = ends[at];
                out.push(t);
                if import { out.extend_from_slice(&tokens[at + 1..end]); }
                else if module || foreign || initializer { surface(tokens, ends, at + 1, end, out); }
                out.push(tokens[end]);
                module = false; foreign = false; import = false; initializer = false;
                at = end + 1;
                continue;
            }
            _ => {}
        }
        out.push(t);
        at += 1;
    }
}

/// The compiler supplies its build identity and cache directory. Cache-off loads
/// never construct a Store, and editor overlays do not write disk outlines.
pub struct Store {
    directory: PathBuf,
    build: u128,
    writable: bool,
}
impl Store {
    pub fn new(directory: PathBuf, build: u128, writable: bool) -> Self { Self { directory, build, writable } }

    pub fn key(&self, src: &[u8], edition: u16, cfg: &CfgSet) -> u128 {
        let mut h = crate::sip::Sip128::new();
        h.str("relax-rs-outline-v1");
        h.u128(self.build);
        h.u128(crate::crate_image::file_hash("", src));
        h.u32(edition as u32);
        h.u128(cfg.session.options.fingerprint());
        let mut set = cfg.set.clone(); set.sort();
        for value in set { h.str(&value); }
        h.finish128()
    }

    fn path(&self, key: u128) -> PathBuf { self.directory.join(format!("{key:032x}.outline")) }

    pub fn read(&self, key: u128, src: &[u8]) -> Option<Outline> {
        let bytes = std::fs::read(self.path(key)).ok()?;
        let mut r = Decode::new(&bytes);
        if u128::get(&mut r)? != key { return None; }
        let checksum = u128::get(&mut r)?;
        if checksum != crate::crate_image::file_hash("", r.bytes) { return None; }
        let tokens = read_tokens(&mut r, src.len())?;
        let active = read_tokens(&mut r, src.len())?;
        let declarations = read_tokens(&mut r, src.len())?;
        if !r.bytes.is_empty() || tokens.last().map(|t| t.kind) != Some(T::Eof) { return None; }
        let _ = matching(&tokens)?;
        let _ = matching(&active)?;
        let _ = matching(&declarations)?;
        let index = index(src, &declarations)?;
        Some(Outline { tokens: Arc::new(tokens), active, declarations, index })
    }

    pub fn write(&self, key: u128, outline: &Outline) {
        if !self.writable { return; }
        let mut payload = Vec::new();
        for tokens in [&*outline.tokens, &outline.active, &outline.declarations] {
            tokens.len().put(&mut payload);
            for &Tok { kind, lo, hi } in tokens { kind.put(&mut payload); lo.put(&mut payload); hi.put(&mut payload); }
        }
        let mut bytes = Vec::new();
        key.put(&mut bytes);
        crate::crate_image::file_hash("", &payload).put(&mut bytes);
        bytes.extend_from_slice(&payload);
        // Each writer owns a distinct temporary file, even with shared crates
        // or concurrent compiler processes. Readers see a complete rename only.
        static NEXT: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
        let serial = NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        let temporary = self.directory.join(format!("{key:032x}.{}.{}.tmp", std::process::id(), serial));
        let mut created = false;
        let result = (|| -> std::io::Result<()> {
            use std::io::Write;
            std::fs::create_dir_all(&self.directory)?;
            let mut file = std::fs::OpenOptions::new().write(true).create_new(true).open(&temporary)?;
            created = true;
            file.write_all(&bytes)?;
            drop(file);
            std::fs::rename(&temporary, self.path(key))
        })();
        if let Err(error) = result {
            if created { let _ = std::fs::remove_file(&temporary); }
            eprintln!("rs-outline: cache write failed: {error}; using in-memory outline");
        }
    }
}

fn read_tokens(r: &mut Decode<'_>, source_len: usize) -> Option<Vec<Tok>> {
    let n = usize::get(r)?;
    if n > r.bytes.len() / 9 { return None; }
    (0..n).map(|_| {
        let token = Tok { kind: T::get(r)?, lo: u32::get(r)?, hi: u32::get(r)? };
        (token.lo <= token.hi && token.hi as usize <= source_len).then_some(token)
    }).collect()
}

/// Expand a macro-owned declaration stream in the caller's crate/module scope.
/// This read-only projection is also useful to embedders comparing a contract
/// against ordinary macro expansion; it never installs parse-reuse entries.
pub fn macro_declaration_index(input: &crate::pm::TokenStream, edition: u16,
    ctx: std::rc::Rc<crate::builtins::FileCtx>, table: Arc<crate::macros::MacroTable>,
    declaration_contract: bool,
) -> Result<NameIndex, String> {
    let input = crate::builtins::Expansion::from_stream(input, edition)?;
    let surface = if declaration_contract {
        crate::parser::rs_expand::expand_declarations(&input, edition, ctx, table)
    } else {
        let mut toks = input.toks.clone();
        let end = input.text.len() as u32;
        toks.push(Tok { kind: T::Eof, lo: end, hi: end });
        crate::parser::rs_expand::expand(input.text.as_bytes(), toks, edition, ctx, table)
    };
    if !surface.unknown.is_empty() { return Err(format!("unsupported macro surface: {:?}", surface.unknown)); }
    expanded_index(&surface.src, &surface.toks).ok_or_else(|| "invalid expanded declaration tokens".into())
}
