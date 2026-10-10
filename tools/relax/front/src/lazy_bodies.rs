//! Scratch storage and immutable arena segments for deferred Rust bodies.
use super::*;
use std::sync::Arc;

/// Mutable parser input retained under the file's publication lock. Each input
/// byte/token is copied from the declaration file once, then expansions append.
/// Published FileParts contain only the newly appended immutable suffix.
#[derive(Default)]
pub struct BodyScratch {
    toks: Vec<Tok>,
    ext: Vec<u8>,
    exp_map: Vec<(u32, u32, u32)>,
    tok_origin: Vec<(u32, u32, u32)>,
    token_origins: Vec<TokenOrigin>,
    rules_exp: Vec<(u32, u32, u32)>,
    body_origin: Vec<(u32, u32, u32)>,
}

impl BodyScratch {
    pub(super) fn parser<'a>(pf: &'a ParsedFile, sess: &'a Arc<crate::Session>, saved: Option<Self>) -> Parser<'a> {
        let state = saved.unwrap_or_else(|| {
            let mut state = Self {
                toks: pf.toks.to_vec(), ext: pf.src[pf.src_len as usize..].to_vec(),
                exp_map: pf.exp_map.to_vec(), tok_origin: pf.tok_origin.to_vec(),
                token_origins: pf.token_origins.to_vec(), rules_exp: pf.rules_exp.to_vec(),
                body_origin: pf.body_origin.to_vec(),
            };
            // The default policy may already have published its batched part.
            for part in pf.parts() {
                state.ext.extend_from_slice(&part.ext);
                state.toks.extend_from_slice(&part.toks);
                state.exp_map.extend_from_slice(&part.exp_map);
                state.tok_origin.extend_from_slice(&part.tok_origin);
                state.token_origins.extend_from_slice(&part.token_origins);
                state.rules_exp.extend_from_slice(&part.rules_exp);
                state.body_origin.extend_from_slice(&part.body_origin);
            }
            state
        });
        let mut p = Parser::new(sess, &pf.src[..pf.src_len as usize], state.toks, pf.edition);
        p.ext = state.ext;
        p.exp_map = state.exp_map;
        p.tok_origin = state.tok_origin;
        p.token_origins = state.token_origins;
        p.rules_exp = state.rules_exp;
        p.body_origin = state.body_origin;
        p
    }

    pub(super) fn retain(p: &mut Parser<'_>) -> Self {
        Self {
            toks: std::mem::take(&mut p.toks), ext: std::mem::take(&mut p.ext),
            exp_map: std::mem::take(&mut p.exp_map), tok_origin: std::mem::take(&mut p.tok_origin),
            token_origins: std::mem::take(&mut p.token_origins), rules_exp: std::mem::take(&mut p.rules_exp),
            body_origin: std::mem::take(&mut p.body_origin),
        }
    }
}

impl ParsedFile {
    pub fn parts(&self) -> impl Iterator<Item = &FilePart> {
        std::iter::successors(self.part.get().map(|p| &**p), |p| p.next.get().map(|p| &**p))
    }

    pub fn part_at(&self, pos: u32) -> Option<&FilePart> {
        self.parts().take_while(|p| p.src_base <= pos).last()
    }

}

impl crate::cfg::SourceTokens for ParsedFile {
    fn token(&self, i: u32) -> Tok { self.tok(i) }
    fn bytes(&self, lo: u32, hi: u32) -> &[u8] { self.bytes(lo, hi) }
}
