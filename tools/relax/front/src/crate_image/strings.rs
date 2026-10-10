//! Local string IDs for planning metadata. IDs never cross a payload boundary.
use super::{Codec, Decode};
use crate::fxhash::HashMap;
use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

/// The distinct strings of one payload. Each is stored once, back to back in one byte buffer
/// (ids are first-use order); an open-addressing table of ids finds a repeat without owning
/// a second copy of the text, so a payload's table costs its bytes plus 12 per distinct string.
#[derive(Default)]
pub(crate) struct Strings {
    bytes: Vec<u8>,
    /// end offset of string `id` in `bytes`
    ends: Vec<u32>,
    hashes: Vec<u32>,
    /// id + 1 per slot (0 empty); a power of two, at most half full
    slots: Vec<u32>,
}
impl Strings {
    fn hash(value: &[u8]) -> u32 {
        use std::hash::Hasher;
        let mut h = crate::fxhash::FxHasher::default();
        h.write(value);
        let h = h.finish();
        (h ^ (h >> 32)) as u32
    }
    fn text(&self, id: usize) -> &[u8] {
        let start = if id == 0 { 0 } else { self.ends[id - 1] as usize };
        &self.bytes[start..self.ends[id] as usize]
    }
    fn id_of(&mut self, value: &str) -> usize {
        if self.slots.is_empty() { self.slots = vec![0; 64]; }
        let hash = Self::hash(value.as_bytes());
        let mask = self.slots.len() - 1;
        let mut at = hash as usize & mask;
        loop {
            let slot = self.slots[at];
            if slot == 0 { break; }
            let id = slot as usize - 1;
            if self.hashes[id] == hash && self.text(id) == value.as_bytes() { return id; }
            at = (at + 1) & mask;
        }
        let id = self.ends.len();
        self.bytes.extend_from_slice(value.as_bytes());
        self.ends.push(u32::try_from(self.bytes.len()).expect("payload strings fit 32 bits"));
        self.hashes.push(hash);
        self.slots[at] = id as u32 + 1;
        if self.ends.len() * 2 > self.slots.len() {
            let mut slots = vec![0u32; self.slots.len() * 2];
            let mask = slots.len() - 1;
            for (id, &hash) in self.hashes.iter().enumerate() {
                let mut at = hash as usize & mask;
                while slots[at] != 0 { at = (at + 1) & mask; }
                slots[at] = id as u32 + 1;
            }
            self.slots = slots;
        }
        id
    }
    pub fn put(&mut self, value: &str, w: &mut Vec<u8>) {
        self.id_of(value).put(w);
    }
    /// The table as `Vec<String>` encodes it (count, then length + bytes each), then `body`.
    pub fn finish(self, body: Vec<u8>) -> Vec<u8> {
        let mut w = Vec::with_capacity(self.header_len() + body.len());
        self.write_header(&mut w);
        w.extend(body);
        w
    }
    fn header_len(&self) -> usize { 4 + 4 * self.ends.len() + self.bytes.len() }
    /// Appends the table (`Vec<String>`'s encoding) to `out`; the caller appends the body after it.
    pub fn write_header(&self, out: &mut Vec<u8>) {
        out.reserve(self.header_len());
        self.ends.len().put(out);
        for id in 0..self.ends.len() {
            let text = self.text(id);
            text.len().put(out);
            out.extend_from_slice(text);
        }
    }
}

pub(crate) trait Pack: Sized {
    fn pack(&self, w: &mut Vec<u8>, strings: &mut Strings);
    fn unpack(r: &mut Decode<'_>, strings: &[String]) -> Option<Self>;
    fn plain_size(&self) -> usize;
}
pub(crate) fn encode<T: Pack>(value: &T) -> Vec<u8> {
    let mut strings = Strings::default();
    let mut w = Vec::new();
    value.pack(&mut w, &mut strings);
    strings.finish(w)
}
pub(crate) fn decode<T: Pack>(bytes: &[u8]) -> Option<T> {
    let mut r = Decode::new(bytes);
    let strings = Vec::<String>::get(&mut r)?;
    let value = T::unpack(&mut r, &strings)?;
    r.bytes.is_empty().then_some(value)
}
impl Pack for String {
    fn pack(&self, w: &mut Vec<u8>, strings: &mut Strings) { strings.put(self, w); }
    fn unpack(r: &mut Decode<'_>, strings: &[String]) -> Option<Self> { strings.get(usize::get(r)?).cloned() }
    fn plain_size(&self) -> usize { 4 + self.len() }
}
macro_rules! scalar {
    ($($ty:ty),*) => {$(impl Pack for $ty {
        fn pack(&self, w: &mut Vec<u8>, _: &mut Strings) { self.put(w); }
        fn unpack(r: &mut Decode<'_>, _: &[String]) -> Option<Self> { Self::get(r) }
        fn plain_size(&self) -> usize { std::mem::size_of::<Self>() }
    })*};
}
scalar!(bool, u8, u32, u128);
impl Pack for usize {
    fn pack(&self, w: &mut Vec<u8>, _: &mut Strings) { self.put(w); }
    fn unpack(r: &mut Decode<'_>, _: &[String]) -> Option<Self> { Self::get(r) }
    fn plain_size(&self) -> usize { 4 }
}
impl<T: Pack> Pack for Vec<T> {
    fn pack(&self, w: &mut Vec<u8>, s: &mut Strings) { self.len().put(w); for value in self { value.pack(w, s); } }
    fn unpack(r: &mut Decode<'_>, s: &[String]) -> Option<Self> {
        let n = usize::get(r)?;
        if n > r.bytes.len() { return None; }
        (0..n).map(|_| T::unpack(r, s)).collect()
    }
    fn plain_size(&self) -> usize { 4 + self.iter().map(Pack::plain_size).sum::<usize>() }
}
impl<T: Pack> Pack for Option<T> {
    fn pack(&self, w: &mut Vec<u8>, s: &mut Strings) { self.is_some().put(w); if let Some(value) = self { value.pack(w, s); } }
    fn unpack(r: &mut Decode<'_>, s: &[String]) -> Option<Self> { Some(if bool::get(r)? { Some(T::unpack(r, s)?) } else { None }) }
    fn plain_size(&self) -> usize { 1 + self.as_ref().map_or(0, Pack::plain_size) }
}
impl<T: Pack> Pack for Arc<T> {
    fn pack(&self, w: &mut Vec<u8>, s: &mut Strings) { (**self).pack(w, s); }
    fn unpack(r: &mut Decode<'_>, s: &[String]) -> Option<Self> { Some(Arc::new(T::unpack(r, s)?)) }
    fn plain_size(&self) -> usize { (**self).plain_size() }
}
impl<T: Pack + Ord> Pack for BTreeSet<T> {
    fn pack(&self, w: &mut Vec<u8>, s: &mut Strings) { self.len().put(w); for value in self { value.pack(w, s); } }
    fn unpack(r: &mut Decode<'_>, s: &[String]) -> Option<Self> { Some(Vec::<T>::unpack(r, s)?.into_iter().collect()) }
    fn plain_size(&self) -> usize { 4 + self.iter().map(Pack::plain_size).sum::<usize>() }
}
impl<K: Pack + Ord, V: Pack> Pack for BTreeMap<K, V> {
    fn pack(&self, w: &mut Vec<u8>, s: &mut Strings) { self.len().put(w); for (k, v) in self { k.pack(w, s); v.pack(w, s); } }
    fn unpack(r: &mut Decode<'_>, s: &[String]) -> Option<Self> { Some(Vec::<(K, V)>::unpack(r, s)?.into_iter().collect()) }
    fn plain_size(&self) -> usize { 4 + self.iter().map(|(k, v)| k.plain_size() + v.plain_size()).sum::<usize>() }
}
macro_rules! tuple {
    ($($ty:ident:$ix:tt),+) => {impl<$($ty: Pack),+> Pack for ($($ty,)+) {
        fn pack(&self, w: &mut Vec<u8>, s: &mut Strings) { $(self.$ix.pack(w, s);)+ }
        fn unpack(r: &mut Decode<'_>, s: &[String]) -> Option<Self> { Some(($($ty::unpack(r, s)?,)+)) }
        fn plain_size(&self) -> usize { 0 $(+ self.$ix.plain_size())+ }
    }};
}
tuple!(A:0, B:1);
tuple!(A:0, B:1, C:2);
tuple!(A:0, B:1, C:2, D:3);
macro_rules! fields {
    ($ty:ty, $($field:ident),+ $(,)?) => {impl $crate::crate_image::strings::Pack for $ty {
        fn pack(&self, w: &mut Vec<u8>, s: &mut $crate::crate_image::strings::Strings) { $(self.$field.pack(w, s);)+ }
        fn unpack(r: &mut $crate::crate_image::Decode<'_>, s: &[String]) -> Option<Self> { Some(Self { $($field: $crate::crate_image::strings::Pack::unpack(r, s)?,)+ }) }
        fn plain_size(&self) -> usize { 0 $(+ self.$field.plain_size())+ }
    }};
}
pub(crate) use fields;
fields!(crate::macros::UseItem, module, path, bind, is_pub);

impl<K: Pack + Ord + std::hash::Hash, V: Pack> Pack for HashMap<K, V> {
    fn pack(&self, w: &mut Vec<u8>, s: &mut Strings) {
        let mut entries = self.iter().collect::<Vec<_>>();
        entries.sort_by(|a, b| a.0.cmp(b.0));
        entries.len().put(w);
        for (k, v) in entries { k.pack(w, s); v.pack(w, s); }
    }
    fn unpack(r: &mut Decode<'_>, s: &[String]) -> Option<Self> { Some(Vec::<(K, V)>::unpack(r, s)?.into_iter().collect()) }
    fn plain_size(&self) -> usize { 4 + self.iter().map(|(k, v)| k.plain_size() + v.plain_size()).sum::<usize>() }
}
impl<T: Pack + Ord + std::hash::Hash> Pack for crate::fxhash::HashSet<T> {
    fn pack(&self, w: &mut Vec<u8>, s: &mut Strings) {
        let mut entries = self.iter().collect::<Vec<_>>();
        entries.sort(); entries.len().put(w);
        for value in entries { value.pack(w, s); }
    }
    fn unpack(r: &mut Decode<'_>, s: &[String]) -> Option<Self> { Some(Vec::<T>::unpack(r, s)?.into_iter().collect()) }
    fn plain_size(&self) -> usize { 4 + self.iter().map(Pack::plain_size).sum::<usize>() }
}
impl Pack for crate::macros::CrateMods {
    fn pack(&self, w: &mut Vec<u8>, s: &mut Strings) {
        self.root.pack(w, s); self.src.pack(w, s); self.mods.pack(w, s);
        self.uses.pack(w, s); self.externs.pack(w, s); self.renames.pack(w, s);
    }
    fn unpack(r: &mut Decode<'_>, s: &[String]) -> Option<Self> {
        Some(Self { root: Pack::unpack(r, s)?, src: Pack::unpack(r, s)?, mods: Pack::unpack(r, s)?,
            uses: Pack::unpack(r, s)?, externs: Pack::unpack(r, s)?, renames: Pack::unpack(r, s)?, ..Self::default() })
    }
    fn plain_size(&self) -> usize {
        self.root.plain_size() + self.src.plain_size() + self.mods.plain_size()
            + self.uses.plain_size() + self.externs.plain_size() + self.renames.plain_size()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    /// The table keeps first-use ids, finds repeats through growth, and encodes as the Vec<String> it replaced.
    #[test]
    fn strings_table_matches_vec_encoding() {
        let mut strings = Strings::default();
        let mut w = Vec::new();
        let mut order: Vec<String> = Vec::new();
        for round in 0..3 {
            for n in 0..5000usize {
                let text = if n % 7 == 0 { String::new() } else { format!("core::mod{}::Name{}", n % 311, n * (round + 1) % 997) };
                let id = strings.id_of(&text);
                let expect = order.iter().position(|t| *t == text).unwrap_or_else(|| { order.push(text.clone()); order.len() - 1 });
                assert_eq!(id, expect);
                strings.put(&text, &mut w);
            }
        }
        let bytes = strings.finish(w.clone());
        let mut expect = super::super::encode(&order);
        expect.extend(w);
        assert_eq!(bytes, expect);
    }
}
