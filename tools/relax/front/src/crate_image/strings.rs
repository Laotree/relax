//! Local string IDs for planning metadata. IDs never cross a payload boundary.
use super::{Codec, Decode};
use crate::fxhash::HashMap;
use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

#[derive(Default)]
pub(crate) struct Strings {
    ids: HashMap<String, usize>,
    values: Vec<String>,
}
impl Strings {
    pub fn put(&mut self, value: &str, w: &mut Vec<u8>) {
        let id = if let Some(id) = self.ids.get(value) { *id } else {
            let id = self.values.len();
            self.values.push(value.to_owned());
            self.ids.insert(value.to_owned(), id);
            id
        };
        id.put(w);
    }
    pub fn finish(self, body: Vec<u8>) -> Vec<u8> {
        let mut w = super::encode(&self.values);
        w.extend(body);
        w
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
