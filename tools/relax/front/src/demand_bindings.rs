//! Interned namespace bindings for the cold demand planner. Qualified spellings
//! are rendered on demand; closure propagation carries sorted integer sets.
use crate::fxhash::HashMap;
use std::sync::{Arc, OnceLock};

/// A sorted set of binding ids. Ids are 32-bit (a graph has far fewer than 2^32 names): a
/// set is half the bytes it was with `usize`, and a grown set holds exactly its elements
/// (the planner keeps millions of them until the graph is recorded).
#[derive(Clone, Default, PartialEq, Eq)]
pub enum Names {
    #[default]
    Empty,
    One(u32),
    Many(Vec<u32>),
}
fn id32(value: usize) -> u32 {
    u32::try_from(value).expect("binding ids fit 32 bits")
}
impl Names {
    fn slice(&self) -> &[u32] {
        match self { Self::Empty => &[], Self::One(value) => std::slice::from_ref(value), Self::Many(values) => values }
    }
    /// `values` sorted ascending without duplicates.
    pub fn from_sorted(mut values: Vec<usize>) -> Self {
        match values.len() { 0 => Self::Empty, 1 => Self::One([values[0]]), _ => { values.shrink_to_fit(); Self::Many(values) } }
    }
    pub fn is_empty(&self) -> bool {
        self.slice().is_empty()
    }
    pub fn len(&self) -> usize {
        self.slice().len()
    }
    pub fn iter(&self) -> std::iter::Map<std::slice::Iter<'_, u32>, fn(&u32) -> usize> {
        self.slice().iter().map(|&id| id as usize)
    }
    pub fn contains(&self, value: usize) -> bool {
        u32::try_from(value).is_ok_and(|value| self.slice().binary_search(&value).is_ok())
    }
    pub fn contains_all(&self, values: &Self) -> bool {
        let mut remaining = self.slice();
        if values.slice().len() > remaining.len() { return false; }
        for &value in values.slice() {
            let at = remaining.partition_point(|&v| v < value);
            remaining = &remaining[at..];
            if remaining.first() != Some(&value) { return false; }
            remaining = &remaining[1..];
        }
        true
    }
    pub fn insert(&mut self, value: usize) {
        let value = id32(value);
        match self {
            Self::Empty => *self = Self::One(value),
            Self::One(first) if *first != value => {
                *self = Self::Many(vec![(*first).min(value), (*first).max(value)]);
            }
            Self::Many(values) => if let Err(at) = values.binary_search(&value) {
                values.reserve_exact(1);
                values.insert(at, value);
            },
            _ => {},
        }
    }
    pub fn extend(&mut self, values: &Self) {
        if values.is_empty() || self == values {
            return;
        }
        if self.is_empty() {
            self.clone_from(values);
            return;
        }
        if let Self::One(value) = values {
            self.insert(*value as usize);
            return;
        }
        // Repeated import waves commonly offer an already included subset.
        // Do not allocate a replacement union when no binding can change.
        if self.contains_all(values) { return; }
        let left = self.slice();
        let right = values.slice();
        let mut merged = Vec::with_capacity(left.len() + right.len());
        let (mut a, mut b) = (0, 0);
        while a < left.len() && b < right.len() {
            match left[a].cmp(&right[b]) {
                std::cmp::Ordering::Less => { merged.push(left[a]); a += 1; }
                std::cmp::Ordering::Greater => { merged.push(right[b]); b += 1; }
                std::cmp::Ordering::Equal => { merged.push(left[a]); a += 1; b += 1; }
            }
        }
        merged.extend_from_slice(&left[a..]);
        merged.extend_from_slice(&right[b..]);
        merged.shrink_to_fit();
        *self = Self::Many(merged);
    }
}
impl IntoIterator for Names {
    type Item = usize;
    type IntoIter = std::iter::Map<std::iter::Chain<std::option::IntoIter<u32>, std::vec::IntoIter<u32>>, fn(u32) -> usize>;
    fn into_iter(self) -> Self::IntoIter {
        let (one, many) = match self {
            Self::Empty => (None, Vec::new()),
            Self::One(value) => (Some(value), Vec::new()),
            Self::Many(values) => (None, values),
        };
        one.into_iter().chain(many).map(|id| id as usize)
    }
}
impl<'a> IntoIterator for &'a Names {
    type Item = usize;
    type IntoIter = std::iter::Map<std::slice::Iter<'a, u32>, fn(&u32) -> usize>;
    fn into_iter(self) -> Self::IntoIter { self.iter() }
}

#[derive(Clone, Default, PartialEq, Eq)]
pub struct Binding {
    pub public: bool,
    pub targets: Names,
    pub via: Names,
}
impl Binding {
    pub fn extend(&mut self, value: &Self) -> bool {
        let before = (self.targets.slice().len(), self.via.slice().len(), self.public);
        self.public |= value.public;
        self.targets.extend(&value.targets);
        self.via.extend(&value.via);
        before != (self.targets.slice().len(), self.via.slice().len(), self.public)
    }
}

enum Spelling {
    Segment(Arc<str>),
    Qualified { module: u32, name: u32, text: OnceLock<Box<str>> },
}

#[derive(Default)]
pub struct Bindings {
    ids: HashMap<Arc<str>, usize>,
    qualified: HashMap<(u32, u32), u32>,
    text: Vec<Spelling>,
    pub values: Vec<Binding>,
    pub modules: HashMap<usize, HashMap<usize, usize>>,
}
impl Bindings {
    pub fn id(&self, name: &str) -> Option<usize> {
        let mut parts = name.split("::");
        let mut id = *self.ids.get(parts.next()?)?;
        for part in parts { id = *self.qualified.get(&(id32(id), id32(*self.ids.get(part)?)))? as usize; }
        Some(id)
    }
    pub fn intern(&mut self, name: &str) -> usize {
        let mut parts = name.split("::");
        let mut id = self.segment(parts.next().unwrap());
        for part in parts {
            let name = self.segment(part);
            id = self.qualify(id, name);
        }
        id
    }
    /// `intern`, with `last` remembering the previous module part's id.
    pub fn intern_after(&mut self, name: &str, last: &mut (String, usize)) -> usize {
        let Some((module, local)) = name.rsplit_once("::") else { return self.intern(name); };
        if last.1 == usize::MAX || last.0 != module { *last = (module.to_owned(), self.intern(module)); }
        let local = self.segment(local);
        self.qualify(last.1, local)
    }
    /// The (module, name) ids a qualified id was interned from.
    pub fn parts(&self, id: usize) -> Option<(usize, usize)> {
        match self.text.get(id)? { Spelling::Qualified { module, name, .. } => Some((*module, *name)), Spelling::Segment(_) => None }
    }
    fn segment(&mut self, name: &str) -> usize {
        if let Some(&id) = self.ids.get(name) { return id; }
        let id = self.text.len();
        let name: Arc<str> = name.into();
        self.ids.insert(name.clone(), id);
        self.text.push(Spelling::Segment(name));
        self.values.push(Binding::default());
        id
    }
    fn qualify(&mut self, module: usize, name: usize) -> usize {
        let key = (id32(module), id32(name));
        if let Some(&id) = self.qualified.get(&key) { return id as usize; }
        let id = self.text.len();
        self.qualified.insert(key, id32(id));
        self.text.push(Spelling::Qualified { module: key.0, name: key.1, text: OnceLock::new() });
        self.values.push(Binding::default());
        id
    }
    /// For every id, the id `other.id(self.spelling(id))` returns: the spelling's segments
    /// folded through `other`'s tables (a qualified id's parts precede it).
    pub fn ids_in(&self, other: &Bindings) -> Vec<Option<usize>> {
        fn fold(this: &Bindings, other: &Bindings, acc: usize, id: usize) -> Option<usize> {
            match &this.text[id] {
                Spelling::Segment(text) => other.qualified.get(&(id32(acc), id32(*other.ids.get(text)?))).map(|&id| id as usize),
                Spelling::Qualified { module, name, .. } => fold(this, other, fold(this, other, acc, *module as usize)?, *name as usize),
            }
        }
        let mut map: Vec<Option<usize>> = Vec::with_capacity(self.text.len());
        for id in 0..self.text.len() {
            let mapped = match &self.text[id] {
                Spelling::Segment(text) => other.ids.get(text).copied(),
                Spelling::Qualified { module, name, .. } => map[*module as usize].and_then(|m| fold(self, other, m, *name as usize)),
            };
            map.push(mapped);
        }
        map
    }
    pub fn spelling(&self, id: usize) -> &str {
        match &self.text[id] {
            Spelling::Segment(text) => text,
            Spelling::Qualified { module, name, text } => text.get_or_init(||
                format!("{}::{}", self.spelling(*module as usize), self.spelling(*name as usize)).into_boxed_str()),
        }
    }
    /// The spelling as an owned string, without keeping it: a snapshot renders every binding of a
    /// crate once (1.4 M on a cold Stage) and would otherwise leave all of them cached in `text`.
    pub fn spelling_string(&self, id: usize) -> String {
        let mut out = String::new();
        self.render(id, &mut out);
        out
    }
    fn render(&self, id: usize, out: &mut String) {
        match &self.text[id] {
            Spelling::Segment(text) => out.push_str(text),
            Spelling::Qualified { module, name, text } => match text.get() {
                Some(text) => out.push_str(text),
                None => { self.render(*module as usize, out); out.push_str("::"); self.render(*name as usize, out); }
            },
        }
    }
    pub fn entry(&mut self, module: usize, name: usize) -> usize {
        if let Some(&id) = self.modules.get(&module).and_then(|names| names.get(&name)) { return id; }
        // Glob forwarding creates many aliases never queried by source. Keep
        // their identity as a pair; render a qualified spelling only on demand.
        let id = self.qualify(module, name);
        self.modules.entry(module).or_default().insert(name, id);
        id
    }
    pub fn path(&mut self, path: &str) -> Vec<usize> {
        path.split("::").map(|part| self.segment(part)).collect()
    }
    pub fn lookup(&self, path: &str) -> Binding {
        let Some(parts) = path.split("::").map(|part| self.id(part)).collect::<Option<Vec<_>>>() else { return Binding::default(); };
        self.watched(&parts, |_, _| {})
    }
    pub fn watched(&self, path: &[usize], mut watch: impl FnMut(usize, usize)) -> Binding {
        let Some((&root, parts)) = path.split_first() else { return Binding::default(); };
        let mut value = Binding { targets: Names::One(id32(root)), public: true, ..Binding::default() };
        for &part in parts {
            let mut next = Binding::default();
            for module in &value.targets {
                watch(module, part);
                if let Some(&id) = self.modules.get(&module).and_then(|names| names.get(&part)) {
                    next.extend(&self.values[id]);
                }
            }
            next.via.extend(&value.via);
            value = next;
            if value.targets.is_empty() { break; }
        }
        value
    }
}
