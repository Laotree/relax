//! Interned namespace bindings for the cold demand planner. Qualified spellings
//! are rendered on demand; closure propagation carries sorted integer sets.
use crate::fxhash::HashMap;
use std::sync::{Arc, OnceLock};

#[derive(Clone, Default, PartialEq, Eq)]
pub enum Names {
    #[default]
    Empty,
    One([usize; 1]),
    Many(Vec<usize>),
}
impl Names {
    fn slice(&self) -> &[usize] {
        match self { Self::Empty => &[], Self::One(value) => value, Self::Many(values) => values }
    }
    pub fn is_empty(&self) -> bool {
        self.slice().is_empty()
    }
    pub fn iter(&self) -> std::slice::Iter<'_, usize> {
        self.slice().iter()
    }
    pub fn contains(&self, value: usize) -> bool {
        self.slice().binary_search(&value).is_ok()
    }
    pub fn contains_all(&self, values: &Self) -> bool {
        let mut remaining = self.slice();
        if values.slice().len() > remaining.len() { return false; }
        for &value in values {
            let at = remaining.partition_point(|&v| v < value);
            remaining = &remaining[at..];
            if remaining.first() != Some(&value) { return false; }
            remaining = &remaining[1..];
        }
        true
    }
    pub fn insert(&mut self, value: usize) {
        match self {
            Self::Empty => *self = Self::One([value]),
            Self::One([first]) if *first != value => {
                *self = Self::Many(vec![(*first).min(value), (*first).max(value)]);
            }
            Self::Many(values) => if let Err(at) = values.binary_search(&value) { values.insert(at, value); },
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
        if let Self::One([value]) = values {
            self.insert(*value);
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
        *self = Self::Many(merged);
    }
}
impl IntoIterator for Names {
    type Item = usize;
    type IntoIter = std::iter::Chain<std::option::IntoIter<usize>, std::vec::IntoIter<usize>>;
    fn into_iter(self) -> Self::IntoIter {
        let (one, many) = match self {
            Self::Empty => (None, Vec::new()),
            Self::One([value]) => (Some(value), Vec::new()),
            Self::Many(values) => (None, values),
        };
        one.into_iter().chain(many)
    }
}
impl<'a> IntoIterator for &'a Names {
    type Item = &'a usize;
    type IntoIter = std::slice::Iter<'a, usize>;
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
    Qualified { module: usize, name: usize, text: OnceLock<Box<str>> },
}

#[derive(Default)]
pub struct Bindings {
    ids: HashMap<Arc<str>, usize>,
    qualified: HashMap<(usize, usize), usize>,
    text: Vec<Spelling>,
    pub values: Vec<Binding>,
    pub modules: HashMap<usize, HashMap<usize, usize>>,
}
impl Bindings {
    pub fn id(&self, name: &str) -> Option<usize> {
        let mut parts = name.split("::");
        let mut id = *self.ids.get(parts.next()?)?;
        for part in parts { id = *self.qualified.get(&(id, *self.ids.get(part)?))?; }
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
        if let Some(&id) = self.qualified.get(&(module, name)) { return id; }
        let id = self.text.len();
        self.qualified.insert((module, name), id);
        self.text.push(Spelling::Qualified { module, name, text: OnceLock::new() });
        self.values.push(Binding::default());
        id
    }
    pub fn spelling(&self, id: usize) -> &str {
        match &self.text[id] {
            Spelling::Segment(text) => text,
            Spelling::Qualified { module, name, text } => text.get_or_init(||
                format!("{}::{}", self.spelling(*module), self.spelling(*name)).into_boxed_str()),
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
        let mut value = Binding { targets: Names::One([root]), public: true, ..Binding::default() };
        for &part in parts {
            let mut next = Binding::default();
            for &module in &value.targets {
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
