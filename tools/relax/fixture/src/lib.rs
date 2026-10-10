//! Relax provided-crate fixture (loader-core.md section 8, step 3). rustc builds this crate into
//! the `relax` loader with its shims (feature `host-shims`); under `relax run` Relax loads its
//! source for the bin but binds the C-shaped non-generic fns below to the loader's code.
//! `bound()` tells which side ran: only the loader's build has the feature.
use std::collections::HashMap;
use std::sync::atomic::{AtomicU32, Ordering};

#[cfg(feature = "host-shims")]
#[path = "host_shims.rs"]
pub mod __host_shims;

/// true when this call ran the loader's rustc-built code
pub fn bound() -> bool {
    cfg!(feature = "host-shims")
}

pub fn add(a: i32, b: i64) -> i64 {
    a as i64 + b
}

pub fn mix(a: f32, b: f64, c: u8, d: bool, e: char) -> f64 {
    a as f64 * b + c as f64 + if d { 0.5 } else { 0.0 } + e as u32 as f64
}

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct P {
    pub x: f32,
    pub y: f32,
}

pub fn scale(p: P, k: f32) -> P {
    P { x: p.x * k, y: p.y * k }
}

/// passed and returned in memory
#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Big {
    pub a: [u64; 6],
}

pub fn big_make(x: u64) -> Big {
    Big { a: [x, x + 1, x + 2, x + 3, x + 4, x + 5] }
}

pub fn big_sum(b: Big) -> u64 {
    b.a.iter().sum()
}

pub fn text_len(s: &str) -> usize {
    s.chars().count()
}

pub fn sum(v: &[u32]) -> u64 {
    v.iter().map(|x| *x as u64).sum()
}

#[repr(u8)]
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Kind {
    A = 1,
    B = 7,
}

pub fn flip(k: Kind) -> Kind {
    match k {
        Kind::A => Kind::B,
        Kind::B => Kind::A,
    }
}

static DROPS: AtomicU32 = AtomicU32::new(0);

/// How many Registry values rustc's code dropped.
pub fn drops() -> u32 {
    DROPS.load(Ordering::Relaxed)
}

/// Opaque to Relax: rustc's Vec/HashMap inside.
pub struct Registry {
    names: Vec<String>,
    by_name: HashMap<String, u32>,
}

impl Registry {
    pub fn new() -> Registry {
        Registry { names: Vec::new(), by_name: HashMap::new() }
    }

    pub fn add(&mut self, name: &str) -> u32 {
        if let Some(id) = self.by_name.get(name) {
            return *id;
        }
        let id = self.names.len() as u32;
        self.names.push(name.to_string());
        self.by_name.insert(name.to_string(), id);
        id
    }

    pub fn len(&self) -> usize {
        self.names.len()
    }

    pub fn name_len(&self, id: u32) -> usize {
        self.names.get(id as usize).map_or(0, |n| n.len())
    }

    pub fn boom(&self, why: u32) -> u32 {
        if why > 0 {
            panic!("boom {} from the provided side", why);
        }
        0
    }

    /// generic: compiled by Relax from this source, calling the bound `add`
    pub fn add_all<'a, I: IntoIterator<Item = &'a str>>(&mut self, names: I) -> usize {
        let mut n = 0;
        for s in names {
            self.add(s);
            n += 1;
        }
        n
    }

    /// compiled on the caller's side (only calls methods)
    #[inline(always)]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl Default for Registry {
    fn default() -> Registry {
        Registry::new()
    }
}

impl Drop for Registry {
    fn drop(&mut self) {
        DROPS.fetch_add(1, Ordering::Relaxed);
    }
}

/// generic, so compiled by Relax: reads an opaque type's field, which Relax refuses (provided.rs)
pub fn names_peek<T>(r: &Registry, _t: T) -> usize {
    r.names.len()
}

/// Option<usize> by value (tag + payload in registers on Relax's side)
pub fn maybe(x: u32) -> Option<usize> {
    (x > 0).then_some(x as usize * 3)
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Io {
    pub kind: u8,
    pub name: u64,
    pub ty: u32,
    pub buffer_index: Option<usize>,
}

impl Io {
    pub fn buffer_index(&self) -> Option<usize> {
        self.buffer_index
    }
}

pub fn ios() -> &'static [Io] {
    static IOS: [Io; 2] = [Io { kind: 1, name: 7, ty: 2, buffer_index: None }, Io { kind: 2, name: 8, ty: 3, buffer_index: Some(3) }];
    &IOS
}

/// opaque (a String field: rustc's layout): its Hash / Debug / Display run rustc's impls, also
/// when Relax code hashes or formats it (jit.rs provided_fmt_hash; Stage's LiteralSite)
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Site {
    pub file: String,
    pub line: u32,
}

pub fn site(file: &str, line: u32) -> Site {
    Site { file: file.to_string(), line }
}

impl std::fmt::Display for Site {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}:{}", self.file, self.line)
    }
}
