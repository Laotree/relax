// What tests/cache_warm_const_edit/run.py edits, one item per probe.
#![allow(dead_code)]
use std::sync::atomic::AtomicU64;
pub const CONST_DIRECT: u64 = 1;
pub const CONST_THROUGH: u64 = 1;
pub const CONST_INLINED: u64 = 1;
pub const CONST_BASE: u64 = 1;
pub const CONST_DERIVED: u64 = CONST_BASE * 2;
pub const CONST_PATTERN: u64 = 1;
pub const CONST_LEN: usize = 1;
pub const CONST_LATE: u64 = 1;
pub const CONST_INCLUDE: &str = include_str!("data.txt");
pub const CONST_SAME: u64 = 1;
pub const CONST_MACRO: u64 = 1;
pub static STATIC_DIRECT: u64 = 1;
pub static STATIC_THROUGH: u64 = 1;
pub static STATIC_LATE: u64 = 1;

pub trait Kind {
    const K: u64;
}
pub struct A;
impl Kind for A {
    const K: u64 = 1;
}
pub struct B;
impl Kind for B {
    const K: u64 = 1;
}

// The value of an impl, reached only through a type argument of generic code: the code's text names
// a parameter, and the argument may be wrapped, foreign, inferred or hidden.
impl Kind for warm_const_dep::DepT {
    const K: u64 = 1;
}
pub struct E1;
impl warm_const_dep::DepKind for E1 {
    const DK: u64 = 1;
}
pub struct W3;
impl Kind for Vec<W3> {
    const K: u64 = 1;
}
impl Kind for u32 {
    const K: u64 = 1;
}
pub trait Mark {}
pub trait Blank {
    const BL: u64;
}
impl<T: Mark> Blank for T {
    const BL: u64 = 1;
}
pub struct M1;
impl Mark for M1 {}
pub struct Cl;
impl Kind for Cl {
    const K: u64 = 1;
}
pub struct Wrap<T>(pub T);
impl<T: Kind> Kind for Wrap<T> {
    const K: u64 = T::K + 1;
}
pub struct A4;
impl Kind for A4 {
    const K: u64 = 1;
}
pub struct Op;
impl Kind for Op {
    const K: u64 = 1;
}
pub fn make_op() -> impl Kind {
    Op
}
pub struct Inf;
impl Kind for Inf {
    const K: u64 = 1;
}
pub fn make_inf() -> Inf {
    Inf
}

pub trait Dflt {
    const D: u64 = 1;
    fn m() -> u64 {
        1
    }
}
pub struct Df;
impl Dflt for Df {}

pub trait Shape {
    type Out;
}
pub struct C;
impl Shape for C {
    type Out = u8;
}
pub struct C2;
impl Shape for C2 {
    type Out = u8;
}
#[repr(C)]
pub struct Holder<T: Shape> {
    pub v: T::Out,
}

// Consts in a type: an array's length, a const argument. (repr(C): a JIT's struct keeps room for
// fields an edit adds, and size_of would show that)
pub const CONST_GEN: usize = 1;
pub const CONST_GEN_TY: usize = 1;
pub const CONST_ARR: usize = 1;
pub const CONST_ARR_TY: usize = 1;
pub struct G<const N: usize>;
impl<const N: usize> Kind for G<N> {
    const K: u64 = N as u64;
}
#[repr(C)]
pub struct Buf {
    pub data: [u8; CONST_ARR],
}
pub struct D1;
impl Kind for D1 {
    const K: u64 = 1;
}
#[repr(C)]
pub struct BufK {
    pub data: [u8; <D1 as Kind>::K as usize],
}

// An impl comes or goes. A type's Drop decides what generic code folds and which glue it runs, and
// a type's Copy which of std's specializations an instance takes.
pub struct Plain;
// impl_added
pub struct Droppy;
impl Drop for Droppy {
    fn drop(&mut self) {}
}
pub static GLUE_DROPS: AtomicU64 = AtomicU64::new(0);
#[derive(Default)]
pub struct Glue;
// impl_added_glue
pub struct Sp(pub u64);
impl Clone for Sp {
    fn clone(&self) -> Sp {
        Sp(self.0 + 1)
    }
}
// impl_added_spec

#[inline(never)]
pub fn same_file() -> u64 {
    CONST_SAME
}

#[inline]
pub fn tiny() -> u64 {
    1
}

#[inline]
pub fn late_tiny() -> u64 {
    1
}

#[inline(always)]
pub fn late_always() -> u64 {
    1
}
