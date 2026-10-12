// run.py edits this file: each marked line is replaced by its edit, one scenario at a time.

pub fn stable_before() -> u32 { 7 }

pub struct Shape { pub a: u32, pub b: u32 } // EDIT layout

pub const SCALE: u32 = 3; // EDIT const

pub static LEVEL: u32 = 5; // EDIT static

pub trait Speak {
    fn speak(&self) -> u32;
    fn loud(&self) -> u32 { 1 }
}

pub struct Dog;

impl Speak for Dog {
    fn speak(&self) -> u32 { 10 } // EDIT body
    // EDIT impl
}

#[inline]
pub fn leaf() -> u32 { 100 } // EDIT inline

pub fn local_size() -> usize {
    struct Local { a: u8 } // EDIT local
    let l = Local { a: 1 };
    std::mem::size_of::<Local>() + l.a as usize
}

pub fn untouched_user() -> u32 { stable_before() + 1 }

pub fn stable_after() -> u32 { 9 }
