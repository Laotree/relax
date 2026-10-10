//! Clone. Primitive impls are generated (num/prim_traits.rs); derive(Clone) is native.

#[cfg_attr(not(relax_check), lang = "clone")]
pub trait Clone: Sized {
    #[cfg_attr(not(relax_check), lang = "clone_fn")]
    fn clone(&self) -> Self;
    fn clone_from(&mut self, source: &Self) {
        *self = source.clone();
    }
}

// library/core/src/clone.rs:737: the never type is trivially Clone.
impl Clone for ! {
    fn clone(&self) -> ! { *self }
}

impl<'a, T: ?Sized> Clone for &'a T {
    fn clone(&self) -> &'a T {
        *self
    }
}

pub use crate::clone_uninit::CloneToUninit;
