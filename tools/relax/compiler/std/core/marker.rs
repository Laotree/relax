//! Marker traits and PhantomData. Copy/Send/Sync/Sized/Unpin are known to the compiler.

#[cfg_attr(not(relax_check), lang = "sized")]
pub trait Sized {}
#[cfg_attr(not(relax_check), lang = "copy")]
pub trait Copy: crate::clone::Clone {}
// library/core/src/marker.rs:484: the never type is trivially Copy.
impl Copy for ! {}
// library/core/src/marker.rs:488: copying a shared reference does not copy its pointee.
impl<T: ?Sized> Copy for &T {}
pub auto trait Send {}
#[cfg_attr(not(relax_check), lang = "sync")]
pub auto trait Sync {}
// library/core/src/marker.rs:105,537-538: a shared borrow transfers only
// thread-safe access; a mutable borrow transfers exclusive access.
unsafe impl<T: ?Sized + Sync> Send for &T {}
unsafe impl<T: ?Sized + Send> Send for &mut T {}
#[cfg_attr(not(relax_check), lang = "unpin")]
pub auto trait Unpin {}
/// Implemented by every fn pointer type (real core's unstable FnPtr; impls in fn_ptr.rs).
#[cfg_attr(not(relax_check), lang = "fn_ptr_trait")]
pub trait FnPtr: Copy + Clone {
    #[cfg_attr(not(relax_check), lang = "fn_ptr_addr")]
    fn addr(self) -> *const ();
}

/// Zero-sized marker owning a `T` for variance/drop-check purposes.
#[cfg_attr(not(relax_check), lang = "phantom_data")]
pub struct PhantomData<T: ?Sized>;

impl<T: ?Sized> crate::clone::Clone for PhantomData<T> {
    fn clone(&self) -> PhantomData<T> {
        PhantomData
    }
}
impl<T: ?Sized> Copy for PhantomData<T> {}
impl<T: ?Sized> crate::default::Default for PhantomData<T> {
    fn default() -> PhantomData<T> {
        PhantomData
    }
}
impl<T: ?Sized> crate::cmp::PartialEq for PhantomData<T> {
    fn eq(&self, _o: &PhantomData<T>) -> bool {
        true
    }
}
impl<T: ?Sized> crate::cmp::Eq for PhantomData<T> {}
impl<T: ?Sized> crate::hash::Hash for PhantomData<T> {
    fn hash<H: crate::hash::Hasher>(&self, _state: &mut H) {}
}

pub struct PhantomPinned;

#[cfg_attr(not(relax_check), lang = "tuple_trait")]
pub trait Tuple {}

// library/core/src/marker.rs:1039-1051: a pointer moves independently of its pointee.
impl<T: ?Sized> Unpin for &T {}
impl<T: ?Sized> Unpin for &mut T {}
impl<T: ?Sized> Unpin for *const T {}
impl<T: ?Sized> Unpin for *mut T {}
impl !Unpin for PhantomPinned {}
