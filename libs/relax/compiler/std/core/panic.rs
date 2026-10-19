// ported from library/core/src/panic/unwind_safe.rs @8d1a764
//! Panic locations and info (core part). Hooks and catch_unwind live in std::panic (std-os).

use crate::fmt;

/// A source location, as `#[track_caller]` / `Location::caller()` report it.
#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[cfg_attr(not(relax_check), lang = "panic_location")]
pub struct Location<'a> {
    // the file name and its terminating nul (rustc Location::file_bytes_with_nul)
    file_bytes_with_nul: &'a [u8],
    line: u32,
    col: u32,
}

impl<'a> Location<'a> {
    /// The location of the caller (through any chain of #[track_caller] fns).
    #[track_caller]
    pub fn caller() -> &'static Location<'static> {
        unsafe { crate::intrinsics_rt::caller_location() }
    }
    /// Built by Relax's lowering for panics and `Location::caller()`.
    pub const fn internal_constructor(file_bytes_with_nul: &'a [u8], line: u32, col: u32) -> Location<'a> {
        Location { file_bytes_with_nul, line, col }
    }
    pub const fn file(&self) -> &'a str {
        let bytes = self.file_bytes_with_nul;
        unsafe { crate::str::from_utf8_unchecked(crate::slice::from_raw_parts(bytes.as_ptr(), bytes.len() - 1)) }
    }
    pub const fn file_as_c_str(&self) -> &'a crate::ffi::CStr {
        unsafe { crate::ffi::CStr::from_bytes_with_nul_unchecked(self.file_bytes_with_nul) }
    }
    pub const fn line(&self) -> u32 {
        self.line
    }
    pub const fn column(&self) -> u32 {
        self.col
    }
}

impl<'a> fmt::Display for Location<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}:{}", self.file(), self.line, self.col)
    }
}

/// What a panic hook sees.
#[cfg_attr(not(relax_check), lang = "panic_info")]
pub struct PanicInfo<'a> {
    message: fmt::Arguments<'a>,
    location: &'a Location<'a>,
}

impl<'a> PanicInfo<'a> {
    pub(crate) fn new(message: fmt::Arguments<'a>, location: &'a Location<'a>) -> PanicInfo<'a> {
        PanicInfo { message, location }
    }
    pub fn message(&self) -> fmt::Arguments<'a> {
        self.message
    }
    pub fn location(&self) -> Option<&Location<'_>> {
        Some(self.location)
    }
}

impl<'a> fmt::Display for PanicInfo<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("panicked at ")?;
        fmt::Display::fmt(self.location, f)?;
        f.write_str(":\n")?;
        fmt::Display::fmt(&self.message, f)
    }
}

/// Marker traits kept for source compatibility (Relax is panic=abort, R11).
pub auto trait UnwindSafe {}
pub auto trait RefUnwindSafe {}

pub struct AssertUnwindSafe<T>(pub T);

// library/core/src/panic/unwind_safe.rs:194,203.
impl<T> UnwindSafe for AssertUnwindSafe<T> {}
impl<T> RefUnwindSafe for AssertUnwindSafe<T> {}

impl<T> crate::ops::Deref for AssertUnwindSafe<T> {
    type Target = T;
    fn deref(&self) -> &T {
        &self.0
    }
}
impl<T> crate::ops::DerefMut for AssertUnwindSafe<T> {
    fn deref_mut(&mut self) -> &mut T {
        &mut self.0
    }
}
/// As real std (library/core/src/panic/unwind_safe.rs): `catch_unwind(AssertUnwindSafe(|| ..))`
/// learns its result type R from this impl's Output.
impl<R, F: FnOnce() -> R> crate::ops::FnOnce<()> for AssertUnwindSafe<F> {
    type Output = R;
    // library/core/src/panic/unwind_safe.rs:270-277 @8d1a764.
    extern "rust-call" fn call_once(self, _args: ()) -> R {
        (self.0)()
    }
}
