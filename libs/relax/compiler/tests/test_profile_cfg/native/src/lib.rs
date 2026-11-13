extern "C" {
    fn profile_value() -> i32;
}

pub fn value() -> i32 {
    // SAFETY: the archive built with this crate defines profile_value with no preconditions.
    unsafe { profile_value() }
}
