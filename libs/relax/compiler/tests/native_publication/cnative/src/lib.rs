extern "C" { fn cn_value() -> i32; }
pub fn value() -> i32 {
    // SAFETY: cn_value takes no arguments and returns an int32_t.
    unsafe { cn_value() }
}
