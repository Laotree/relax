extern "C" {
    fn cn_add(a: i32, b: i32) -> i32;
    fn cn_home_is_unset() -> i32;
}
pub fn add(a: i32, b: i32) -> i32 {
    // SAFETY: cn_add accepts and returns scalar int32_t values.
    unsafe { cn_add(a, b) }
}
pub fn home_is_unset() -> bool {
    // SAFETY: the C function takes no arguments and returns an int32_t boolean.
    unsafe { cn_home_is_unset() != 0 }
}
