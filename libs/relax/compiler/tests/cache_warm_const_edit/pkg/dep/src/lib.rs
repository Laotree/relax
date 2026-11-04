pub const DEP_VALUE: u64 = 1;
pub struct DepT;
pub trait DepKind {
    const DK: u64;
}
#[inline(never)]
pub fn read_dk<T: DepKind>() -> u64 {
    T::DK
}
