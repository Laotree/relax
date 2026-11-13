// Indexing a slice or str by `(Bound<usize>, Bound<usize>)` (SliceIndex since 1.53). The tuple
// is no builtin index: rustc selects `Index<I> for [T]` through its SliceIndex impl. Relax took
// it for an element index (E0277, then `&T` where `&[T]` was expected). indexmap's impl_index!
// lists `(Bound<usize>, Bound<usize>)` among its range types.
use std::ops::{Bound, Index, IndexMut};

pub struct Slice {
    entries: [u8],
}
impl Slice {
    fn from_slice(s: &[u8]) -> &Slice { unsafe { &*(s as *const [u8] as *const Slice) } }
    fn from_mut_slice(s: &mut [u8]) -> &mut Slice { unsafe { &mut *(s as *mut [u8] as *mut Slice) } }
}
macro_rules! impl_index {
    ($($range:ty),*) => {$(
        impl Index<$range> for Slice {
            type Output = Slice;
            fn index(&self, range: $range) -> &Self { Self::from_slice(&self.entries[range]) }
        }
        impl IndexMut<$range> for Slice {
            fn index_mut(&mut self, range: $range) -> &mut Self { Self::from_mut_slice(&mut self.entries[range]) }
        }
    )*}
}
impl_index!(std::ops::Range<usize>, (Bound<usize>, Bound<usize>));

#[test]
fn bound_pairs_index_slices_and_strs() {
    let mut v = [1u8, 2, 3, 4];
    let r = (Bound::Excluded(0), Bound::Included(2));
    assert_eq!(v[r], [2, 3]);
    v[(Bound::Unbounded, Bound::Excluded(1))][0] = 9;
    assert_eq!(v, [9, 2, 3, 4]);
    assert_eq!(&"hello"[(Bound::Included(1), Bound::Excluded(4))], "ell");
    let s = Slice::from_mut_slice(&mut v);
    assert_eq!(s[(Bound::Excluded(0), Bound::Unbounded)].entries, [2, 3, 4]);
    s[(Bound::Included(3), Bound::Unbounded)].entries[0] = 7;
    assert_eq!(s[0..4].entries, [9, 2, 3, 7]);
}
