pub trait SerializableState {
    fn serialize(&self) -> Vec<u8>;
}
const fn extent(n: usize) -> usize {
    let mut length = 0;
    while length < n { length += 1; }
    length
}
macro_rules! arrays {
    ($($n:expr),*) => {$(
        impl SerializableState for [u8; extent($n)] {
            fn serialize(&self) -> Vec<u8> { self.to_vec() }
        }
    )*};
}
arrays!(1, 2, 3, 4);
