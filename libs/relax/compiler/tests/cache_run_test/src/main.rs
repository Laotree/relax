use array_codec::SerializableState;
fn main() {
    let s = [7u8; 3].serialize();
    println!("{:?}", &s[..]);
}

#[test]
fn three_bytes_serialize() {
    assert_eq!(&[7u8; 3].serialize()[..], &[7, 7, 7]);
}
