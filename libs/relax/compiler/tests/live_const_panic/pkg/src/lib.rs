const fn capacity(label: &str) -> usize {
    let bytes = label.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] == b's' { return i + 3; }
        i += 1;
    }
    panic!("missing size marker");
}
const N: usize = capacity("s");

pub fn value() -> usize { 1 }

#[test]
fn result() {
    let data: [u8; N] = [0; N];
    assert_eq!(data.len(), 3);
    assert_eq!(value(), 1);
}
