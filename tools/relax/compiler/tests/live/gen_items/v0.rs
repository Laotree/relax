// Items the parser generates are named by their source position (`__relax_len_<pos>_<n>`: a
// hidden const for an array length expression). An edit ABOVE such an item moves it: it is the
// same item (paired by identity, renamed), not a removal plus an addition.
const TABLE: [u8; 3] = [1, 2, 3];

fn first(x: u64) -> u64 {
    x + 1
}

fn sized() -> usize {
    let buf = [0u8; TABLE.len() + 2];
    buf.len()
}

#[test]
fn run() {
    println!("out {} {}", first(1), sized());
}
