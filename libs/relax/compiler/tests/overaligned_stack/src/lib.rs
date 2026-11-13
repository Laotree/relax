#![cfg(test)]

#[repr(C, align(64))]
struct Aligned([u64; 8]);

#[repr(C, align(256))]
struct Wide([u64; 32]);

#[inline(never)]
fn check_local(seed: u64) {
    let mut value = Aligned([seed; 8]);
    let pointer = std::hint::black_box(&mut value) as *mut Aligned;
    assert_eq!(pointer as usize % 64, 0, "64-byte local alignment");
    assert_eq!(value.0[7], seed);
}

#[test]
fn local_alignment() {
    for seed in 0..32 {
        check_local(seed);
    }
}

#[test]
fn array_alignment() {
    let mut values = [Aligned([1; 8]), Aligned([2; 8]), Aligned([3; 8])];
    for value in std::hint::black_box(&mut values) {
        assert_eq!(value as *mut Aligned as usize % 64, 0, "64-byte array element alignment");
    }
}

#[test]
fn wider_local_alignment() {
    let mut value = Wide([7; 32]);
    assert_eq!(std::hint::black_box(&mut value) as *mut Wide as usize % 256, 0, "256-byte local alignment");
    assert_eq!(value.0[31], 7);
}

#[test]
fn heap_alignment() {
    let mut value = Box::new(Aligned([9; 8]));
    assert_eq!(std::hint::black_box(&mut *value) as *mut Aligned as usize % 64, 0, "64-byte heap alignment");
    assert_eq!(value.0[7], 9);
}

#[inline(never)]
fn make_aligned(seed: u64) -> Aligned {
    Aligned([std::hint::black_box(seed); 8])
}

#[inline(never)]
fn read_aligned(mut value: Aligned) -> u64 {
    assert_eq!(std::hint::black_box(&mut value) as *mut Aligned as usize % 64, 0);
    value.0[7]
}

#[test]
fn returned_values_and_arguments() {
    for seed in 0..8 {
        assert_eq!(read_aligned(make_aligned(seed)), seed);
    }
}

#[test]
fn simultaneous_storage() {
    let mut a = Aligned([11; 8]);
    let mut b = Wide([22; 32]);
    let a = std::hint::black_box(&mut a);
    let b = std::hint::black_box(&mut b);
    assert_eq!(a as *mut Aligned as usize % 64, 0);
    assert_eq!(b as *mut Wide as usize % 256, 0);
    a.0[7] = 33;
    b.0[31] = 44;
    assert_eq!(a.0, [11, 11, 11, 11, 11, 11, 11, 33]);
    assert_eq!(b.0[0], 22);
    assert_eq!(b.0[31], 44);
}

#[test]
fn zero_sized_alignment() {
    #[repr(align(256))]
    struct Empty;
    let mut value = Empty;
    assert_eq!(std::hint::black_box(&mut value) as *mut Empty as usize % 256, 0);
}
