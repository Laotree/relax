// Sandboxed code takes 70000 distinct functions as values (a static table of them): each gets
// its own sandbox thunk, the table's written part grows as they reach it, and calls through any
// of them land on their own function. (The table used to be 65536 thunks, one per twin.)
use std::relax::Module;

const M: &str = r#"
fn tag<const N: u32>() -> u32 {
    N
}

macro_rules! t {
    ($a:literal $b:literal $c:literal $d:literal $e:literal) => {
        tag::<{ $a * 10000 + $b * 1000 + $c * 100 + $d * 10 + $e }> as fn() -> u32
    };
}
macro_rules! l1 {
    ($($p:literal)*) => { [t!($($p)* 0), t!($($p)* 1), t!($($p)* 2), t!($($p)* 3), t!($($p)* 4), t!($($p)* 5), t!($($p)* 6), t!($($p)* 7), t!($($p)* 8), t!($($p)* 9)] };
}
macro_rules! l2 {
    ($($p:literal)*) => { [l1!($($p)* 0), l1!($($p)* 1), l1!($($p)* 2), l1!($($p)* 3), l1!($($p)* 4), l1!($($p)* 5), l1!($($p)* 6), l1!($($p)* 7), l1!($($p)* 8), l1!($($p)* 9)] };
}
macro_rules! l3 {
    ($($p:literal)*) => { [l2!($($p)* 0), l2!($($p)* 1), l2!($($p)* 2), l2!($($p)* 3), l2!($($p)* 4), l2!($($p)* 5), l2!($($p)* 6), l2!($($p)* 7), l2!($($p)* 8), l2!($($p)* 9)] };
}
macro_rules! l4 {
    ($($p:literal)*) => { [l3!($($p)* 0), l3!($($p)* 1), l3!($($p)* 2), l3!($($p)* 3), l3!($($p)* 4), l3!($($p)* 5), l3!($($p)* 6), l3!($($p)* 7), l3!($($p)* 8), l3!($($p)* 9)] };
}

static FNS: [[[[[fn() -> u32; 10]; 10]; 10]; 10]; 7] = [l4!(0), l4!(1), l4!(2), l4!(3), l4!(4), l4!(5), l4!(6)];

/// The table's distinct function addresses.
pub fn distinct() -> u64 {
    let mut all = Vec::new();
    for a in FNS.iter() {
        for b in a.iter() {
            for c in b.iter() {
                for d in c.iter() {
                    for f in d.iter() {
                        all.push(*f as usize);
                    }
                }
            }
        }
    }
    all.sort();
    all.dedup();
    all.len() as u64
}

/// Calls entry `i` of the table.
pub fn call(i: u64) -> u64 {
    let i = i as usize;
    FNS[i / 10000][i / 1000 % 10][i / 100 % 10][i / 10 % 10][i % 10]() as u64
}
"#;

#[test]
fn many_fn_values() {
    let m = Module::load_source("fn_values", "fn_values.rs", M, &[]).unwrap();
    let distinct: fn() -> u64 = m.get("distinct").unwrap();
    let call: fn(u64) -> u64 = m.get("call").unwrap();
    println!("out distinct fn values: {}", distinct());
    println!("out calls land: {}", [0u64, 4095, 4096, 65535, 65536, 69999].iter().all(|&i| call(i) == i));
    m.unload();
}
