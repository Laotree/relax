//~ E0277
// A u64 field collected into a Vec<usize> through `&&T` (`iter()` over a `Vec<&T>` gives the closure
// `&&T`): rustc rejects it, as no u64 -> usize FromIterator exists (Sandbox's game_cost.rs had it once
// its tick counts became u64; the closure's output is the field's type, whatever the reference depth).
struct Cost { instructions: u64 }
fn main() {
    let all = vec![Cost { instructions: 3 }, Cost { instructions: 1 }];
    let ticks: Vec<_> = all.iter().rev().take(2).collect();
    let instr: Vec<usize> = ticks.iter().map(|t| t.instructions).collect();
    println!("{}", instr.len());
}
