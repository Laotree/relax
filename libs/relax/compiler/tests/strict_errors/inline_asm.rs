//~ msg: inline assembly (asm!, global_asm!, naked_asm!) is assembled only with `--allow-asm` (or MAKEPAD_RUN_ALLOW_ASM=1)
// Without --allow-asm (user decision 2026-10-21) asm! is a compile error naming the flag.
fn read() -> u64 {
    let v: u64;
    unsafe { std::arch::asm!("mov {0}, #7", out(reg) v) };
    v
}

fn main() {
    println!("{}", read());
}
