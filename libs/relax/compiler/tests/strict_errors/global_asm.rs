//~ msg: inline assembly (asm!, global_asm!, naked_asm!) is assembled only with `--allow-asm` (or MAKEPAD_RUN_ALLOW_ASM=1)
// Without --allow-asm global_asm! is rejected like asm!.
std::arch::global_asm!(".globl relax_test_sym", "relax_test_sym:", "ret");

fn main() {}
