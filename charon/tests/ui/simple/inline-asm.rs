//@ rustc-args=--target x86_64-unknown-linux-gnu
fn main() {
    unsafe {
        core::arch::asm!("nop");
    }
}

fn multiple_targets(mut x: u32) -> u32 {
    unsafe {
        core::arch::asm!(
            "jmp {}",
            label {
                x = 1;
            },
        );
    }
    x
}

static ASM_STATIC: u64 = 0;

fn asm_target() {}

fn operands_and_options(mut x: u64) -> u64 {
    let output: u64;
    unsafe {
        core::arch::asm!(
            "mov {output}, {input}",
            "/* {{literal}} {input:e} {constant} {function} {static_symbol} */",
            input = in(reg) x,
            output = lateout(reg) output,
            constant = const 7,
            function = sym asm_target,
            static_symbol = sym ASM_STATIC,
            options(nomem, nostack, preserves_flags),
        );
        core::arch::asm!("mov {0}, {0}", inout(reg) x, options(pure, nomem));
        core::arch::asm!("/* { */", out("rax") _, options(raw, att_syntax));
    }
    x + output
}

fn asm_noreturn() -> ! {
    unsafe { core::arch::asm!("ud2", options(noreturn)) }
}

fn label_noreturn() {
    unsafe {
        core::arch::asm!(
            "jmp {}",
            label {
                return;
            },
            options(noreturn),
        );
    }
}

#[unsafe(naked)]
extern "C" fn naked() {
    core::arch::naked_asm!("ret")
}
