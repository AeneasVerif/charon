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
