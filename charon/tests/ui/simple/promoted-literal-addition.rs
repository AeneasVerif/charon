//@ charon-args=--mir_optimized
fn two() -> &'static u32 {
    &(1 + 1)
}

fn main() {}
