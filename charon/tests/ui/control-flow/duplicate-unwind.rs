//@ charon-args=--ullbc --print-ullbc
struct Guard;

impl Drop for Guard {
    fn drop(&mut self) {}
}

fn may_panic() {}

// Both calls share the same cleanup chain in MIR. Each must get its own copy,
// including the shared tail and the abort path for a panic during cleanup.
fn shared_cleanup() {
    let _first = Guard;
    let _second = Guard;
    may_panic();
    may_panic();
}
