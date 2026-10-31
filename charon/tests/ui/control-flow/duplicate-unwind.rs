//@ charon-args=--ullbc --print-ullbc
struct Guard;

impl Drop for Guard {
    fn drop(&mut self) {}
}

fn may_panic() {}

// Both calls share the same cleanup chain in MIR. We duplicate the paths in LLBC (see https://github.com/AeneasVerif/charon/issues/1549).
fn shared_cleanup() {
    let _first = Guard;
    let _second = Guard;
    may_panic();
    may_panic();
}
