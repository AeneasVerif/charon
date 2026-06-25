//@ charon-args=--sysroot default --monomorphize --mir elaborated
// Check that the reconstruct_fallible_operations pass correctly handles check_add usage
// that spans multiple basic blocks.
#![feature(core_intrinsics)]

fn other() {}
fn sink_tuple(_x: (usize, bool)) {}
fn sink_int(_x: usize) {}
fn sink_bool(_x: bool) {}

fn must_preserve_tuple() {
    let z = std::intrinsics::add_with_overflow(0usize, 0usize);
    other();
    sink_tuple(z);
}

fn can_erase_check() {
    let z = std::intrinsics::add_with_overflow(0usize, 0usize);
    other();
    sink_int(z.0);
}

fn must_preserve_overflow_flag() {
    let z = std::intrinsics::add_with_overflow(0usize, 0usize);
    other();
    sink_bool(z.1);
}

fn mixed_field0_and_cross_block_tuple() {
    let z = std::intrinsics::add_with_overflow(0usize, 0usize);
    sink_int(z.0);
    other();
    sink_tuple(z);
}

fn can_erase_check_multi_block() {
    let z = std::intrinsics::add_with_overflow(0usize, 0usize);
    other();
    sink_int(z.0);
    other();
    sink_int(z.0);
}
