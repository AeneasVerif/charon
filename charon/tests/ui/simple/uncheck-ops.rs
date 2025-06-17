//@ charon-args=--mir elaborated
#![feature(core_intrinsics)]
fn main() {
    let _ = unsafe { std::intrinsics::unchecked_add(255, 1) };
}
