//@ charon-args=--include=alloc::vec::*
//@ charon-args=--sysroot=default
fn vec(x: &mut Vec<u32>) {
    x.push(42)
}
