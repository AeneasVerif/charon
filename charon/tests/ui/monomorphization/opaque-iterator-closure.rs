//@ charon-args=--monomorphize
//@ charon-args=--start-from=crate::main
//@ charon-args=--opaque=core::iter::*
// The only call to this closure is inside the opaque iterator implementation.

fn callback(x: u32) -> u32 {
    x + 1
}

fn main() {
    let mut iter = (0..1).map(|x| callback(x));
    let _ = iter.next();
}
