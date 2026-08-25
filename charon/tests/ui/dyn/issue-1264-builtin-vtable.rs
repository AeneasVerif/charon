//@ charon-args=--monomorphize
//@ charon-args=--include=core::marker::Send
fn main() {
    let _x: &dyn Send = &0;
}
