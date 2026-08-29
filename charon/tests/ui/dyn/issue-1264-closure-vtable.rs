//@ charon-args=--monomorphize
//@ charon-args=--include=core::ops::function

fn main() {
    let f: &dyn Fn(u32) -> u32 = &|x| x + 1;
    let _y = f(1);
}
