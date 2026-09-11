//@ charon-args=--monomorphize --include=core::ops::function
#![feature(fn_traits, unboxed_closures)]

fn add_one(x: u32) -> u32 {
    x + 1
}

fn call_it<F: Fn(u32) -> u32>(f: F, x: u32) -> u32 {
    f(x)
}

fn main() {
    let f: fn(u32) -> u32 = add_one;
    let _ = call_it(f, 0);
    let _ = Fn::call(&f, (1,));
    let g: extern "rust-call" fn(&fn(u32) -> u32, (u32,)) -> u32 =
        <fn(u32) -> u32 as Fn<(u32,)>>::call;
    let _ = g(&f, (2,));
}
