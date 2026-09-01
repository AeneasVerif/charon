//@ charon-args=--include=core::ops::function

fn foo(x: u32) -> u32 {
    x
}

fn wrap<F: Fn(u32) -> u32 + 'static>(f: F) -> Box<dyn Fn(u32) -> u32> {
    Box::new(f)
}

fn main() {
    // These coercions translate the vtable instances for `fn(u32) -> u32: Fn*<(u32,)>`.
    let f: &dyn Fn(u32) -> u32 = &(foo as fn(u32) -> u32);
    let _ = f(1);
    let g: &mut dyn FnMut(u32) -> u32 = &mut (foo as fn(u32) -> u32);
    let _ = g(2);
    let _h: Box<dyn FnOnce(u32) -> u32> = Box::new(foo as fn(u32) -> u32);
    // The same builtin impls appear as clause proofs in the call generics.
    let _ = wrap(foo as fn(u32) -> u32)(3);
}
