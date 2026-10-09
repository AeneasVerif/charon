//@ charon-args=--monomorphize
//@ charon-args=--start-from=crate::main
//@ charon-args=--opaque=core::iter::*
//@ charon-args=--opaque=test_crate::apply_fn
//@ charon-args=--opaque=test_crate::apply_once
// The only calls to these closures are inside opaque callees. Keep their native
// Fn/FnMut/FnOnce method bodies, without extracting unused adapters.

fn callback(x: u32) -> u32 {
    x + 1
}

fn apply_fn(f: impl Fn(u32) -> u32) -> u32 {
    f(0)
}

fn apply_once(f: impl FnOnce(u32) -> u32) -> u32 {
    f(0)
}

struct Thing;

fn main() {
    let mut iter = (0..1).map(|x| callback(x));
    let _ = iter.next();

    let offset = 1;
    let _ = apply_fn(|x| callback(x + offset));

    let thing = Thing;
    let _ = apply_once(|x| {
        drop(thing);
        callback(x)
    });
}
