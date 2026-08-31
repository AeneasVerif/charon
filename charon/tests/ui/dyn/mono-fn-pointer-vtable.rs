//@ charon-args=--monomorphize --include=core::ops::function
//! Function *pointers* coerced to `dyn Fn`/`dyn FnMut`/`dyn FnOnce`. The builtin
//! `Fn*` impls of a `fn(..)` type have no impl items to take the vtable method
//! from, so the shim concretizes the receiver to the `fn(..)` type and calls
//! through it, untupling the arguments itself.
//!
//! `builtin-vtables.rs` covers the fn *item* and closure cases; `fn-pointer-vtable.rs` shows why
//! this needs `--monomorphize`.
fn foo(x: u32) -> u32 {
    x
}

fn main() {
    let f: &dyn Fn(u32) -> u32 = &(foo as fn(u32) -> u32);
    let _ = f(1);
    let g: &mut dyn FnMut(u32) -> u32 = &mut (foo as fn(u32) -> u32);
    let _ = g(2);
    // Built but not called: calling a by-value `dyn` receiver is a separate issue.
    let _h: Box<dyn FnOnce(u32) -> u32> = Box::new(foo as fn(u32) -> u32);
}
