//@ known-failure
//@ charon-args=--include=core::ops::function
//! Polymorphic counterpart of `mono-fn-pointer-vtable.rs`: function *pointers* coerced to
//! `dyn Fn`/`dyn FnMut`/`dyn FnOnce`.
//!
//! Unlike a closure or fn item, a `fn(..)` type has no item to hang its builtin `Fn*` impl off,
//! so we key the vtable method shim on the `Fn*` trait itself. In poly mode items are keyed by
//! `DefId` alone, so we only get one shim for the whole trait, with `Self` and `Args` still type
//! variables: we can neither see that the receiver is a function pointer nor untuple `Args` to
//! build the call. Supporting this would need the shim to be keyed on the trait ref rather than
//! the trait, so `--monomorphize` is required for now.
//!
//! `issue-1264-closure-vtable-poly.rs` covers the closure case, which works in poly mode because
//! the shim hangs off the closure, where both are concrete.
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
