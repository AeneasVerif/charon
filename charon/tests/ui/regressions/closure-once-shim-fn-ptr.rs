//@ revisions=values,bytes
//@[values] charon-args=--consts values
//@[bytes] charon-args=--consts bytes
// rustc represents both of these function pointers as pointers to the same `ClosureOnce` shim
// instance; only the type of the pointer tells them apart.
#![feature(fn_traits, unboxed_closures, type_alias_impl_trait)]

// A stateless closure coerced to a function pointer.
static AS_FN: fn() -> u8 = || 1;

// The `FnOnce::call_once` method of a stateless closure.
type Closure = impl Fn() -> u8;
#[define_opaque(Closure)]
fn mk_closure() -> Closure {
    || 2
}
static CALL_ONCE: extern "rust-call" fn(Closure, ()) -> u8 = <Closure as FnOnce<()>>::call_once;
