//@ known-failure
//@ charon-args=--consts values
#![feature(fn_traits, unboxed_closures)]

struct A(fn() -> u8);
static CLOSURE_STATELESS: &A = &A(|| 1);

struct B(fn(&(u8, u8)) -> (u8, u8));
static BUILTIN_IMPL: &B = &B(<(u8, u8) as Clone>::clone);

struct C(extern "rust-call" fn(&fn(u8) -> u8, (u8,)) -> u8);
static FN_PTR_CALL: &C = &C(<fn(u8) -> u8 as Fn<(u8,)>>::call);
