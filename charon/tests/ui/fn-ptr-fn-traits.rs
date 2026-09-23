//@ revisions=poly,mono
//@ charon-args=--include=core::ops::function
//@[mono] charon-args=--monomorphize
#![allow(private_interfaces)]

trait Trait {}

impl Trait for u32 {}

struct Adt<'a, T: Trait>(&'a T);

fn identity<'a>(x: Adt<'a, u32>) -> Adt<'a, u32> {
    x
}

fn call_once<'a, F>(f: F, x: Adt<'a, u32>) -> Adt<'a, u32>
where
    F: FnOnce(Adt<'a, u32>) -> Adt<'a, u32>,
{
    f(x)
}

fn generic_call_once<F, A, B>(f: F, x: A) -> B
where
    F: FnOnce(A) -> B,
{
    f(x)
}

fn generic_call_once2<F, A, B, C>(f: F, x: A, y: B) -> C
where
    F: FnOnce(A, B) -> C,
{
    f(x, y)
}

pub fn test<'a>(x: &'a u32) -> &'a u32 {
    let f: for<'b> fn(Adt<'b, u32>) -> Adt<'b, u32> = identity;
    call_once(f, Adt(x)).0
}

struct ConstAdt<const N: usize>([u8; N]);

fn const_identity<const N: usize>(x: ConstAdt<N>) -> ConstAdt<N> {
    x
}

pub fn test_const(x: ConstAdt<3>) -> ConstAdt<3> {
    let f: fn(ConstAdt<3>) -> ConstAdt<3> = const_identity::<3>;
    generic_call_once(f, x)
}

fn ref_identity(x: &u32) -> &u32 {
    x
}

pub fn test_free_region<'a>(x: &'a u32) -> &'a u32 {
    let f: fn(&'a u32) -> &'a u32 = ref_identity;
    generic_call_once(f, x)
}

struct Plain<T>(T);

fn ignore_plain<'a>(_: Plain<u32>, x: &'a u32) -> &'a u32 {
    x
}

pub fn test_freshen_whole_adt<'a>(x: Plain<u32>, y: &'a u32) -> &'a u32 {
    let f: for<'b> fn(Plain<u32>, &'b u32) -> &'b u32 = ignore_plain;
    generic_call_once2(f, x, y)
}

fn array_identity<'a>(x: [&'a u8; 3]) -> [&'a u8; 3] {
    x
}

pub fn test_const_under_binder<'a>(x: [&'a u8; 3]) -> [&'a u8; 3] {
    let f: for<'b> fn([&'b u8; 3]) -> [&'b u8; 3] = array_identity;
    generic_call_once(f, x)
}

fn increment(x: u32) -> u32 {
    x + 1
}

pub fn test_dyn_fn(x: u32) -> u32 {
    let fn_ptr: fn(u32) -> u32 = increment;
    let dyn_fn: &dyn Fn(u32) -> u32 = &fn_ptr;
    dyn_fn(x)
}

trait Family {
    type Member<'a>;
}

trait Takes<T> {}

// The shape `for<'a> fn(A::Member<'a>) -> B` could naively require both `A: Family` and `A:
// MetaSized`.
// When translating the clause, `A` is instantiated with `T`, and to prove `T: MetaSized`, trait
// elaboration may choose `<T as Takes<for<'a> fn(T::Member<'a>)>>::ImpliedClause0`, which would
// create an `ItemRef` that contains itself.
// To avoid that we remove the redundant `A: MetaSized` clause but this would require a more
// principled solution.
// Taken from rustc's `vtable/impossible-method.rs` test.
trait RecursiveProof<T: Family> {
    fn method(&self)
    where
        T: Takes<for<'a> fn(T::Member<'a>)>;
}
