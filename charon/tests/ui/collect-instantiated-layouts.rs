//@ charon-args=--print-layouts --collect-instantiated-layouts
#![feature(trivial_bounds)]

struct Wrap<T>(Option<T>);
struct Grow<T>(T, *const Grow<(T, T)>);
struct Ref<'a>(&'a u8);
struct Holder<'a>(Wrap<&'a u16>);
fn instances(_: Wrap<bool>, _: (u8, &u32), _: Grow<u8>, _: Ref<'_>, _: Holder<'_>) {}
fn generic<T>(_: Option<T>) {}
fn opaque() -> impl Copy {
    0u8
}
fn uses_opaque() {
    let _ = Some(opaque());
}

// rustc evaluates the constant before we see it, so `Option<&u64>` isn't recorded
fn const_block() {
    let _ = const { size_of::<Option<&u8>>() };
}

// here too, we won't reach `Option<&u8>`
fn doc_example() {
    fn foo<T>() -> usize {
        size_of::<Option<T>>()
    }
    foo::<&u8>();
}

// instantiated layouts are useful here!
fn check_equal<T>(size: usize) {
    assert!(size == const { size_of::<T>() })
}
fn do_check() {
    check_equal::<Option<&u64>>(const { size_of::<Option<&u64>>() })
}

// `S<u8>` depends on the clauses of `trivial_clause` (here its field is `u64`), so we don't record it.
trait Tr {
    type A;
}
impl Tr for u8 {
    type A = u8;
}
struct S<T: Tr>(T::A);
fn trivial_clause(_: S<u8>)
where
    u8: Tr<A = u64>,
{
}
