//@ revisions=poly,mono
//@ no-default-options
//@ charon-args=--mir=promoted --raw-consts
//@[mono] charon-args=--monomorphize

// The promoted must inherit the closure late-bound region.
pub fn foo() -> impl for<'a> Fn(&'a u8) -> (&'a u8, &'a u8) {
    |x| (x, &42)
}

pub fn call(x: &u8) -> (&u8, &u8) {
    foo()(x)
}
