//@ revisions=poly,mono
//@ charon-args=--include=core::ops::function
//@[mono] charon-args=--monomorphize

pub fn captured_ref<'a>(x: &'a u8) -> impl Fn() -> &'a u8 {
    move || x
}

// The captured value can itself be a closure with extra lifetime parameters. Their arguments
// are currently erased when translating the captured closure type.
pub fn captured_closure<'a>(x: &'a u8) -> impl Fn() -> &'a u8 {
    let inner = move || x;
    move || inner()
}

// Lifetimes bound inside an upvar type must remain bound there.
pub fn captured_fn_ptr(
    f: for<'a> fn(&'a u8) -> &'a u8,
) -> impl for<'a> Fn(&'a u8) -> &'a u8 {
    move |x| f(x)
}
