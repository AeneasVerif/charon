//@ revisions=poly,mono
//@ charon-args=--include=core::ops::function
//@[mono] known-failure
//@[mono] charon-args=--monomorphize

pub fn captured_ref<'a>(x: &'a u8) -> impl Fn() -> &'a u8 {
    move || x
}

// The captured value can itself be a closure with extra lifetime parameters. Their arguments
// must refer to the enclosing closure's parameters.
pub fn captured_closure<'a>(x: &'a u8) -> impl Fn() -> &'a u8 {
    let inner = move || x;
    move || inner()
}

fn generic_closure<T: Copy>(x: T) -> impl Fn() -> T {
    move || x
}

// The lifetime in `T = &'a u8` is supplied through the type argument, not an extra parameter
// of the polymorphic closure definition.
pub fn captured_generic_closure<'a>(x: &'a u8) -> impl Fn() -> &'a u8 {
    let inner = generic_closure(x);
    move || inner()
}

// Lifetimes bound inside an upvar type must remain bound there.
pub fn captured_fn_ptr(f: for<'a> fn(&'a u8) -> &'a u8) -> impl for<'a> Fn(&'a u8) -> &'a u8 {
    move |x| f(x)
}

pub fn captured_fn_ptr_with_free_region<'a>(
    f: for<'b> fn(&'b u8) -> &'a u8,
) -> impl Fn(&u8) -> &'a u8 {
    move |x| f(x)
}

trait WithItem {
    type Item: Copy;
}

impl WithItem for () {
    type Item = u8;
}

fn generic_assoc_closure<'a, T: WithItem>(x: &'a T::Item) -> impl Fn() -> &'a T::Item {
    move || x
}

// Substitution can normalize a captured associated type before the closure is matched.
pub fn captured_assoc_closure<'a>(x: &'a u8) -> impl Fn() -> &'a u8 {
    let inner = generic_assoc_closure::<()>(x);
    move || inner()
}
