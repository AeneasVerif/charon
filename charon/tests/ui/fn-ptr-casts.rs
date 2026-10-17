//@ charon-args=--consts=values

#![allow(dead_code)]
#![allow(late_bound_lifetime_arguments)]

fn identity<'a>(x: &'a u8) -> &'a u8 {
    x
}

static UNSAFE_IDENTITY: for<'a> unsafe fn(&'a u8) -> &'a u8 = identity;

fn widen_safety(f: fn()) -> unsafe fn() {
    f
}

fn with_early_and_late<'a, 'b>(x: &'a u8, y: &'b u8) -> &'b u8
where
    &'a u8: Sized,
{
    let _ = x;
    y
}

fn from_fn_def<'a>(x: &'a u8) -> &'a u8 {
    let f: for<'b> fn(&'b u8) -> &'b u8 = identity;
    let g: for<'b> unsafe fn(&'a u8, &'b u8) -> &'b u8 = with_early_and_late::<'a>;
    unsafe { g(x, f(x)) }
}

fn from_inline_const<'a>(x: &'a u8) -> &'a u8 {
    let f: for<'b> fn(&'b u8) -> &'b u8 = const { identity };
    f(x)
}

fn from_closure<'a>(x: &'a u8) -> &'a u8 {
    let f: for<'b> unsafe fn(&'a u8, &'b u8) -> &'b u8 = |_, y| y;
    unsafe { f(x, x) }
}

fn from_fn_ptr(f: for<'a, 'b> fn(&'a u8, &'b u8) -> &'a u8) {
    let _: for<'x, 'y> unsafe fn(&'y u8, &'x u8) -> &'y u8 = f;
}

fn nested_binder(f: for<'a> fn(for<'b> fn(&'a u8, &'b u8))) {
    let _: for<'x> unsafe fn(for<'y> fn(&'x u8, &'y u8)) = f;
}

fn nested_binder_swapped(f: for<'a, 'b> fn(for<'c> fn(&'a (), &'b (), &'c ()))) {
    let _: for<'x, 'y> unsafe fn(for<'z> fn(&'y (), &'x (), &'z ())) = f;
}

fn doubly_nested_binder(f: for<'a> fn(for<'b> fn(for<'c> fn(&'a (), &'b (), &'c ())))) {
    let _: for<'x> unsafe fn(for<'y> fn(for<'z> fn(&'x (), &'y (), &'z ()))) = f;
}
