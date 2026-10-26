//@ charon-args=--include=core::ops::function

trait Provide<'a> {
    fn provide() -> &'a u8;
}

// The input and first output share a genuinely bound lifetime. The second output's lifetime
// is fixed by `T`: rustc erases it, so it becomes an extra parameter of the closure struct.
fn make<'a, T: Provide<'a>>() -> impl for<'b> Fn(&'b u8) -> (&'b u8, &'a u8) {
    |x| (x, T::provide())
}

// Exercise the virtual impls too: `FnOnce::Output` must agree with the call method signatures.
fn apply<'a, 'b, F>(f: F, x: &'b u8) -> (&'b u8, &'a u8)
where
    F: for<'c> Fn(&'c u8) -> (&'c u8, &'a u8),
{
    f(x)
}

fn call<'a, 'b, T: Provide<'a>>(x: &'b u8) -> (&'b u8, &'a u8) {
    apply(make::<T>(), x)
}
