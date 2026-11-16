//@ no-default-options
//@ charon-args=--mir=promoted --raw-consts
pub fn foo<'a, T: 'a>(
    x: &'a T,
) -> impl Fn() -> (
    &'a T,
    &'static dyn for<'b> Fn(&'b u8) -> (&'b u8, Option<&'a T>),
) {
    move || (x, &(|y| (y, None)))
}
