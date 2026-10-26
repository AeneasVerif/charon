//@ no-default-options
//@ charon-args=--mir=promoted --raw-consts
// The promoted constant inherits the closure's recovered lifetime parameters. Keep its
// declaration and reference visible so we can check that the arguments match those parameters.
pub fn foo<'a>(x: &'a u8) -> impl Fn() -> (&'a u8, &'static u8) {
    move || (x, &42)
}
