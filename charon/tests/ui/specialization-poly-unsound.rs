//@ known-failure
#![feature(min_specialization)]
trait Tr {
    fn f(&self);
}
impl<T> Tr for T {
    default fn f(&self) {}
}
impl Tr for u8 {
    fn f(&self) {}
}

// Resolves to the blanket impl's `f`, which is wrong for `T = u8`.
fn generic<T>(x: &T) {
    x.f()
}
