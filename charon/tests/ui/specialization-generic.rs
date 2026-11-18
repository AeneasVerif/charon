//@ revisions=poly,mono
//@[poly] known-failure
//@[mono] charon-args=--monomorphize
#![feature(min_specialization)]
struct Pair<X, Y>(X, Y);

trait Tr<A> {
    fn inherited(&self);
    fn overridden(&self);
}
impl<A, S> Tr<A> for S {
    default fn inherited(&self) {}
    default fn overridden(&self) {}
}
// Generics don't line up with the parent impl's; `'a` must be preserved in inherited items.
impl<'a, T> Tr<u32> for Pair<&'a T, bool> {
    fn overridden(&self) {}
}

fn main() {
    Tr::<u32>::inherited(&Pair(&0u8, true));
    Tr::<u32>::overridden(&Pair(&0u8, true));
}
