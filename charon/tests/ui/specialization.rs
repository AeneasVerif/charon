//@ revisions=poly,mono
//@[poly] known-failure
//@[mono] charon-args=--monomorphize
#![feature(min_specialization)]
trait Tr {
    fn inherited(&self) -> u8;
    fn overridden(&self) -> u8;
}
impl<T> Tr for T {
    default fn inherited(&self) -> u8 {
        0
    }
    default fn overridden(&self) -> u8 {
        1
    }
}
impl Tr for u8 {
    fn overridden(&self) -> u8 {
        *self
    }
}

fn main() {
    2u8.inherited();
    2u8.overridden();
    let _ = &3u8 as &dyn Tr;
}
