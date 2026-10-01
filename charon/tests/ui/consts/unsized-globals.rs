//@ revisions=values,initializers
//@[values] charon-args=--consts=values
//@[initializers] charon-args=--consts=initializers

use std::fmt::Debug;

pub struct Wrap<T: ?Sized> {
    a: u8,
    b: T,
}
pub struct Outer<T: ?Sized> {
    x: u32,
    w: Wrap<T>,
}

pub const OUTER: &Outer<[u16]> = &Outer {
    x: 1,
    w: Wrap { a: 2, b: [3, 4] },
};

const WRAP: &Wrap<[u8]> = &Wrap { a: 5, b: [97, 98] };
pub const TUPLE: &(u8, [u8]) = unsafe { &*(WRAP as *const Wrap<[u8]> as *const (u8, [u8])) };
pub const STR_TAIL: &Wrap<str> = unsafe { &*(WRAP as *const Wrap<[u8]> as *const Wrap<str>) };
pub const NESTED: (u8, &Outer<[u16]>) = (7, OUTER);

pub static STATIC: &Outer<[u16]> = OUTER;
pub static INTERIOR: &Wrap<[u16]> = &STATIC.w;

pub trait Trait: Sync {}
impl Trait for u8 {}
pub struct RawPtr(*const dyn Trait);
unsafe impl Sync for RawPtr {}

pub static DYN: &dyn Trait = &8;
pub static FOO: &(dyn Debug + Sync) = &42;
pub static DYN_TAIL: &Wrap<dyn Trait> = &Wrap { a: 9, b: 10u8 };
pub static RAW_DYN: RawPtr = RawPtr(&11u8);

pub fn inline_const() {
    let _: &Outer<[u16]> = const {
        &Outer {
            x: 1,
            w: Wrap { a: 2, b: [3, 4] },
        }
    };
}
