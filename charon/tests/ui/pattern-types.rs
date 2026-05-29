#![feature(pattern_type_macro)]
#![feature(pattern_types)]
#![allow(internal_features)]

pub type Positive = std::pat::pattern_type!(i32 is 1..);
pub type NonNullPtr = std::pat::pattern_type!(*const u8 is !null);

pub fn keep_positive(x: Positive) -> Positive {
    x
}

pub fn keep_non_null_ptr(x: NonNullPtr) -> NonNullPtr {
    x
}
