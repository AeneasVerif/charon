#![feature(pattern_type_macro)]
#![feature(pattern_types)]
#![allow(internal_features)]

pub type Positive = std::pat::pattern_type!(i32 is 1..);
const ONE: Positive = const { unsafe { std::mem::transmute(1) } };
