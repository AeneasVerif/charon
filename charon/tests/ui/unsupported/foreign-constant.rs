//@ known-failure
//@ aux-crate=foreign-constant-aux.rs
use foreign_constant_aux::CONSTANT;
const _: i32 = 1 << CONSTANT;
