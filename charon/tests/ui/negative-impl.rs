#![feature(negative_impls)]
struct S;
impl !Send for S {}
