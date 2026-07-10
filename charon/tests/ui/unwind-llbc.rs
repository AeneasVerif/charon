//@ no-default-options
#![allow(arithmetic_overflow)]

struct Foo;

impl Drop for Foo {
    fn drop(&mut self) {}
}

fn may_unwind() {}

fn main() {
    let f = Foo;
    may_unwind();
    let _ = 255u8 + 1;
    let _ = &f;
}
