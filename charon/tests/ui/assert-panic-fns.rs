//@ no-default-options
//@ charon-args=--ullbc --print-ullbc --mir optimized
#![allow(arithmetic_overflow, unconditional_panic)]

fn bounds_check(a: [u8; 3], i: usize) -> u8 {
    a[i]
}

fn add(x: i32, y: i32) -> i32 {
    x + y
}
fn sub(x: i32, y: i32) -> i32 {
    x - y
}
fn mul(x: i32, y: i32) -> i32 {
    x * y
}
// Also checks for division by zero and for overflow.
fn div(x: i32, y: i32) -> i32 {
    x / y
}
// Also checks for remainder by zero and for overflow.
fn rem(x: i32, y: i32) -> i32 {
    x % y
}
fn shl(x: i32, y: u32) -> i32 {
    x << y
}
fn shr(x: i32, y: u32) -> i32 {
    x >> y
}
fn neg(x: i32) -> i32 {
    -x
}

#[repr(u8)]
enum E {
    A = 1,
}
fn transmute(x: u8) -> E {
    unsafe { std::mem::transmute(x) }
}
