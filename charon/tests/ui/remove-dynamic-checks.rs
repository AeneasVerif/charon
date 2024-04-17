//@ output=pretty-llbc

/// Testing unop simplification
/// In debug mode, rust introduces an assertion before the negation.
pub fn neg_test(x: i32) -> i32 {
    -x
}

/// Testing binop simplification
/// In debug mode, rust inserts an assertion after the addition
pub fn add_u32(x: u32, y: u32) -> u32 {
    x + y
}

pub fn incr(x: &mut u32) {
    *x += 1;
}

/// Testing binop simplification
/// In debug mode, rust inserts an assertion after the substraction
pub fn subs_u32(x: u32, y: u32) -> u32 {
    x - y
}

/// Testing binop simplification
/// In debug mode, rust inserts an assertion before the division
pub fn div_u32(x: u32, y: u32) -> u32 {
    x / y
}

/// Testing binop simplification
/// When using constants, rustc removes the unnecessary assertions (but
/// only at a specific pass)
pub fn div_u32_const(x: u32) -> u32 {
    x / 2
}

/// Testing binop simplification
pub fn rem_u32(x: u32, y: u32) -> u32 {
    x % y
}

pub fn mul_u32(x: u32, y: u32) -> u32 {
    x * y
}

/// The assertions introduced by rust are not the same for the signed integers
/// and the unsigned integers. For instance, `i32::min / (-1)` can overflow.
pub fn add_i32(x: i32, y: i32) -> i32 {
    x + y
}

pub fn subs_i32(x: i32, y: i32) -> i32 {
    x - y
}

pub fn div_i32(x: i32, y: i32) -> i32 {
    x / y
}

pub fn div_i32_const(x: i32) -> i32 {
    x / 2
}

pub fn rem_i32(x: i32, y: i32) -> i32 {
    x % y
}

pub fn mul_i32(x: i32, y: i32) -> i32 {
    x * y
}

pub fn mix_arith_u32(x: u32, y: u32, z: u32) -> u32 {
    ((x + y) * (x / y) + (x - (z % y))) % (x + y + z)
}

pub fn mix_arith_i32(x: i32, y: i32, z: i32) -> i32 {
    ((x + y) * (x / y) + (x - (z % y))) % (x + y + z)
}

fn shl(x: u32, y: u32) -> u32 {
    x << y
}

fn shr(x: u32, y: u32) -> u32 {
    x >> y
}

/* Checking the simplification of binop operations *inside* global constants.

   In release mode, the Rust compiler inserts additional checks inside constant
   bodies.
*/
pub const CONST0: usize = 1 + 1;
pub const CONST1: usize = 2 * 2;

fn div_signed_with_constant() -> i32 {
    const FOO: i32 = 42;
    FOO / 2
}

// See issue #87
fn div_unsigned_to_slice(result: &mut [u32], x: u32) {
    result[0] = x / 3329;
}

fn div_signed_to_slice(result: &mut [i32], x: i32) {
    result[0] = x / 3329;
}
