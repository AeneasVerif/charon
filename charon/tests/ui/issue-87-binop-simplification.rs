//@ output=pretty-llbc
fn div_signed(x: i32, y: i32) -> i32 {
    x / y
}

fn div_signed_with_constant() -> i32 {
    const FOO: i32 = 42;
    FOO / 2
}

fn div_unsigned(x: u32, y: u32) -> u32 {
    x / y
}

fn div_unsigned_to_slice(result: &mut [u32], x: u32) {
    result[0] = x / 3329;
}

fn div_signed_to_slice(result: &mut [i32], x: i32) {
    result[0] = x / 3329;
}
