// Regression test for https://github.com/AeneasVerif/charon/issues/988.
pub fn call_fn_shared(a: &[u8], i: usize) -> u8 {
    let read = |i: usize| -> u8 { a[i] };
    read(i)
}
