// Regression test for https://github.com/AeneasVerif/charon/issues/1040.
pub fn foo(s: &u8) {
    let _ = || &*s;
}
