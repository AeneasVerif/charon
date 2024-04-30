//! This tests the invocation of `charon` on a crate with external dependencies.
fn silly_incr(x: &mut u32) {
    take_mut::take(x, |y| y + 1);
}

fn main() {
    let mut x = 0;
    silly_incr(&mut x);
    assert_eq!(x, 1);
}
