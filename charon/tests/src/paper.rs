//! The examples from the ICFP submission, all in one place.
#![allow(dead_code)]

// 2.1
fn ref_incr(x: &mut i32) {
    *x = *x + 1;
}

fn test_incr() {
    let mut x = 0i32;
    ref_incr(&mut x);
    assert!(x == 1);
}

// 2.2
fn choose<'a, T>(b: bool, x: &'a mut T, y: &'a mut T) -> &'a mut T {
    if b {
        return x;
    } else {
        return y;
    }
}

fn test_choose() {
    let mut x = 0;
    let mut y = 0;
    let z = choose(true, &mut x, &mut y);
    *z = *z + 1;
    assert!(*z == 1);
    assert!(x == 1);
    assert!(y == 0);
}
