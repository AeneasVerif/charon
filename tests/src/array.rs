//! Exercise the translation of arrays
#![allow(dead_code)]

// Nano-tests
// ----------

fn take_array(_: [u32; 2]) {}
fn take_array_borrow(_: &[u32; 2]) {}
fn take_slice(_: &[u32]) {}
fn take_mut_slice(_: &mut [u32]) {}

fn take_all() {
    let mut x: [u32; 2] = [0, 0];
    // x is deep copied (copy node appears in Charon, followed by a move)
    take_array(x);
    take_array(x);
    // x passed by address, there is a reborrow here
    take_array_borrow(&x);
    // automatic cast from array to slice (spanning entire array)
    take_slice(&x);
    // note that both appear as SliceNew expressions, meaning the SliceNew UnOp is overloaded for
    // mut and non-mut cases
    take_mut_slice(&mut x);
}

fn index_array(x: [u32; 2]) -> u32 { x[0] }
fn index_array_borrow(x: &[u32; 2]) -> u32 { x[0] }
fn index_slice(x: &[u32]) -> u32 { x[0] }
fn index_mut_slice(x: &mut [u32]) -> u32 { x[0] }

fn index_all() -> u32 {
    let mut x: [u32; 2] = [0, 0];
    index_array(x) +
    index_array(x) +
    index_array_borrow(&x) +
    index_slice(&x) +
    index_mut_slice(&mut x)
}

fn update_array(mut x: [u32; 2]) { x[0] = 1 }
fn update_array_mut_borrow(x: &mut [u32; 2]) { x[0] = 1 }
fn update_mut_slice(x: &mut [u32]) { x[0] = 1 }

fn update_all() {
    let mut x: [u32; 2] = [0, 0];
    update_array(x);
    update_array(x);
    update_array_mut_borrow(&mut x);
    update_mut_slice(&mut x);
}

// Nano-tests, with ranges
// -----------------------

fn range_all() {
    let mut x: [u32; 4] = [ 0, 0, 0, 0 ];
    // CONFIRM: there is no way to shrink [T;N] into [T;M] with M<N?
    update_mut_slice(&mut x[1..3]);
}

// Non-copiable arrays
// -------------------

enum T { A, B }

fn take_array_t(_: [T; 2]) {
}

fn non_copyable_array() {
    let x: [T; 2] = [ T::A, T::B ];
    // x is moved (not deep copied!)
    // TODO: determine whether the translation needs to be aware of that and pass by ref instead of by copy
    take_array_t(x);

    // this fails, naturally:
    // take_array_t(x);
}

// Larger, random tests
// --------------------

fn sum2(s: &[u32], s2: &[u32]) -> u32 {
    let mut sum = 0;
    assert!(s.len() == s2.len());
    let mut i = 0;
    while i < s.len() {
        sum += s[i] + s2[i];
        i += 1;
    }
    sum
}

// TODO: this makes the compilation fail
// const SZ: usize = 32;

fn f4(x: &[u32; 32], y: usize, z: usize) -> (&[u32], u32) {
    (&x[y..z], x[0])
}

fn f2() -> u32 {
    let a: [u32; 2] = [1, 2];
    let b = [0; 32];
    let (b, _) = f4(&b, 16, 18);
    sum2(&a, b)
}

// To avoid lifetime shortening
fn ite() {
    let mut x: [u32; 2] = [0,0];
    if true {
        let mut y: [u32; 2] = [0,0];
        index_mut_slice(&mut x);
        index_mut_slice(&mut y);
    }
}
