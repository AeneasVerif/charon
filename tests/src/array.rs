//! Exercise the translation of arrays
#![allow(dead_code)]

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

fn f3(_: u32) -> () {

}

fn f4(x: &[u32; 32], y: usize, z: usize) -> &[u32] {
    &x[y..z]
}

fn f2() -> u32 {
    let a: [u32; 2] = [1, 2];
    f3(a[0]);
    let b = [0; 32];
    sum2(&a, f4(&b, 16, 18))
}
