//! Exercise the translation of arrays
#![allow(dead_code)]

fn sum2 (s: &[u32], s2: &[u32]) -> u32 {
    let mut sum = 0;
    assert!(s.len() == s2.len());
    let mut i = 0;
    while i < s.len() {
        sum += s[i] + s2[i];
        i += 1;
    }
    return sum
}

const SZ: usize = 32;

fn f2 () -> u32 {
    let a: [u32; 2 ] = [ 1, 2 ];
    let b = [ 0; SZ ];
    return sum2(&a, &b[16..18])
}

fn main() {
    print!("{}", f2());
}
