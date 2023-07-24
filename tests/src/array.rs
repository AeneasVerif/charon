//! Exercise the translation of arrays
#![allow(dead_code)]

fn array_to_slice<T>(s: &[T; 32]) -> &[T] {
    s
}

fn array_to_mut_slice<T>(s: &mut [T; 32]) -> &mut [T] {
    s
}

fn index_array<T>(s: &[T; 32], i: usize) -> &T {
    &s[i]
}

fn index_mut_array<T>(s: &mut [T; 32], i: usize) -> &mut T {
    &mut s[i]
}

fn index_slice<T>(s: &[T], i: usize) -> &T {
    &s[i]
}

fn index_mut_slice<T>(s: &mut [T], i: usize) -> &mut T {
    &mut s[i]
}

fn slice_subslice(x: &[u32], y: usize, z: usize) -> &[u32] {
    &x[y..z]
}

fn slice_subslice_mut(x: &mut [u32], y: usize, z: usize) -> &mut [u32] {
    &mut x[y..z]
}

fn array_subslice(x: &[u32; 32], y: usize, z: usize) -> &[u32] {
    &x[y..z]
}

fn array_subslice_mut(x: &mut [u32; 32], y: usize, z: usize) -> &mut [u32] {
    &mut x[y..z]
}

fn sum(s: &[u32]) -> u32 {
    let mut sum = 0;
    let mut i = 0;
    while i < s.len() {
        sum += s[i];
        i += 1;
    }
    sum
}

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

fn f3(_: u32) {}

// TODO: this makes the compilation fail
//const SZ: usize = 32;

fn f4(x: &[u32; 32], y: usize, z: usize) -> &[u32] {
    &x[y..z]
}

fn f2() -> u32 {
    let a: [u32; 2] = [1, 2];
    f3(a[0]);
    let b = [0; 32];
    sum2(&a, f4(&b, 16, 18))
}
