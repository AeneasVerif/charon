//! Exercise the translation of arrays
#![allow(dead_code)]

fn array_to_slice<T>(s: &[T; 32]) -> &[T] {
    s
}

fn array_to_mut_slice<T>(s: &mut [T; 32]) -> &mut [T] {
    s
}

fn array_len<T>(s: [T; 32]) -> usize {
    s.len()
}

fn shared_array_len<T>(s: &[T; 32]) -> usize {
    s.len()
}

fn shared_slice_len<T>(s: &[T]) -> usize {
    s.len()
}

fn index_array_shared<T>(s: &[T; 32], i: usize) -> &T {
    &s[i]
}

// Remark: can't move out of an array
// Also: can't move out of a slice.

fn index_array_u32(s: [u32; 32], i: usize) -> u32 {
    s[i]
}

fn index_array_generic<const N: usize>(s: [u32; N], i: usize) -> u32 {
    s[i]
}

fn index_array_generic_call<const N: usize>(s: [u32; N], i: usize) -> u32 {
    index_array_generic(s, i)
}

fn index_array_copy(x: &[u32; 32]) -> u32 {
    x[0]
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

fn array_to_slice_shared(x: &[u32; 32]) -> &[u32] {
    x
}

fn array_to_slice_mut(x: &mut [u32; 32]) -> &mut [u32] {
    x
}

fn array_subslice(x: &[u32; 32], y: usize, z: usize) -> &[u32] {
    &x[y..z]
}

fn array_subslice_mut(x: &mut [u32; 32], y: usize, z: usize) -> &mut [u32] {
    &mut x[y..z]
}

fn index_slice_0<T>(s: &[T]) -> &T {
    &s[0]
}

fn index_array_0<T>(s: &[T; 32]) -> &T {
    &s[0]
}

/*
// Unsupported by Aeneas
fn index_index_slice<'a, T>(s: &'a [&[T]], i: usize, j: usize) -> &'a T {
    &s[i][j]
}
*/

fn index_index_array(s: [[u32; 32]; 32], i: usize, j: usize) -> u32 {
    s[i][j]
}

/*
// Unsupported by Aeneas
fn update_update_slice(s: &mut [&mut [u32]], i: usize, j: usize) {
    s[i][j] = 0;
}
*/

fn update_update_array(mut s: [[u32; 32]; 32], i: usize, j: usize) {
    s[i][j] = 0;
}

fn array_local_deep_copy(x: &[u32; 32]) {
    let _y = *x;
}

fn f0() {
    let s: &mut [u32] = &mut [1, 2];
    s[0] = 1;
}

fn f1() {
    let mut s: [u32; 2] = [1, 2];
    s[0] = 1;
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

fn f2() -> u32 {
    let a: [u32; 2] = [1, 2];
    f3(a[0]);
    let b = [0; 32];
    sum2(&a, f4(&b, 16, 18))
}

fn f3(_: u32) {}

// TODO: this makes the compilation fail
//const SZ: usize = 32;

fn f4(x: &[u32; 32], y: usize, z: usize) -> &[u32] {
    &x[y..z]
}
