//! Exercise the translation of arrays, features not yet supported by Eurydice
#![allow(dead_code)]

fn index_array_generic<const N: usize>(s: [u32; N], i: usize) -> u32 {
    s[i]
}

fn index_array_generic_call<const N: usize>(s: [u32; N], i: usize) -> u32 {
    index_array_generic(s, i)
}

// Using const generics as values
fn const_gen_ret<const N: usize>() -> usize {
    N
}
