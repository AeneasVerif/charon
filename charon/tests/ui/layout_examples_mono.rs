//@ no-default-options
//@ charon-args=--print-layouts --monomorphize
//! Layouts of instantiated generic types with `--monomorphize`.
use std::num::NonZero;

struct GenericStruct<T> {
    a: usize,
    b: T,
}

// Rust reorders the fields depending on `T`.
struct Reordered<T> {
    x: u8,
    y: T,
    z: u8,
}

#[repr(C)]
struct PolyReprC<T> {
    hd: u8,
    tl: T,
}

// The niche depends on `T`.
enum GenericEnum<T> {
    None,
    Some(T),
}

union GenericUnion<T: Copy> {
    x: T,
    y: u8,
}

fn instances(
    _: GenericStruct<u8>,
    _: Reordered<u32>,
    _: PolyReprC<u32>,
    _: GenericEnum<NonZero<u32>>,
    _: GenericEnum<u32>,
    _: GenericEnum<!>,
    _: GenericUnion<u64>,
    _: (u8, u32),
) {
}
