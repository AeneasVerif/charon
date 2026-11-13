//@ charon-args=--hide-marker-traits
#![feature(trivial_bounds)]
#![allow(trivial_bounds)]

// Trivial bounds take precedence over impls during trait resolution, so the trait proofs
// of a parameter-free item reference can depend on its parent.

fn foo()
where
    String: Copy,
{
}

fn bar()
where
    String: Copy,
{
    foo()
}

fn baz<T>()
where
    String: Copy,
{
    foo()
}

fn main() {}
