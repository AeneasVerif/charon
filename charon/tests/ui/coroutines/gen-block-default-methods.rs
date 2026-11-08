//@ known-failure
//@ revisions=poly,mono
//@ charon-args=--mir elaborated
//@[mono] charon-args=--monomorphize
//@ no-default-options
//@ rustc-args=--edition=2024
#![feature(gen_blocks)]

// The `Iterator` impl of a `gen` block provides the default methods of the trait.
fn count() -> usize {
    gen {
        yield 1u32;
        yield 2;
    }
    .count()
}
