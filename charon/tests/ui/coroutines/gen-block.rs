//@ known-failure
//@ charon-args=--mir elaborated
//@ no-default-options
//@ rustc-args=--edition=2024
#![feature(gen_blocks)]

fn gen_block() -> impl Iterator<Item = ()> {
    gen { yield () }
}
