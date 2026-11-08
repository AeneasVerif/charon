//@ known-failure
//@ charon-args=--mir elaborated
//@ no-default-options
//@ rustc-args=--edition=2024
#![feature(async_iterator, gen_blocks)]
use std::async_iter::AsyncIterator;

fn async_gen() -> impl AsyncIterator<Item = ()> {
    async gen { yield () }
}
