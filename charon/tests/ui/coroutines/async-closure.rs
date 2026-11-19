//@ known-failure
//@ charon-args=--mir elaborated
use std::ops::AsyncFn;

fn mk() -> impl AsyncFn() {
    async || {}
}
