//@ known-failure
//@ revisions=poly,mono
//@ charon-args=--mir elaborated
//@[mono] charon-args=--monomorphize
#![feature(coroutines, coroutine_trait, stmt_expr_attributes)]
use std::ops::Coroutine;
use std::pin::Pin;

fn wrap<T>(x: T) -> impl Coroutine<Yield = (), Return = T> {
    #[coroutine]
    move || {
        yield;
        x
    }
}

fn resume() {
    let mut c = wrap(());
    let _ = Pin::new(&mut c).resume(());
}
