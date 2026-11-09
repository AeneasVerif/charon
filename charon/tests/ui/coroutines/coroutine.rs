//@ charon-args=--mir elaborated
#![feature(coroutines, coroutine_trait, stmt_expr_attributes)]
use std::ops::Coroutine;

fn movable(x: &u8, y: u8) -> impl Coroutine<u8, Yield = u8, Return = u8> + '_ {
    #[coroutine]
    move |a: u8| {
        let b = yield *x;
        yield a;
        yield y;
        b
    }
}

fn immovable() -> impl Coroutine<Yield = (), Return = ()> {
    #[coroutine]
    static || {
        let x = ();
        let r = &x;
        yield;
        *r
    }
}
