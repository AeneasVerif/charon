//@ charon-args=--mir elaborated --print-layouts --no-compute-layout-guarantees
//@ charon-args=--opaque=test_crate::mk::coroutine::resume
//@ no-default-options
#![feature(coroutines, coroutine_trait, stmt_expr_attributes)]
use std::ops::Coroutine;

fn mk(x: u8, y: u64) -> impl Coroutine<Yield = (), Return = ()> {
    #[coroutine]
    move || {
        // saved across all yields: goes in the prefix next to upvars/tag
        let a = 0u32;
        yield;
        {
            // only saved for this yield -- overlaps with `c`
            let b = 0u16;
            yield;
            drop(b);
        }
        // only saved for this yield -- overlaps with `b`
        let c = 0u64;
        yield;
        drop(x);
        drop(y);
        drop(a);
        drop(c);
    }
}
