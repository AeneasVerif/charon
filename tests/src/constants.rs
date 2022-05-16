//! Tests with constants
#![allow(dead_code)]

pub struct Pair<T1, T2> {
    x: T1,
    y: T2,
}

const X0: u32 = 0;

const X1: u32 = u32::MAX;

const fn incr(n: u32) -> u32 {
    n + 1
}

const X2: u32 = incr(32);

const fn mk_pair0(x: u32, y: u32) -> (u32, u32) {
    (x, y)
}

const P0: (u32, u32) = mk_pair0(0, 1);

const fn mk_pair1(x: u32, y: u32) -> Pair<u32, u32> {
    Pair { x, y }
}

const P1: Pair<u32, u32> = mk_pair1(0, 1);
