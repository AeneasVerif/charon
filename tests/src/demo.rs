#![allow(clippy::needless_lifetimes)]

/* Simple functions */

pub fn choose<'a, T>(b: bool, x: &'a mut T, y: &'a mut T) -> &'a mut T {
    if b {
        x
    } else {
        y
    }
}

pub fn mul3_add1(x: u32) -> u32 {
    x + x + x + 1
}

pub fn use_mul3_add1(x: u32, y: u32) -> u32 {
    mul3_add1(x) + y
}

pub fn incr<'a>(x: &'a mut u32) {
    *x += 1;
}

pub fn use_incr() {
    let mut x = 0;
    incr(&mut x);
    incr(&mut x);
    incr(&mut x);
}

/* Recursion, loops */

pub enum CList<T> {
    CCons(T, Box<CList<T>>),
    CNil,
}

pub fn list_nth<'a, T>(l: &'a CList<T>, i: u32) -> &'a T {
    match l {
        CList::CCons(x, tl) => {
            if i == 0 {
                x
            } else {
                list_nth(tl, i - 1)
            }
        }
        CList::CNil => {
            panic!()
        }
    }
}

pub fn list_nth1<'a, T>(mut l: &'a CList<T>, mut i: u32) -> &'a T {
    while let CList::CCons(x, tl) = l {
        if i == 0 {
            return x;
        }
        i -= 1;
        l = tl;
    }
    panic!();
}

/* Traits */

pub trait Counter {
    fn incr(&mut self) -> usize;
}

impl Counter for usize {
    fn incr(&mut self) -> usize {
        let x = *self;
        *self += 1;
        x
    }
}

pub fn use_counter<'a, T: Counter>(cnt: &'a mut T) -> usize {
    let _ = cnt.incr();
    cnt.incr()
}

use std::ops::Index;

pub fn use_vec_index(i: usize, v: &Vec<u32>) -> u32 {
    *(v.index(i))
}
