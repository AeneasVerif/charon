#![allow(dead_code)]
use std::collections::HashMap;

/// The example the Rust team uses to illustrate why we need Polonius.
pub fn get_or_insert(map: &mut HashMap<u32, u32>) -> &u32 {
    match map.get(&22) {
        Some(v) => v,
        None => {
            map.insert(22, 33);
            &map[&22]
        }
    }
}

pub enum List<T> {
    Cons(T, Box<List<T>>),
    Nil,
}

/// Return a mutable borrow to the first portion of the list where we can find [x].
/// Allow to do in-place modifications (this example comes from the b-epsilon tree).
pub fn get_list_at_x<'a>(ls: &'a mut List<u32>, x: u32) -> &'a mut List<u32> {
    match ls {
        List::Nil => {
            // We reached the end: just return it
            ls
        }
        List::Cons(hd, tl) => {
            if *hd == x {
                ls
            } else {
                get_list_at_x(tl, x)
            }
        }
    }
}

fn main() {}
