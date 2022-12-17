#![allow(dead_code)]

/*
/// No borrows
fn sum(max: u32) -> u32 {
    let mut i = 0;
    let mut s = 0;
    while i < max {
        s += i;
        i += 1;
    }

    s *= 2;
    s
}
*/

pub enum List<T> {
    Cons(T, Box<List<T>>),
    Nil,
}

/// Same as [list_nth_mut] but with a loop
///
/// TODO: move to `loops` once we implement translation for loops.
pub fn list_nth_mut_loop<'a, T>(mut ls: &'a mut List<T>, mut i: u32) -> &'a mut T {
    loop {
        match ls {
            List::Nil => {
                panic!()
            }
            List::Cons(x, tl) => {
                if i == 0 {
                    return x;
                } else {
                    ls = tl;
                    i -= 1;
                }
            }
        }
    }
}
