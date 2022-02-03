//! This module doesn't contain function using nested borrows in their signatures,
//! and doesn't contain functions with loops.
//! It is slightly trimmed in comparison with [no_nested_borrows]

pub struct Pair<T1, T2> {
    x: T1,
    y: T2,
}

pub enum List<T> {
    Cons(T, Box<List<T>>),
    Nil,
}

fn get_elem<'a, T>(b: bool, x: &'a mut T, y: &'a mut T) -> &'a mut T {
    if b {
        return x;
    } else {
        return y;
    }
}

pub fn list_length<'a, T>(l: &'a List<T>) -> u32 {
    match l {
        List::Nil => {
            return 0;
        }
        List::Cons(_, l1) => {
            return 1 + list_length(l1);
        }
    }
}

pub fn list_nth<'a, T>(l: &'a mut List<T>, i: u32) -> &'a mut T {
    // (i)
    match l {
        List::Nil => {
            panic!()
        }
        List::Cons(x, tl) => {
            // (ii)
            if i == 0 {
                return x; // (iii)
            } else {
                // (iv)
                return list_nth(tl, i - 1);
            }
        }
    }
}
