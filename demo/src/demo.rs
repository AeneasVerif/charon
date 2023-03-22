pub fn choose<'a, T>(b: bool, x: &'a mut T, y: &'a mut T) -> &'a mut T {
    if b {
        return x;
    } else {
        return y;
    }
}

/*pub enum List<T> {
    Cons(T, Box<List<T>>),
    Nil,
}

pub fn list_nth_rec<'a, T>(l: &'a mut List<T>, i: u32) -> &'a mut T {
    match l {
        List::Nil => {
            panic!()
        }
        List::Cons(x, tl) => {
            if i == 0 {
                return x;
            } else {
                return list_nth_rec(tl, i - 1);
            }
        }
    }
}

pub fn list_nth<T>(mut ls: &mut List<T>, mut i: u32) -> &mut T {
    while let List::Cons(x, tl) = ls {
        if i == 0 {
            return x;
        } else {
            ls = tl;
            i -= 1;
        }
    }
    panic!()
}

pub fn test_swap() {
    let mut x = 0;
    let mut y = 1;
    std::mem::swap(&mut x, &mut y);
    assert!(x == 1);
    assert!(y == 0);
}*/

/*
mod opaque;
use crate::opaque::*;

pub fn f() -> S {
    let mut s = create(0);
    let x = get_field(&mut s);
    *x += 1;
    return s;
}
*/
