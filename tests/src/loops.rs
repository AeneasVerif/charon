#![allow(dead_code)]

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

/// Same as [sum], but we use borrows in order tocreate loans inside a loop
/// iteration, and those borrows will have to be ended by the end of the
/// iteration.
fn sum_with_mut_borrows(max: u32) -> u32 {
    let mut i = 0;
    let mut s = 0;
    while i < max {
        let ms = &mut s;
        *ms += i;
        let mi = &mut i;
        *mi += 1;
    }

    s *= 2;
    s
}

/// Similar to [sum_with_mut_borrows].
fn sum_with_shared_borrows(max: u32) -> u32 {
    let mut i = 0;
    let mut s = 0;
    while i < max {
        i += 1;
        // We changed the order compared to [sum_with_mut_borrows]:
        // we want to have a shared borrow surviving until the end
        // of the iteration.
        let mi = &i;
        s += *mi;
    }

    s *= 2;
    s
}

pub enum List<T> {
    Cons(T, Box<List<T>>),
    Nil,
}

/// Same as [list_nth_mut] but with a loop
pub fn list_nth_mut_loop<T>(mut ls: &mut List<T>, mut i: u32) -> &mut T {
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

/// Same as [list_nth_mut_loop] but with shared borrows
pub fn list_nth_shared_loop<T>(mut ls: &List<T>, mut i: u32) -> &T {
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

/// Same as [list_nth_mut] but on a pair of lists.
///
/// This test checks that we manage to decompose a loop into disjoint regions.
pub fn list_nth_mut_loop_pair<'a, 'b, T>(
    mut ls0: &'a mut List<T>,
    mut ls1: &'b mut List<T>,
    mut i: u32,
) -> (&'a mut T, &'b mut T) {
    loop {
        match (ls0, ls1) {
            (List::Nil, _) | (_, List::Nil) => {
                panic!()
            }
            (List::Cons(x0, tl0), List::Cons(x1, tl1)) => {
                if i == 0 {
                    return (x0, x1);
                } else {
                    ls0 = tl0;
                    ls1 = tl1;
                    i -= 1;
                }
            }
        }
    }
}

/// Same as [list_nth_mut_loop_pair] but with shared borrows.
pub fn list_nth_shared_loop_pair<'a, 'b, T>(
    mut ls0: &'a List<T>,
    mut ls1: &'b List<T>,
    mut i: u32,
) -> (&'a T, &'b T) {
    loop {
        match (ls0, ls1) {
            (List::Nil, _) | (_, List::Nil) => {
                panic!()
            }
            (List::Cons(x0, tl0), List::Cons(x1, tl1)) => {
                if i == 0 {
                    return (x0, x1);
                } else {
                    ls0 = tl0;
                    ls1 = tl1;
                    i -= 1;
                }
            }
        }
    }
}

/// Same as [list_nth_mut_loop_pair] but this time we force the two loop
/// regions to be merged.
pub fn list_nth_mut_loop_pair_merge<'a, T>(
    mut ls0: &'a mut List<T>,
    mut ls1: &'a mut List<T>,
    mut i: u32,
) -> (&'a mut T, &'a mut T) {
    loop {
        match (ls0, ls1) {
            (List::Nil, _) | (_, List::Nil) => {
                panic!()
            }
            (List::Cons(x0, tl0), List::Cons(x1, tl1)) => {
                if i == 0 {
                    return (x0, x1);
                } else {
                    ls0 = tl0;
                    ls1 = tl1;
                    i -= 1;
                }
            }
        }
    }
}

/// Same as [list_nth_mut_loop_pair_merge] but with shared borrows.
pub fn list_nth_shared_loop_pair_merge<'a, T>(
    mut ls0: &'a List<T>,
    mut ls1: &'a List<T>,
    mut i: u32,
) -> (&'a T, &'a T) {
    loop {
        match (ls0, ls1) {
            (List::Nil, _) | (_, List::Nil) => {
                panic!()
            }
            (List::Cons(x0, tl0), List::Cons(x1, tl1)) => {
                if i == 0 {
                    return (x0, x1);
                } else {
                    ls0 = tl0;
                    ls1 = tl1;
                    i -= 1;
                }
            }
        }
    }
}

/// Mixing mutable and shared borrows.
pub fn list_nth_mut_shared_loop_pair<'a, 'b, T>(
    mut ls0: &'a mut List<T>,
    mut ls1: &'b List<T>,
    mut i: u32,
) -> (&'a mut T, &'b T) {
    loop {
        match (ls0, ls1) {
            (List::Nil, _) | (_, List::Nil) => {
                panic!()
            }
            (List::Cons(x0, tl0), List::Cons(x1, tl1)) => {
                if i == 0 {
                    return (x0, x1);
                } else {
                    ls0 = tl0;
                    ls1 = tl1;
                    i -= 1;
                }
            }
        }
    }
}

/// Same as [list_nth_mut_shared_loop_pair] but this time we force the two loop
/// regions to be merged.
pub fn list_nth_mut_shared_loop_pair_merge<'a, T>(
    mut ls0: &'a mut List<T>,
    mut ls1: &'a List<T>,
    mut i: u32,
) -> (&'a mut T, &'a T) {
    loop {
        match (ls0, ls1) {
            (List::Nil, _) | (_, List::Nil) => {
                panic!()
            }
            (List::Cons(x0, tl0), List::Cons(x1, tl1)) => {
                if i == 0 {
                    return (x0, x1);
                } else {
                    ls0 = tl0;
                    ls1 = tl1;
                    i -= 1;
                }
            }
        }
    }
}

/// Same as [list_nth_mut_shared_loop_pair], but we switched the positions of
/// the mutable and shared borrows.
pub fn list_nth_shared_mut_loop_pair<'a, 'b, T>(
    mut ls0: &'a List<T>,
    mut ls1: &'b mut List<T>,
    mut i: u32,
) -> (&'a T, &'b mut T) {
    loop {
        match (ls0, ls1) {
            (List::Nil, _) | (_, List::Nil) => {
                panic!()
            }
            (List::Cons(x0, tl0), List::Cons(x1, tl1)) => {
                if i == 0 {
                    return (x0, x1);
                } else {
                    ls0 = tl0;
                    ls1 = tl1;
                    i -= 1;
                }
            }
        }
    }
}

/// Same as [list_nth_mut_shared_loop_pair_merge], but we switch the positions of
/// the mutable and shared borrows.
pub fn list_nth_shared_mut_loop_pair_merge<'a, T>(
    mut ls0: &'a List<T>,
    mut ls1: &'a mut List<T>,
    mut i: u32,
) -> (&'a T, &'a mut T) {
    loop {
        match (ls0, ls1) {
            (List::Nil, _) | (_, List::Nil) => {
                panic!()
            }
            (List::Cons(x0, tl0), List::Cons(x1, tl1)) => {
                if i == 0 {
                    return (x0, x1);
                } else {
                    ls0 = tl0;
                    ls1 = tl1;
                    i -= 1;
                }
            }
        }
    }
}
