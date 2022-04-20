#![allow(dead_code)]

/// Simple test with a loop
fn test_loop1(max: u32) -> u32 {
    let mut i = 0;
    let mut s = 0;
    while i < max {
        s += i;
        i += 1;
    }

    s *= 2;
    return s;
}

/// Test with a loop and a break
fn test_loop2(max: u32) -> u32 {
    let mut i = 0;
    let mut s = 0;
    while i < max {
        if i == 17 {
            break;
        }
        s += i;
        i += 1;
    }

    return s;
}

/// Test with nested loops and continue to outer loops
fn test_loop3(max: u32) -> u32 {
    let mut i = 0;
    let mut j = 0;
    let mut s = 0;
    'outer: while i < max {
        while j < max {
            if i + j == 17 {
                continue;
            }
            s += i;
            j += 1;

            continue 'outer;
        }
        j = 0;
        s += i;
        i += 1;
    }

    return s;
}

/// Test with nested loops and breaks to outer loops.
/// This test is a bit of a mistake: the `break 'outer` doesn't really make
/// sense, but it initially lead to strange results after control-flow reconstruction
/// (with some code duplicata).
#[allow(unused_assignments)]
fn test_loop4(max: u32) -> u32 {
    let mut i = 1;
    let mut j = 0;
    let mut s = 0;
    'outer: while i < max {
        while j < max {
            if i + j == 17 {
                continue;
            }
            s += i;
            j += 1;

            break 'outer;
        }
        j = 0;
        s += i;
        i += 1;
    }

    return s;
}

/// Just checking we don't generate interleaved loops (with the inner loop
/// using a break or a continue to the outer loop).
fn test_loop5(max: u32) -> u32 {
    let mut i = 0;
    let mut j = 0;
    let mut s = 0;
    while i < max {
        while j < max {
            s += j;
            j += 1;
        }
        s += i;
        i += 1;
    }

    return s;
}

/// In this function, the loop has several exit candidates with a number of
/// occurrences > 1.
fn test_loop6(max: u32) -> u32 {
    let mut i = 0;
    let mut s = 0;
    while i < max {
        if i > 3 {
            break;
        }
        s += i;
        i += 1;
    }

    // All the below nodes are exit candidates (each of them is referenced twice)
    s += 1;
    return s;
}

/// In this function, the loop is inside an `if ... then ... else ...`, so
/// that the loop exit coincides with the `if ... then ... else ...` exit.
fn test_loop7(max: u32) -> u32 {
    let mut i = 0;
    let mut s = 0;
    if i < max {
        while i < max {
            if i > 3 {
                break;
            }
            s += i;
            i += 1;
        }
    } else {
        s = 2;
    }

    s += 1;
    return s;
}

fn test_loops() {
    let x = test_loop1(2);
    assert!(x == 2);
    let x = test_loop2(2);
    assert!(x == 1);
    let x = test_loop3(2);
    assert!(x == 3);
    let x = test_loop4(20);
    assert!(x == 1);
    let x = test_loop5(2);
    assert!(x == 2);
    let x = test_loop6(2);
    assert!(x == 2);
}

pub enum List<T> {
    Cons(T, Box<List<T>>),
    Nil,
}

/// Same as [list_nth_mut] but with a loop
///
/// TODO: move to `no_nested_borrows` once we implement translation for loops.
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
