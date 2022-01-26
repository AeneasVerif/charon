pub struct Pair<T1, T2> {
    x: T1,
    y: T2,
}

pub enum List<T> {
    Cons(T, Box<List<T>>),
    Nil,
}

/// Sometimes, enumerations with one variant are not treated
/// the same way as the other variants (for example, downcasts
/// are not always introduced).
/// A downcast is the cast of an enum to a specific variant, like
/// in the left value of:
/// `((_0 as Right).0: T2) = move _1;`
pub enum One<T1> {
    One(T1),
}

/// Truely degenerate case
/// Instanciations of this are encoded as constant values by rust.
pub enum EmptyEnum {
    Empty,
}

/// Enumeration (several variants with no parameters)
/// Those are not encoded as constant values.
pub enum Enum {
    Variant1,
    Variant2,
}

/// Degenerate struct
/// Instanciations of this are encoded as constant values by rust.
pub struct EmptyStruct {}

pub enum Sum<T1, T2> {
    Left(T1),
    Right(T2),
}

/// Testing binop simplification
fn add_test(x: u32, y: u32) -> u32 {
    x + y
}

/// Testing binop simplification
fn subs_test(x: u32, y: u32) -> u32 {
    x - y
}

/// Testing binop simplification
fn div_test(x: u32, y: u32) -> u32 {
    x / y
}

/// Testing binop simplification
fn rem_test(x: u32, y: u32) -> u32 {
    x % y
}

fn test2() {
    let x: u32 = 23;
    let y: u32 = 44;
    let z = x + y;
    let p: Pair<u32, u32> = Pair { x: x, y: z };
    let s: Sum<u32, bool> = Sum::Right(true);
    let o: One<u64> = One::One(3);
    let e0 = EmptyEnum::Empty;
    let e1 = e0;
    let enum0 = Enum::Variant1;
}

fn get_max(x: u32, y: u32) -> u32 {
    if x >= y {
        x
    } else {
        y
    }
}

fn test3() {
    let x = get_max(4, 3);
    let y = get_max(10, 11);
    let z = x + y;
    assert!(z == 15);
}

/// Testing what happens with negation - in particular for overflows.
/// In debug mode, rust introduces an assertion before the negation.
fn test_neg(x: i32) -> i32 {
    -x
}

fn test_neg1() {
    let x: i32 = 3;
    let y = -x;
    assert!(y == -3);
}

/// Testing nested references.
fn refs_test1() {
    let mut x = 0;
    let mut px = &mut x;
    let ppx = &mut px;
    **ppx = 1;
    // The interesting thing happening here is that the borrow of x is inside
    // the borrow of px: ending the borrow of x requires ending the borrow of
    // px first.
    assert!(x == 1);
}

fn refs_test2() {
    let mut x = 0;
    let mut y = 1;
    let mut px = &mut x;
    let py = &mut y;
    let ppx = &mut px;
    *ppx = py;
    **ppx = 2;
    assert!(*px == 2);
    assert!(x == 0);
    assert!(*py == 2);
    assert!(y == 2);
}

/// Box creation
fn test_list1() {
    let l: List<i32> = List::Cons(0, Box::new(List::Nil));
}

/// Box deref
fn test_box1() {
    use std::ops::Deref;
    use std::ops::DerefMut;
    let mut b: Box<i32> = Box::new(0);
    let x = b.deref_mut();
    *x = 1;
    let x = b.deref();
    assert!(*x == 1);
}

fn copy_int(x: i32) -> i32 {
    x
}

// Just testing that shared loans are correctly handled
fn test_copy_int() {
    let x = 0;
    let px = &x;
    let y = copy_int(x);
    assert!(*px == y);
}

fn is_cons<T>(l: &List<T>) -> bool {
    match l {
        List::Cons(_, _) => true,
        List::Nil => false,
    }
}

fn test_is_cons() {
    let l: List<i32> = List::Cons(0, Box::new(List::Nil));

    assert!(is_cons(&l));
}

fn split_list<T>(l: List<T>) -> (T, List<T>) {
    match l {
        List::Cons(hd, tl) => (hd, *tl),
        _ => panic!(),
    }
}

fn test_split_list() {
    let l: List<i32> = List::Cons(0, Box::new(List::Nil));

    let (hd, tl) = split_list(l);
    assert!(hd == 0);
}

fn get_elem<'a, T>(b: bool, x: &'a mut T, y: &'a mut T) -> &'a mut T {
    if b {
        return x;
    } else {
        return y;
    }
}

fn get_elem_test() {
    let mut x = 0;
    let mut y = 0;
    let z = get_elem(true, &mut x, &mut y);
    *z = *z + 1;
    assert!(*z == 1);
    // drop(z)
    assert!(x == 1);
    assert!(y == 0);
}

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

/// Test with a char literal - testing serialization
fn test_char() -> char {
    'a'
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
