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

fn id_mut_mut<'a, 'b, T>(x: &'a mut &'b mut T) -> &'a mut &'b mut T {
    x
}

fn id_mut_pair<'a, T>(x: &'a mut (&'a mut T, u32)) -> &'a mut (&'a mut T, u32) {
    x
}

fn id_mut_pair_test1() {
    let mut x: u32 = 0;
    let px = &mut x;
    let mut p = (px, 1);
    let pp0 = &mut p;
    let pp1 = id_mut_pair(pp0);
    let mut y = 2;
    *pp1 = (&mut y, 3);
}

fn id_mut_mut_pair<'a, T>(x: &'a mut &'a mut (&'a mut T, u32)) -> &'a mut &'a mut (&'a mut T, u32) {
    x
}

fn id_mut_mut_mut_same<'a, T>(x: &'a mut &'a mut &'a mut u32) -> &'a mut &'a mut &'a mut u32 {
    x
}

fn id_borrow1<'a, 'b, 'c>(_x: &'a mut &'b u32, _y: &'a &'a mut u32) {
    ()
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

/// Test with a static lifetime - testing serialization
fn test_static(x: &'static u32) -> &'static u32 {
    x
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

/// For symbolic execution: testing what happens with several abstractions.
fn id_mut_mut_test1() {
    let mut x = 0;
    let mut px = &mut x;
    let ppx = &mut px;
    let ppy = id_mut_mut(ppx);
    **ppy = 1;
    // Ending one abstraction
    assert!(*px == 1);
    // Ending the other abstraction
    assert!(x == 1);
}

/*
/// For symbolic execution: testing what happens with several abstractions.
/// This case is a bit trickier, because we modify the borrow graph through
/// a value returned by a function call.
/// TODO: not supported! We overwrite a borrow in a returned value.
fn id_mut_mut_test2() {
    let mut x = 0;
    let mut px = &mut x;
    let ppx = &mut px;
    let ppy = id_mut_mut(ppx);
    **ppy = 1;
    // This time, we replace one of the borrows
    let mut y = 2;
    let py = &mut y;
    *ppy = py;
    // Ending one abstraction
    assert!(*px == 2);
    *px = 3;
    // Ending the other abstraction
    assert!(x == 1);
    assert!(y == 3);
}
*/

/*
/// For symbolic execution: testing what happens with several abstractions.
/// See what happens when chaining function calls.
/// TODO: not supported! We overwrite a borrow in a returned value.
fn id_mut_mut_test3() {
    let mut x = 0;
    let mut px = &mut x;
    let ppx = &mut px;
    let ppy = id_mut_mut(ppx); // &'a mut &'b mut i32
    **ppy = 1;
    let ppz = id_mut_mut(ppy); // &'c mut &'b mut i32
    **ppz = 2;
    // End 'a and 'c
    assert!(*px == 2);
    // End 'b (2 abstractions at once)
    assert!(x == 2);
}*/

/*
/// For symbolic execution: testing what happens with several abstractions.
/// See what happens when chaining function calls.
/// This one is slightly more complex than the previous one.
fn id_mut_mut_test4() {
    let mut x = 0;
    let mut px = &mut x;
    let ppx = &mut px;
    let ppy = id_mut_mut(ppx); // &'a mut &'b mut i32
    **ppy = 1;
    let ppz = id_mut_mut(ppy); // &'c mut &'b mut i32
    **ppz = 2;
    // End 'c
    assert!(**ppy == 2);
    // End 'a
    assert!(*px == 2);
    // End 'b (2 abstractions at once)
    assert!(x == 2);
}
*/

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

/*struct WrapShared<'a, T> {
    x: &'a T,
}

impl<'a, T> WrapShared<'a, T> {
    /*    fn new(x: &'a T) -> WrapShared<'a, T> {
        WrapShared { x }
    }*/

    fn new2<'b, T2>(x: &'a T, y: &'b T2) -> (WrapShared<'a, T>, WrapShared<'b, T2>) {
        (WrapShared { x }, WrapShared { x: y })
    }
}

// TODO: what happens if I call WrapShared::new2? Are there lifetime parameters
// present in the function call?

fn wrap_shared_new2_test1() {
    let x: u32 = 0;
    let y: u32 = 1;
    let (px, py) = WrapShared::new2(&x, &y);
}

fn wrap_shared_new2_test2<'a, T>(x: &'a T) -> (WrapShared<'a, T>, WrapShared<'a, T>) {
    // The region variables are erased below, and we only see the early bound ones
    let (px, py) = WrapShared::<'a, T>::new2(x, x);
    (px, py)
}*/

/*fn f4<'a, 'b>(
    ppx: &'a mut &'b mut u32,
    ppy: &'a mut &'b mut u32,
) -> (&'a mut &'b mut u32, &'a mut &'b mut u32) {
    (ppx, ppy)
}*/

/*enum Enum1 {
    Case0(i32),
    Case1(i32),
    Case2(i32),
}*/

/*
fn enum1_get(x: Enum1) -> i32 {
    match x {
        Enum1::Case0(x) => x,
        Enum1::Case1(x) => x,
        Enum1::Case2(x) => x,
    }
}

fn test_match2() {
    let x = Enum1::Case1(0);
    let y = enum1_get(x);
    assert!(y == 0);
}*/

// TODO: switch test
// TODO: panic!

// TODO: &'a mut (&'a mut u32, u32)
// TODO: make an example with a match, to see how the discriminant is handled
// TODO: test binops, unops, etc.
// TODO: loops
// TODO: vectors
// TODO: arrays and slices
// TODO: intensive tests for two-phase borrows (https://rustc-dev-guide.rust-lang.org/borrow_check/two_phase_borrows.html)
// TODO: impl taking a self parameter (self, &self, &mut self)
// TODO: play with types and functions taking anonymous types and regions as parameters.
// TODO: functions with no parameters (we should extract them to: () -> ...)
// Test this on: top-level type declarations and functions and also impls.

//fn main() {}
