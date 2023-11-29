//! This module contains functions with nested borrows in their signatures.

pub fn id_mut_mut<'a, 'b, T>(x: &'a mut &'b mut T) -> &'a mut &'b mut T {
    x
}

pub fn id_mut_pair<'a, T>(x: &'a mut (&'a mut T, u32)) -> &'a mut (&'a mut T, u32) {
    x
}

pub fn id_mut_pair_test1() {
    let mut x: u32 = 0;
    let px = &mut x;
    let mut p = (px, 1);
    let pp0 = &mut p;
    let pp1 = id_mut_pair(pp0);
    let mut y = 2;
    *pp1 = (&mut y, 3);
}

pub fn id_mut_mut_pair<'a, T>(
    x: &'a mut &'a mut (&'a mut T, u32),
) -> &'a mut &'a mut (&'a mut T, u32) {
    x
}

pub fn id_mut_mut_mut_same<'a, T>(x: &'a mut &'a mut &'a mut u32) -> &'a mut &'a mut &'a mut u32 {
    x
}

pub fn id_borrow1<'a, 'b, 'c>(_x: &'a mut &'b u32, _y: &'a &'a mut u32) {
    ()
}

/// For symbolic execution: testing what happens with several abstractions.
pub fn id_mut_mut_test1() {
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
pub fn id_mut_mut_test2() {
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
pub fn id_mut_mut_test3() {
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
pub fn id_mut_mut_test4() {
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
