/// Test with a static lifetime
fn test_static(x: &'static u32) -> &'static u32 {
    x
}

struct SStatic {
    x: &'static u32,
}

/// Types with complex regions hierarchy
enum E1<'a, 'b, T1, T2> {
    V1(&'a mut T1, &'b mut T2),
    /// Invert the type parameters, but not the region parameters
    V2(Box<E1<'a, 'b, T2, T1>>),
}

enum E2<'a, 'b, T1, T2> {
    V1(&'a mut T1, &'b mut T2),
    /// Invert the type parameters, but not the region parameters
    V2(Box<E2<'a, 'b, T2, T1>>),
    /// Invert the region parameters, but not the type parameters
    V3(Box<E2<'b, 'a, T2, T1>>),
}

enum E3<'a, 'b, 'c, T1, T2> {
    V1(&'a mut T1, &'b mut T2),
    /// Invert the type parameters, but not the region parameters
    V2(Box<E3<'a, 'b, 'c, T2, T1>>),
    /// Invert the region parameters, but not the type parameters
    V3(Box<E3<'b, 'a, 'c, T2, T1>>),
    V4(&'c &'a T1),
}

fn id<'a, T>(x: &'a mut T) -> &'a mut T {
    x
}

/// Checking projectors over symbolic values
pub fn test_borrows1() {
    let mut x = 3;
    let y = id(&mut x);
    let z = id(y);
    // We do not write a statement which would expand `z` on purpose:
    // we want to test that the handling of non-expanded symbolic values
    // is correct
    assert!(x == 3);
}

fn id_pair<'a, 'b, T>(x: &'a mut T, y: &'b mut T) -> (&'a mut T, &'b mut T) {
    (x, y)
}

/// Similar to the previous one
pub fn test_borrows2() {
    let mut x = 3;
    let mut y = 4;
    let z = id_pair(&mut x, &mut y);
    // We do not write a statement which would expand `z` on purpose:
    // we want to test that the handling of non-expanded symbolic values
    // is correct
    assert!(x == 3);
    assert!(y == 4);
}

/// input type: 'b must last longer than 'a
/// output type: 'a must last longer than 'b
/// So: 'a = 'b, and the function is legal.
pub fn nested_mut_borrows1<'a, 'b>(x: &'a mut &'b mut u32) -> &'b mut &'a mut u32 {
    x
}

pub fn nested_shared_borrows1<'a, 'b>(x: &'a &'b u32) -> &'a &'b u32 {
    x
}

pub fn nested_borrows1<'a, 'b>(x: &'a mut &'b u32) -> &'a mut &'b u32 {
    x
}

pub fn nested_borrows2<'a, 'b>(x: &'a &'b mut u32) -> &'a &'b mut u32 {
    x
}

fn nested_borrows1_test1() {
    let x = 0;
    let mut px = &x;
    let ppx = &mut px;
    let ppy = nested_borrows1(ppx);
    assert!(**ppy == 0);
    assert!(x == 0);
}

fn nested_borrows1_test2<'a, 'b>(x: &'a mut &'b u32) -> &'a mut &'b u32 {
    nested_borrows1(x)
}

fn nested_borrows2_test1() {
    let mut x = 0;
    let px = &mut x;
    let ppx = &px;
    let ppy = nested_borrows2(ppx);
    assert!(**ppy == 0);
    assert!(x == 0);
}
