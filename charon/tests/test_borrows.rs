/// Test with a static lifetime
fn test_static(x: &'static u32) -> &'static u32 {
    x
}

fn id<'a, T>(x: &'a mut T) -> &'a mut T {
    x
}

/// Checking projectors over symbolic values
pub fn test_borrows1() {
    let mut x = 3;
    let mut y = id(&mut x);
    let z = id(y);
    assert!(x == 3);
}

fn id_pair<'a, 'b, T>(x: &'a mut T, y: &'b mut T) -> (&'a mut T, &'b mut T) {
    x
}

/// Similar to the previous one
pub fn test_borrows2() {
    let mut x = 3;
    let mut y = 4;
    let mut z = id_pair(&mut x, &mut y);
    assert!(x == 3);
    assert!(y == 4);
}
