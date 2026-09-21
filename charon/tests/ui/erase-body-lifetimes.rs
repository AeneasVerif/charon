//@ charon-args=--erase-body-lifetimes

struct A<'a, 'b> {
    x: &'a mut u32,
    y: &'b u32,
}

fn choose<'a, T>(b: bool, x: &'a mut T, y: &'a mut T) -> &'a mut T {
    if b { x } else { y }
}

fn test(x: &mut u32, y: &u32) -> u32 {
    let mut z = 0;
    let a = A { x, y };
    let r = choose(true, a.x, &mut z);
    *r += *a.y;
    *r
}
