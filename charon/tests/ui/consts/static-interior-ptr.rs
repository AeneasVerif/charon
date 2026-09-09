//@charon-args=--consts=values
// Pointers into the middle of a static.
static ARR: [u32; 3] = [1, 2, 3];
static FIRST: &u32 = &ARR[0];
static SECOND: &u32 = &ARR[1];

struct S {
    a: u32,
    b: u32,
}
static S0: S = S { a: 1, b: 2 };
static B: &u32 = &S0.b;

fn main() {
    let _ = (FIRST, SECOND, B);
}
