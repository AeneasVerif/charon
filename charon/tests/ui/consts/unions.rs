//@charon-args=--monomorphize --consts=values
//
union U {
    a: u32,
    b: f64,
    c: u8,
    p: &'static u32,
}
static Z: u32 = 5;
static A: U = U { a: 1 };
static B: U = U { b: 1.0 };
static C: U = U { c: 1 };
static P1: U = U { p: &Z };
static P2: U = U { p: &1 };

// Same-ABI fields make the union a scalar immediate.
union Same {
    a: u32,
    b: u32,
}
static SAME: Same = Same { a: 7 };

fn main() {
    let _ = &A;
    let _ = &B;
    let _ = &C;
    let _ = &P1;
    let _ = &P2;
    let _ = &SAME;
}
