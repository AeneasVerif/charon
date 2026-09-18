//@charon-args=--consts=values
// References to anonymous (promoted) allocations of various alignments.
struct S {
    a: u8,
    b: u64,
}

static U8: &u8 = &1;
static U16: &u16 = &2;
static U32: &u32 = &3;
static U64: &u64 = &4;
static U128: &u128 = &5;
static ARR: &[u32; 3] = &[1, 2, 3];
static SLICE: &[u32] = &[1, 2, 3];
static STRUCT: &S = &S { a: 1, b: 2 };
// A pointer into the middle of an anonymous allocation.
static INNER: &u64 = &STRUCT.b;

fn main() {
    let _ = U8;
    let _ = U16;
    let _ = U32;
    let _ = U64;
    let _ = U128;
    let _ = ARR;
    let _ = SLICE;
    let _ = STRUCT;
    let _ = INNER;
}
