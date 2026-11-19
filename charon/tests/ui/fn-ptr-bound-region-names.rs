//@ revisions=poly,mono
//@ charon-args=--include=core::ops::function
//@[mono] charon-args=--monomorphize
fn id<'a>(x: &'a u8) -> &'a u8 {
    x
}

fn call<F: FnOnce(&u8) -> &u8>(f: F, x: &u8) -> &u8 {
    f(x)
}

fn main() {
    let f: for<'a> fn(&'a u8) -> &'a u8 = id;
    call(f, &0);
    let g: fn(&u8) -> &u8 = id;
    call(g, &0);
}
