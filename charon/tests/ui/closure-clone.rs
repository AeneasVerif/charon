//@ revisions=poly,mono
//@[mono] charon-args=--monomorphize

pub fn closure(x: u32) {
    let f = move || x;
    let mut g = f.clone();
    g.clone_from(&f);
}

pub fn closure_generic<T: Clone>(x: T) {
    let f = move || x.clone();
    let _ = f.clone();
}

pub fn tuple(x: &(u32, u8), y: &mut (u32, u8)) -> (u32, u8) {
    y.clone_from(x);
    x.clone()
}
