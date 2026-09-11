//@ charon-args=--monomorphize --include=core::ops::function

fn foo(x: u32) -> u32 {
    x
}

fn bar(x: &u32) -> u32 {
    *x
}

fn main() {
    let f: &dyn Fn(u32) -> u32 = &(foo as fn(u32) -> u32);
    let _ = f(1);
    let g: &mut dyn FnMut(u32) -> u32 = &mut (foo as fn(u32) -> u32);
    let _ = g(2);
    // A by-value `dyn` receiver, through `Box`.
    let h: Box<dyn FnOnce(u32) -> u32> = Box::new(foo as fn(u32) -> u32);
    let _ = h(3);
    // A higher-ranked fn pointer.
    let h: &dyn for<'a> Fn(&'a u32) -> u32 = &(bar as fn(&u32) -> u32);
    let _ = h(&3);
}
