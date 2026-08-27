//@ charon-args=--no-gen-tuple-structs

fn mk_unit() -> () {
    ()
}

fn mk_pair(x: u32, y: bool) -> (u32, bool) {
    (x, y)
}

fn fst(p: (u32, bool)) -> u32 {
    p.0
}

fn nested<T>(x: T, y: (u8, u8, u8)) -> (T, (u8, u8, u8)) {
    (x, y)
}

struct Struct {
    field: (u32, (bool, char)),
}

fn get_field(s: Struct) -> (bool, char) {
    s.field.1
}

trait Trait {
    type Assoc;
}

impl Trait for u32 {
    type Assoc = (u32, u32);
}

// Closures take their arguments as a tuple.
fn call_closure(f: impl Fn(u32, bool) -> u32) -> u32 {
    f(0, true)
}

fn use_closure(z: u32) -> u32 {
    call_closure(|x, y| if y { x } else { z })
}
