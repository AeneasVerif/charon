#![allow(unconditional_panic)]

fn main() {
    let f: fn() = || {
        let _ = 1 / 0;
    };
    f();
}
