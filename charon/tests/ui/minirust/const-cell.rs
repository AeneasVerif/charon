//@ output=run-with-minirust

use std::cell::Cell;

unsafe extern "Rust" {
    safe fn minirust_print(value: u32);
}

const FOO: Cell<u32> = Cell::new(42);

fn main() {
    let first = &FOO;
    let second = &FOO;
    first.set(13);
    minirust_print(first.get());
    minirust_print(second.get());
}
