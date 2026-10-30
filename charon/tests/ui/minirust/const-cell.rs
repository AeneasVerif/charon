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

    let cells = [FOO; 3];
    cells[0].set(7);
    minirust_print(cells[0].get());
    minirust_print(cells[1].get());

    let cells = [const { Cell::new(5) }; 2];
    cells[0].set(9);
    minirust_print(cells[0].get());
    minirust_print(cells[1].get());

    let [cell] = [Cell::new(11); 1];
    minirust_print(cell.get());
}
