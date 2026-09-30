//@ output=run-with-minirust
#![feature(core_intrinsics)]
#![allow(internal_features)]

use std::cell::Cell;

unsafe extern "Rust" {
    safe fn minirust_print(value: u32);
    unsafe fn minirust_start_unwind(payload: *mut u8) -> !;
}

#[derive(Clone, Copy)]
enum Choice {
    Left(u32),
    Right,
}

static VALUES: [u32; 2] = [20, 22];
static SELECTED: &Choice = &Choice::Left(7);

fn choose(choice: Choice) -> u32 {
    match choice {
        Choice::Left(value) => value + 1,
        Choice::Right => 0,
    }
}

fn boolean_ops(left: bool, right: bool) -> bool {
    (left & !right) | (left ^ right)
}

fn get(values: &[u32; 1], index: usize) -> u32 {
    values[index]
}

enum CellContainer {
    Variant1 {
        prefix: u8,
        cell: Cell<u32>,
        suffix: u8,
    },
    Variant2 {
        prefix: u16,
        cell: Cell<u16>,
    },
}

fn update_cell(value: &CellContainer) -> u32 {
    match value {
        CellContainer::Variant1 { cell, .. } => {
            cell.set(43);
            cell.get()
        }
        CellContainer::Variant2 { cell, .. } => {
            cell.set(43);
            cell.get() as u32
        }
    }
}

struct CatchData {
    payload: u32,
    caught: *mut u8,
}

unsafe fn throw(data: *mut CatchData) {
    let payload = unsafe { (&raw mut (*data).payload).cast() };
    unsafe { minirust_start_unwind(payload) };
}

unsafe fn catch(data: *mut CatchData, payload: *mut u8) {
    unsafe { (*data).caught = payload };
}

fn main() {
    minirust_print(choose(Choice::Left(41)));
    minirust_print(boolean_ops(true, false) as u32);
    minirust_print(get(&[42], 0));
    minirust_print(VALUES[0] + VALUES[1]);
    let cells = [
        CellContainer::Variant1 { prefix: 1, cell: Cell::new(7), suffix: 2 },
        CellContainer::Variant2 { prefix: 3, cell: Cell::new(8) },
    ];
    minirust_print(update_cell(&cells[0]));
    minirust_print(update_cell(&cells[1]));
    match SELECTED {
        Choice::Left(value) => minirust_print(*value),
        Choice::Right => minirust_print(0),
    }

    let mut data = CatchData { payload: 42, caught: std::ptr::null_mut() };
    let caught = unsafe { core::intrinsics::catch_unwind(throw, &raw mut data, catch) };
    minirust_print(if caught { 1 } else { 0 });
    minirust_print(unsafe { *data.caught.cast() });
}
