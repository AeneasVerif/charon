//@ no-default-options
//@ charon-args=--ullbc --print-ullbc --deallocate-all-locals
//! MIR omits the storage markers for some locals; by default we only add the missing
//! `StorageLive`s, but `--deallocate-all-locals` also adds a `StorageDead` for each of them before
//! every function exit.

fn sum(x: u32, y: u32) -> u32 {
    let z = x + y;
    z + 1
}

fn main() {
    let _ = sum(1, 2);
}
