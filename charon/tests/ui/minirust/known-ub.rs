//@ output=run-with-minirust
//@ known-ub

fn read(pointer: *const u32) -> u32 {
    unsafe { *pointer }
}

fn main() {
    let _ = read(std::ptr::null::<u32>());
}
