//@ output=run-with-minirust
//@ known-panic

unsafe extern "Rust" {
    unsafe fn minirust_start_unwind(payload: *mut u8) -> !;
}

fn main() {
    unsafe { minirust_start_unwind(std::ptr::null_mut()) };
}
