//@ charon-args=--include=core::ffi::c_str::CStr
fn main() {
    let _ = c"123";
}
