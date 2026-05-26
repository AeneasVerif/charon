//@ charon-args=--targets=x86_64-unknown-linux-gnu,powerpc64-unknown-linux-gnu
//@ charon-args=--include=core::ffi::c_str::CStr
//! Multi-target because the definition of c_char is target-dependent.
fn main() {
    let _ = c"123";
}
