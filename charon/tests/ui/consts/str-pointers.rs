//@ rustc-args=--target x86_64-unknown-linux-gnu
//@ charon-args=--consts=values
pub static STR: &str = "hello";
pub static STR_SUFFIX: &str = "hello".split_at(1).1;
pub static CSTR: &core::ffi::CStr = c"hi";
pub struct W<T: ?Sized>(pub u8, pub T);
pub static WS: W<[u8; 2]> = W(0, [1, 2]);
pub static W_SLICE: &W<[u8]> = &WS;
