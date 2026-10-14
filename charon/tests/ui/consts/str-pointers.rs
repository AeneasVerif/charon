//@ revisions=values,unsized_strings
//@[values] charon-args=--consts=values
//@[unsized_strings] charon-args=--consts=values --unsized-strings
pub static STR: &str = "hello";
pub static STR_SUFFIX: &str = "hello".split_at(1).1;
pub static CSTR: &core::ffi::CStr = c"hi";
pub struct W<T: ?Sized>(pub u8, pub T);
pub static WS: W<[u8; 2]> = W(0, [1, 2]);
pub static W_SLICE: &W<[u8]> = &WS;
