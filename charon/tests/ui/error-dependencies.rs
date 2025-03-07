//@ known-failure
//! This file tests the error messages that indicates why we attempt to translate a given
//! definition.
#![feature(ptr_metadata)]
#![feature(register_tool)]
#![register_tool(charon)]

pub fn main() {
    let _ = core::ptr::null::<u8>();
    let _ = opaque::other_error();
}

#[charon::opaque]
mod opaque {
    pub fn other_error() {
        let _ = custom_null::<u8>();
    }
    fn custom_null<T: core::ptr::Thin>() {}
}
