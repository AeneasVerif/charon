//@ ignore
#![feature(linkage)]

#[unsafe(export_name = "dep_hook")]
pub fn renamed() -> u8 {
    7
}

#[unsafe(no_mangle)]
#[linkage = "weak"]
pub extern "C" fn weak_hook() -> u8 {
    8
}

#[unsafe(no_mangle)]
pub fn unused_hook() -> u8 {
    9
}
