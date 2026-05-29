pub fn rust_id(x: u32) -> u32 {
    x
}

pub extern "C" fn c_id(x: u32) -> u32 {
    x
}

pub fn get_rust_fn() -> fn(u32) -> u32 {
    rust_id
}

pub fn get_c_fn() -> extern "C" fn(u32) -> u32 {
    c_id
}
