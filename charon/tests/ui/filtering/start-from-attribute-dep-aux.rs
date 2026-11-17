//@ ignore
#![feature(register_tool)]
#![register_tool(verify)]

pub fn dont_translate() {}

#[verify::start_from]
fn private_model() -> u64 {
    42
}

#[verify::start_from]
pub fn generic_model<T>(x: T) -> T {
    x
}
