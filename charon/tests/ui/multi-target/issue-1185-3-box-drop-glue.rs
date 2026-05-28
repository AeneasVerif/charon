//@ charon-args=--targets=x86_64-unknown-linux-gnu,i686-unknown-linux-gnu
//@ charon-args=--hide-marker-traits
pub fn mono() -> u32 {
    let _b = Box::new(0u32);
    0
}
