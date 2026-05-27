//@ charon-args=--targets=x86_64-unknown-linux-gnu,i686-unknown-linux-gnu
pub fn mod_reduce(a: u32) -> u32 {
    assert!(a < 100);
    a.wrapping_add(1)
}
