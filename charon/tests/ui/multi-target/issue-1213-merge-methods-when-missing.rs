//@ charon-args=--targets=x86_64-apple-darwin,aarch64-apple-darwin
#[cfg(target_arch = "x86_64")]
fn f(blocks: &mut [u8]) {
    for _ in blocks.iter_mut() {}
}

#[cfg(target_arch = "aarch64")]
fn g(s0: &[u8], s1: &[u8]) {
    for _ in s0.iter().zip(s1.iter()) {}
}
