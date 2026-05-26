//@ charon-args=--targets=x86_64-pc-windows-msvc,aarch64-apple-darwin,i686-unknown-linux-gnu
#[cfg(any(target_arch = "x86_64", target_arch = "x86"))]
fn x86_common() -> u32 {
    42
}

#[cfg(target_arch = "x86_64")]
fn x86_different() -> u32 {
    64
}

#[cfg(target_arch = "x86")]
fn x86_different() -> u32 {
    32
}
