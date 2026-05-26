//@ charon-args=--targets=x86_64-pc-windows-msvc,aarch64-apple-darwin,i686-unknown-linux-gnu
#[cfg(target_arch = "aarch64")]
fn aarch64_only() -> u32 {
    1
}

#[cfg(target_arch = "x86_64")]
fn x86_64_only() -> u32 {
    2
}
