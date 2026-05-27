//@ charon-args=--targets=x86_64-unknown-linux-gnu,i686-unknown-linux-gnu
#[cfg_attr(target_arch = "x86_64", repr(align(16)))]
pub struct Inner {
    pub x: u32,
}
