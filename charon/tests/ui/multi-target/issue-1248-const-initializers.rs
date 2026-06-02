//@ no-default-options
//@ charon-args=--targets=x86_64-unknown-linux-gnu,i686-unknown-linux-gnu
#[cfg(target_arch = "x86_64")]
const ARCH_TAG: u32 = 64;

#[cfg(target_arch = "x86")]
const ARCH_TAG: u32 = 32;
