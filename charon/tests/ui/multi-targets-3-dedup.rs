//@ charon-args=--targets=x86_64-pc-windows-msvc,aarch64-apple-darwin,i686-pc-windows-msvc
#![allow(unused)]

fn clone_it(x: &u32) -> u32 {
    x.clone()
}

#[cfg(target_arch = "x86_64")]
fn platform_specific() -> u32 { 42 }

#[cfg(target_arch = "aarch64")]
fn platform_specific() -> u32 { 43 }

#[cfg(target_arch = "x86")]
fn platform_specific() -> u32 { 44 }

pub fn call_both(x: &u32) -> u32 {
    clone_it(x) + platform_specific()
}
