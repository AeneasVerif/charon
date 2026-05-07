//! Minimal test for multi-target extraction.
//! Run with: charon rustc --targets x86_64-apple-darwin,aarch64-apple-darwin -- multi_target_mwe.rs
#![allow(unused)]

#[cfg(target_arch = "x86_64")]
fn platform_add(a: u32, b: u32) -> u32 {
    a.wrapping_add(b)
}

#[cfg(target_arch = "aarch64")]
fn platform_add(a: u32, b: u32) -> u32 {
    a.wrapping_add(b).wrapping_add(1)
}

fn call_platform(a: u32, b: u32) -> u32 {
    platform_add(a, b)
}
