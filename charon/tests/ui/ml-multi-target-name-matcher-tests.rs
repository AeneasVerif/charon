//@ charon-args=--targets=x86_64-apple-darwin,aarch64-apple-darwin
#![register_tool(pattern)]
//! Tests for the ml name matcher with multi-target items. After multi-target merging,
//! target-specific items get a `PeTarget` path element appended to their name. The name
//! matcher should handle these correctly.

// Target-specific functions get a PeTarget path element after multi-target merging.
#[cfg(target_arch = "x86_64")]
#[pattern::pass("test_crate::x86_only::x86_64-apple-darwin")]
#[pattern::pass("test_crate::x86_only::_")]
#[pattern::fail("test_crate::x86_only")]
#[pattern::fail("test_crate::x86_only::aarch64-apple-darwin")]
fn x86_only() -> u64 {
    42
}

#[cfg(target_arch = "aarch64")]
#[pattern::pass("test_crate::arm_only::aarch64-apple-darwin")]
#[pattern::pass("test_crate::arm_only::_")]
#[pattern::fail("test_crate::arm_only")]
#[pattern::fail("test_crate::arm_only::x86_64-apple-darwin")]
fn arm_only() -> u64 {
    99
}

// Shared function: exists identically on all targets. After merging, it should be
// deduplicated and have no PeTarget suffix, so the pattern matches without a target.
#[pattern::pass("test_crate::shared_fn")]
fn shared_fn() -> u64 {
    0
}
