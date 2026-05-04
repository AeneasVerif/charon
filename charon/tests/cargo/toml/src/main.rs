#![allow(unexpected_cfgs)]

// `[cfg(abc)]` is here to test that we correctly passed rustc flags from `[package.metadata.charon.rustc]`:
// without `--cfg abc`, `main` does not exist and the build fails.
// The call to `is_some` exercises the `extract_opaque_bodies` option.
#[cfg(abc)]
pub mod included {
    pub fn run() {
        let _ = Some(false).is_some();
    }
}

// Must NOT appear in the output: `start_from = ["crate::included"]` filters this out.
pub mod excluded {
    pub fn unreachable() -> u32 {
        42
    }
}

#[cfg(abc)]
fn main() {
    included::run();
}
