//@ charon-args=--targets=i686-unknown-linux-gnu,x86_64-apple-darwin
pub fn f1() -> u64 {
    0
}

#[cfg(target_os = "linux")]
pub fn f2_per_target() -> u64 {
    1
}

#[cfg(not(target_os = "linux"))]
pub fn f2_per_target() -> u64 {
    2
}

fn foo() -> u64 {
    f1() + f2_per_target()
}
