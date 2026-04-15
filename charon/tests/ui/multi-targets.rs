//@ charon-args=--targets=i686-unknown-linux-gnu,x86_64-apple-darwin
pub struct StructTargetIndep {
    pub x: u64,
    pub y: u64,
}

fn make_pair_same() -> StructTargetIndep {
    StructTargetIndep { x: 1, y: 2 }
}

pub fn f1_same() -> u64 {
    0
}

fn f2_same() -> u64 {
    f1_same()
}

#[cfg(target_os = "linux")]
pub fn f3_different() -> u64 {
    1 + f2_same()
}

#[cfg(not(target_os = "linux"))]
pub fn f3_different() -> u64 {
    2
}

fn foo_same() -> u64 {
    f2_same() + f3_different()
}
