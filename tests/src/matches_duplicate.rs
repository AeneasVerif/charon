//! This module tests the translation of matches.

pub fn id<T>(x: T) -> T {
    x
}

pub enum E2 {
    V1(u32),
    V2(u32),
    V3,
}

/// Testing matches where several branches are "fused".
/// The following leads to code-duplication (we must thus deactivate
/// code-duplication detection).
pub fn test2(x: E2) -> u32 {
    match x {
        E2::V1(n) | E2::V2(n) => n,
        E2::V3 => 0,
    }
}

/// Similar to test2
pub fn test3(x: E2) -> u32 {
    let y = match x {
        E2::V1(n) | E2::V2(n) => n,
        E2::V3 => 0,
    };
    let z = id(3);
    return y + z;
}
