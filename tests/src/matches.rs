//! This module tests the translation of matches.
#![allow(dead_code)]

enum E1 {
    V1,
    V2,
    V3,
}

/// Testing matches where several branches are "fused": the control-flow
/// reconstruction must detect this (note that the control-flow reconstruction
/// algorithm checks that code blocks don't get duplicated - this is not
/// important for soundness, but we enforce this for now to make sure the
/// reconstruction is of good quality).
fn test1(x: E1) -> bool {
    match x {
        E1::V1 | E1::V2 => true,
        E1::V3 => false,
    }
}
