//! This module tests the translation of matches.
#![allow(dead_code)]

enum E1 {
    V1,
    V2,
    V3,
}

/// Testing matches where several branches are "fused".
/// We attempt to detect this when the option `--no-code-duplication` is activated,
/// so as not to fail because the same block of code is duplicated, but it can be tricky
/// because depending on the MIR pass we take as input, some intermediate blocks may be
/// in the control flow or not.
/// If we use the "Optimized MIR" pass, it is ok. If we use the "Promoted MIR",
/// then we have the following for the `E1::V1 | E1::V2 => ...` branch:
/// ```text
/// bb0: {
///     @fake_read(x(var@1));
///     var@2 := @discriminant(x(var@1));
///     switch move (var@2) -> 0 : isize: bb1, 1 : isize: bb4, 2 : isize: bb5, otherwise: bb6;
/// }
/// // V1 branch
/// bb1: {
///     goto bb2; // bb2 gets duplicated, not bb1
/// }
/// // V2 branch
/// bb4: {
///     goto bb2; // bb2 gets duplicated, not bb4
/// }
/// ```
/// We could detect the "fused" branches by noticing that blocks bb1 and bb4 are
/// gotos, and checking that they goto the same block, but it is annoying, really,
/// especially because it makes the control-flow reconstruction more ad-hoc. The
/// main problem is that it would be difficult to make the distinction between
/// a goto we need to ignore, and a "real" goto.
/// Consequently, whenever branhces are fused, don't use `--no-code-duplication`.
fn test1(x: E1) -> bool {
    match x {
        E1::V1 | E1::V2 => true,
        E1::V3 => false,
    }
}
