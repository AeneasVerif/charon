//@ aux-crate=issue-1393-foreign-static-aux.rs
//@ charon-args=--extract-opaque-bodies
// Statics have no cross-crate MIR, so the body of a foreign static's initializer is built by
// evaluating the static instead. That evaluation used to fail (leaving a `Missing` body) for
// statics with a mutable allocation, and for statics holding a pointer with no provenance.
// A generic "trivial" const has no MIR either, and const-evaluation gives up on it because it
// isn't monomorphic; we read the value rustc stored for it instead.
use issue_1393_foreign_static_aux::*;

fn foo() -> (u8, *const u8, u8) {
    (
        unsafe { MUTABLE },
        DANGLING.0,
        Generic::<bool, 3>::TRIVIAL,
    )
}
