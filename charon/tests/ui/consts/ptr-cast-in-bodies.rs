//@ aux-crate=ptr-cast-in-bodies-aux.rs
//@ charon-args=--extract-opaque-bodies
// Statics have no cross-crate MIR, so the initializer bodies of foreign statics are built from
// their evaluated value. This exercises the lowering of pointer constants in bodies.
use ptr_cast_in_bodies_aux::*;

fn main() {
    let _ = &END;
    let _ = &BYTE;
    let _ = &OOB;
    let _ = &FN_RAW;
}
