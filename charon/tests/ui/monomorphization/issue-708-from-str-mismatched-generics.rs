//@ charon-args=--extract-opaque-bodies --monomorphize
//@ charon-args=--opaque=core::num::niche_types::UsizeNoHighBit
//@ no-check-output

// Regression test for https://github.com/AeneasVerif/charon/issues/708.
fn main() {
    let _ = std::path::PathBuf::from("foo");
    let _ = String::from("Hello, world!");
}
