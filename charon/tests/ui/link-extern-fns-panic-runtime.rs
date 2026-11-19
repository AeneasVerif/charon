//@ revisions=unwind,abort
//@[abort] known-failure
//@ charon-args=--link-extern-fns --start-from=std::panicking::__rust_start_panic
//@ charon-args=--include=panic_abort::__rust_start_panic
//@[unwind] rustc-args=--crate-type=bin -Cpanic=unwind
//@[abort] rustc-args=--crate-type=bin -Cpanic=abort
fn main() {}
