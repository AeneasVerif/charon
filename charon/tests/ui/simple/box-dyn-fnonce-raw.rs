//@ known-failure
//@ no-default-options
//@ charon-args=--include=alloc::boxed::_ --include=core::ops::function::FnOnce
//@ charon-arg=--start-from=crate
//@ charon-arg=--start-from={impl core::ops::function::FnOnce for alloc::boxed::Box}
// no-default-options removes the default `--treat-box-as-builtin`
pub fn box_box(f: Box<dyn FnOnce()>) -> Box<dyn FnOnce()> {
    Box::new(f)
}
