//@ known-failure
//@ charon-args=--include=alloc::boxed::_
pub fn call_box(f: Box<dyn FnOnce()>) {
    f();
}
