//@ no-default-options
//@ charon-args=--include alloc::boxed::Box --include core::ptr::unique::Unique
//@ charon-args=--include core::pin::Pin --include alloc::rc::Rc
//@ charon-args=--include alloc::sync::Arc --include core::ptr::non_null::NonNull
use std::pin::Pin;
use std::rc::Rc;
use std::sync::Arc;

trait T {
    fn by_box(self: Box<Self>);
    fn by_rc(self: Rc<Self>);
    fn by_arc(self: Arc<Self>);
    fn by_pin_mut(self: Pin<&mut Self>);
    fn by_pin_box(self: Pin<Box<Self>>);
}

pub fn call_box(x: Box<dyn T>) {
    x.by_box()
}

pub fn call_rc(x: Rc<dyn T>) {
    x.by_rc()
}

pub fn call_arc(x: Arc<dyn T>) {
    x.by_arc()
}

pub fn call_pin_mut(x: Pin<&mut dyn T>) {
    x.by_pin_mut()
}

pub fn call_pin_box(x: Pin<Box<dyn T>>) {
    x.by_pin_box()
}
