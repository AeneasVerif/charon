#![feature(derive_coerce_pointee)]
use std::fmt::Display;
use std::marker::CoercePointee;
use std::rc::Rc;
use std::sync::Arc;

#[derive(CoercePointee)]
#[repr(transparent)]
struct MyPtr<T: ?Sized>(Box<T>);

impl<T> MyPtr<T> {
    fn new(x: T) -> Self {
        MyPtr(Box::new(x))
    }
}

fn foo() {
    let array: [_; 2] = [0, 0];
    let _: &[_] = &array;
    let _: Box<[_]> = Box::new(array);
    let _: Rc<[_]> = Rc::new(array);
    let _: Arc<[_]> = Arc::new(array);
    let _: MyPtr<[_]> = MyPtr::new(array);

    let string = String::new();
    let _: &dyn Display = &string;
    let _: Box<dyn Display> = Box::new(string.clone());
    let _: Rc<dyn Display> = Rc::new(string.clone());
    let _: Arc<dyn Display> = Arc::new(string.clone());
    let _: MyPtr<dyn Display> = MyPtr::new(string.clone());
}
