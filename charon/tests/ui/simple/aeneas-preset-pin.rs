//@ no-default-options
//@ charon-args=--preset=aeneas
// The `aeneas` preset exposes the definition of `core::pin::Pin`: Aeneas rewrites the calls to its
// (generic) functions into aggregates and field accesses.
use std::pin::Pin;

pub fn new<T: Unpin>(x: &mut T) -> Pin<&mut T> {
    Pin::new(x)
}

pub fn get_mut<T: Unpin>(p: Pin<&mut T>) -> &mut T {
    p.get_mut()
}
