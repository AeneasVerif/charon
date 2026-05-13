//@ known-failure
use std::fmt::Debug;
struct UnsizedStruct {
    x: usize,
    y: dyn Debug,
}
