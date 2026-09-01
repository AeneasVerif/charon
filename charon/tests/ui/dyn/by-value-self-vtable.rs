//! A trait method taking `self: Self` by value is still dyn-compatible; its vtable shim must
//! take the receiver via `*mut Self` (like rustc's `ShimKind::VTable`) since a `dyn Trait`
//! value can't be passed directly.
trait Consume {
    fn consume(self) -> u32;
    fn read(&self) -> u32;
}

struct S(u32);
impl Consume for S {
    fn consume(self) -> u32 {
        self.0
    }
    fn read(&self) -> u32 {
        self.0
    }
}

// `Self` being itself a pointer must not be mistaken for the `*mut Self` shim receiver.
impl Consume for *mut u32 {
    fn consume(self) -> u32 {
        unsafe { *self }
    }
    fn read(&self) -> u32 {
        unsafe { **self }
    }
}

fn mk() -> Box<dyn Consume> {
    Box::new(S(42))
}

fn mk_ptr(x: *mut u32) -> Box<dyn Consume> {
    Box::new(x)
}

fn main() {
    let x = mk();
    let _v = x.read();
    let mut n = 5u32;
    let p = mk_ptr(&mut n);
    let _v = p.read();
}
