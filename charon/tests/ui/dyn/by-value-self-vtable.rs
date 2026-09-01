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

fn mk() -> Box<dyn Consume> {
    Box::new(S(42))
}

fn main() {
    let x = mk();
    let _v = x.read();
}
