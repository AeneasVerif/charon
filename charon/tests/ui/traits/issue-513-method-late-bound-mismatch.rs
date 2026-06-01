trait Trait: Sized {
    fn method(self, other: &'static u32);
}

impl Trait for () {
    // This implementation is more general because it works for non-static refs.
    fn method(self, _other: &u32) {}
}

fn main() {
    let _ = ().method(&1u32);
}
