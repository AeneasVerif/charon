pub struct Foo<'a, 'b>(&'a &'b u32);

impl<'a, 'b> Foo<'a, 'b> {
    // The impl's self type implies `'b: 'a`, even without a `self` parameter.
    pub fn shorten(x: &'b u32) -> &'a u32 {
        x
    }
}
