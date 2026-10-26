trait Accept<'a> {
    fn accept(x: &'a u8);
}

// The closure captures nothing, but its input lifetime is fixed by this bound on `T`.
fn make<'a, T: Accept<'a>>() -> impl Fn(&'a u8) {
    |x| T::accept(x)
}
