pub struct S;

impl From<&u64> for S {
    fn from(_: &u64) -> S {
        S
    }
}

pub fn use_fn<'a, F: FnMut(&'a u64) -> S>(_: &'a u64, _: F) {}

pub fn test<'a>(x: &'a u64) {
    use_fn(x, S::from);
}
