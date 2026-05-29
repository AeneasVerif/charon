pub trait Trait {
    type Item;
    fn defaulted(&self)
    where
        Self: Copy,
    {
    }
}

impl<T> Trait for Option<T> {
    type Item = T;
}
impl Trait for String {
    type Item = String;
}
