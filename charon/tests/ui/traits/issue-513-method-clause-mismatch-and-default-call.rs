trait Trait {
    fn fold(&self)
    where
        Self: Copy;

    fn method(&self)
    where
        Self: Copy,
    {
        self.fold()
    }
}

impl Trait for () {
    fn fold(&self) {}
}
