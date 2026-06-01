trait Takes<T> {}

impl Takes<bool> for () {}

trait Trait {
    type Item;

    fn consume<P: Takes<Self::Item>>(&self);

    fn provided(&self)
    where
        Self: Trait<Item = bool>,
    {
        self.consume::<()>();
    }
}

impl Trait for () {
    type Item = u32;

    fn consume<P: Takes<Self::Item>>(&self) {}

    // This gets a copy of `provided` which passes a proof of `(): Takes<bool>` to `consume`, which
    // is fine because we're inside an incoherent context but my typechecker doesn't know that.
}
