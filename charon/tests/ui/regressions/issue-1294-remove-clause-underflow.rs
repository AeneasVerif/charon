//@ charon-args=--remove-unused-self-clauses
trait Trait {
    type Assoc<T>;
    fn method()
    where
        Self::Assoc<u8>: Clone,
    {
    }
}
