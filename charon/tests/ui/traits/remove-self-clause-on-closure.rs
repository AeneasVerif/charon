//@ charon-args=--remove-adt-clauses --lift-associated-types=_ --remove-unused-self-clauses
pub trait Trait {
    fn method(&self) {
        let _ = || 0usize;
    }
}

impl Trait for () {}
