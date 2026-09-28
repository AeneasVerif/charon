//! This tests that we order decl methods _after_ the trait.
use foo::Trait;
fn main() {
    fn takes_trait<T: Trait>(x: &T) {
        x.defaulted()
    }
    let _ = takes_trait(&());
    let _ = ().defaulted();
}

// Make the module opaque so the trait is discovered like a foreign trait. This affects order.
#[charon::opaque]
mod foo {
    pub trait Trait {
        fn defaulted(&self) {}
    }

    impl Trait for () {}
}
