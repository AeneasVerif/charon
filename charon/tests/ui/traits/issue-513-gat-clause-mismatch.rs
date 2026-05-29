trait Trait: Sized {
    // To mention the type I need `Self` to be `Copy`.
    type Type
    where
        Self: Copy;
}

impl Trait for () {
    // To mention the type I only need `Self` to be `Clone`.
    type Type
        = ()
    where
        Self: Clone;
}

fn foo<T: Trait + Copy>(_: &T::Type) {}

fn main() {
    let _: <() as Trait>::Type = ();
}
