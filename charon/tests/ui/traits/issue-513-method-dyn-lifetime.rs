//@ charon-args=--hide-marker-traits
//! Minimized from rustc's nll/issue-54779-anon-static-lifetime.rs.
trait Trait {}

trait Use<C: ?Sized> {
    fn method<'a>(context: &'a C);
}

impl Use<dyn Trait + 'static> for () {
    // Charon gives this method the argument `&'a (dyn Trait + 'static)` as given by the trait
    // definition, ignoring that the user chose a more general signature.
    fn method<'a>(context: &'a (dyn Trait + 'a)) {}
}
