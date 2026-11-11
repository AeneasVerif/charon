trait Trait {}

impl<T> Trait for fn(T) {}
impl Trait for for<'a> fn(&'a (), &'a ()) {}

fn require<T: Trait>() {}

fn fixed_lifetime<'a>() {
    require::<fn(&'a ())>();
}

fn nested_binder() {
    require::<fn(for<'a> fn(&'a ()))>();
}

fn higher_ranked_impl() {
    require::<for<'b> fn(&'b (), &'b ())>();
}
