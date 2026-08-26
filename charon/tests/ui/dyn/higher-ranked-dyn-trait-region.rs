//@ known-failure

pub trait Trait<'a> {}

pub fn use_type<T: 'static>() {}

fn main() {
    use_type::<for<'a> fn(&'a dyn Trait<'a>)>();
}
