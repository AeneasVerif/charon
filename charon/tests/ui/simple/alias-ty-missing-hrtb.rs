pub trait HasLifetimeAssoc<'a> {
    type Assoc;
}

pub type FnAlias<B> = for<'a> fn(<B as HasLifetimeAssoc<'a>>::Assoc);

pub trait HasTwoLifetimeAssoc<'a, 'b> {
    type Assoc;
}

pub type NestedFnAlias<B> = for<'a> fn(for<'b> fn(<B as HasTwoLifetimeAssoc<'a, 'b>>::Assoc));

pub trait HasMixedLifetimeAssoc<'outer, 'late> {
    type Assoc;
}

pub type MixedFnAlias<'outer, B> =
    for<'late> fn(<B as HasMixedLifetimeAssoc<'outer, 'late>>::Assoc);
