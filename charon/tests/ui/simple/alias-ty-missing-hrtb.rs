pub trait HasLifetimeAssoc<'a> {
    type Assoc;
}

// We don't lift such a clause today; see https://github.com/AeneasVerif/charon/issues/1143.
pub type FnAlias<B> = for<'a> fn(<B as HasLifetimeAssoc<'a>>::Assoc);
