//@ known-failure

pub trait C<T> {}

pub struct S<I, F>
where
    I: Iterator,
    F: C<I::Item>, {}

pub type S2<I, F> = S<I, F>;
