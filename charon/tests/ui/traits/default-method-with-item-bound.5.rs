//@ charon-args=--translate-all-methods

trait Iterator {
    type Item;

    fn rposition<P>(&mut self)
    where
        P: FnMut(Self::Item),
        Self: DoubleEndedIterator;
}

trait DoubleEndedIterator: Iterator {}

struct Iter<'a, T>(&'a T);

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn rposition<P>(&mut self)
    where
        P: FnMut(Self::Item),
        Self: DoubleEndedIterator,
    {
    }
}

impl<'a, T> DoubleEndedIterator for Iter<'a, T> {}
