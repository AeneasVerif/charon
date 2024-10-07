//@ known-failure
// See also `non-lifetime-gats.rs`

trait LendingIterator {
    type Item<'a>
    where
        Self: 'a;

    fn next<'a>(&'a mut self) -> Option<Self::Item<'a>>;
}

impl<'a, T> LendingIterator for Option<&'a T> {
    type Item<'b> = &'b T;

    fn next<'b>(&'b mut self) -> Option<Self::Item<'b>> {
        if let Some(item) = self {
            *self = None;
            let item = &**item;
            Some(item)
        } else {
            None
        }
    }
}

fn for_each<I: LendingIterator>(mut iter: I, f: impl for<'a> FnMut(I::Item<'a>)) {
    while let Some(item) = iter.next() {
        f(item)
    }
}

fn main() {
    let x = 42;
    let iter = Some(&42);
    let mut sum = 0;
    for_each(iter, |item| sum += *item);
    assert_eq!(sum, 42);
}
