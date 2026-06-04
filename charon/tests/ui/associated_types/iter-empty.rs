//@ charon-args=--lift-associated-types=*

trait Apply<A> {
    type Output;
}

struct F;

impl Apply<()> for F {
    type Output = ();
}

trait Iter {
    type Item;

    fn map<B, F>(&mut self, _f: F)
    where
        F: Apply<Self::Item, Output = B>,
    {
    }
}

struct Empty<T>([T; 0]);

impl<T> Iter for Empty<T> {
    type Item = T;
}

fn g() {
    Empty::<()>([]).map(F);
}
