//@ known-failure
//@ charon-args=--lift-associated-types=*
pub trait HasAssoc {
    type Assoc;
    fn method(&self);
}

pub trait T1<O>: HasAssoc<Assoc = O> {}

pub trait T2<O>: T1<O> {}

pub fn x<O, F: T2<O>>(f: F) {
    f.method()
}
