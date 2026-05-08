//@ charon-args=--remove-adt-clauses
//@ charon-args=--remove-associated-types=*
// Regression test: closure ADTs reference trait impls (FnOnce/FnMut/Fn) that depend on
// trait clauses inherited from the parent function. Stripping all ADT clauses would invalidate
// those references, so closure ADTs must keep their clauses.
fn f<T: Copy>(x: &T) {
    let _c = || *x;
}

fn g<T: Copy>(x: T) {
    let _c = || x;
}
