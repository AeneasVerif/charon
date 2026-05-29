//@ charon-arg=--monomorphize-mut=except-types
//@ charon-arg=--remove-adt-clauses
//@ charon-args=--remove-associated-types=*

fn id<T>(x: T) -> T {
    x
}

fn call_id_pair_mut<'a, T, U>(x: (&'a mut T, &'a mut U)) -> (&'a mut T, &'a mut U) {
    id(x)
}
