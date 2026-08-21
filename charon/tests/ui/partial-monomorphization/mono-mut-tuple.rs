//@ charon-arg=--monomorphize-mut
//! Check pretty-printing of tuples with `--monomorphize-mut`

fn id<T>(x: T) -> T {
    x
}

fn call<'a, T>(x: (&'a mut u32, T)) -> (&'a mut u32, T) {
    id(x)
}
