trait Trait {
    type LifetimeGat<'a>: Clone;
    type NonLifetimeGat<T>: Clone;
    type ConstGat<const N: usize>: Clone;
}

fn lifetime_gat_bound<X: Trait>(x: X::LifetimeGat<'_>) {
    let _ = x.clone();
}

fn non_lifetime_gat_bound<X: Trait>(x: X::NonLifetimeGat<u8>) {
    let _ = x.clone();
}

fn const_gat_bound<X: Trait>(x: X::ConstGat<4>) {
    let _ = x.clone();
}
