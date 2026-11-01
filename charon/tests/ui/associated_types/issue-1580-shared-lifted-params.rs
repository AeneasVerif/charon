//@ charon-args=--lift-associated-types=* --hide-marker-traits
//! Two paths reaching the same associated type must share a single lifted parameter.

/// `<A::L as Lang>::T` and `<B::L as Lang>::T` are the same type.
mod equality_constraint {
    pub trait Lang {
        type T;
    }
    pub trait Abstr {
        type L: Lang;
    }
    pub fn put<A: Abstr>(_: <A::L as Lang>::T) {}
    pub fn f<A: Abstr, B: Abstr<L = A::L>>(x: <A::L as Lang>::T) {
        put::<B>(x)
    }
    /// `<A::L as Lang>::T` is `L::T`, which is known to be `u8`.
    pub fn known_value<L: Lang<T = u8>, A: Abstr<L = L>>(x: u8) {
        put::<A>(x)
    }
    /// `<A::L as Lang>::T` is `<B::L as Lang>::T`, which is known to be `u8`.
    pub fn known_value_via_equality<A: Abstr, B: Abstr<L = A::L>>(x: <A::L as Lang>::T)
    where
        B::L: Lang<T = u8>,
    {
        put::<A>(x)
    }
}

/// `L::T` is reachable both from `L: Lang` and from the `L: Lang` clause of `P: Process<L>`.
mod clause_on_trait_param {
    pub trait Lang {
        type T;
    }
    pub trait Process<L: Lang> {
        fn run(x: L::T);
    }
    pub fn explore<L: Lang, P: Process<L>>(x: L::T) {
        P::run(x)
    }
}

/// The impl binds `make` using its own `L: Logic` clause instead of the method-level one.
mod impl_bound_for_method_bound {
    pub trait Logic {
        type B;
    }
    pub trait State<L> {
        fn make(b: L::B) -> L::B
        where
            L: Logic;
    }
    impl<L: Logic> State<L> for () {
        fn make(b: L::B) -> L::B {
            b
        }
    }
}

/// `Both` reaches `Self: X` through two parent clauses.
mod trait_with_two_paths {
    pub trait X {
        type Assoc;
    }
    pub trait A: X {}
    pub trait B: X {}
    pub trait Both: A + B {}
    impl X for u8 {
        type Assoc = bool;
    }
    impl A for u8 {}
    impl B for u8 {}
    impl Both for u8 {}

    pub fn via_b<T: B>(x: <T as X>::Assoc) -> <T as X>::Assoc {
        x
    }
    pub fn via_both<T: Both>(x: <T as X>::Assoc) -> <T as X>::Assoc {
        via_b::<T>(x)
    }
    pub fn call() -> bool {
        via_both::<u8>(true)
    }
}
