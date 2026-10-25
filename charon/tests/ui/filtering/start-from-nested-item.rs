//@ revisions=crate,impl,opaque,required,defaulted
//@[impl] charon-arg=--start-from={impl crate::outer::inner::Trait for _}
//@[opaque] charon-arg=--opaque=crate::outer
//@[opaque] charon-arg=--include=crate::outer::inner::Trait
//@[required] charon-arg=--start-from=crate::outer::inner::Trait::required
//@[defaulted] charon-arg=--start-from=crate::outer::inner::Trait::defaulted

// `g` is reached through `h` before exploring `a::b`.
fn h() {
    a::b::g()
}

mod a {
    pub mod b {
        pub fn g() {
            fn in_g() {}
        }
    }
}

trait Foo {
    fn f(&self) {
        fn in_default() {}
    }
}

impl Foo for () {
    fn f(&self) {
        fn in_impl() {}
    }
}

// Retrieving the default method translates the trait before exploring `outer::inner`.
impl outer::inner::Trait for () {
    fn required() {
        fn in_impl() {}
    }

    const VALUE: () = {
        fn in_impl_const() {}
    };
}

mod outer {
    pub mod inner {
        pub trait Trait {
            fn required();

            fn defaulted() {
                fn in_default() {}
            }

            const VALUE: () = {
                fn in_default_const() {}
            };
        }
    }
}
