//@ charon-arg=--start-from-attribute=verify::start_from,foobar::haha
#![register_tool(verify)]
#![register_tool(foobar)]

fn dont_translate() {}

#[verify::start_from] // does nothing
mod module1 {
    fn dont_translate() {}
}

mod module2 {
    fn dont_translate() {}

    #[verify::start_from]
    fn do_translate() {}

    #[foobar::haha]
    fn also_translate() {}

    struct Type1;
    struct Type2;

    trait Trait1 {
        fn method();
    }
    impl Trait1 for Type1 {
        #[verify::start_from]
        fn method() {}
    }
    impl Trait1 for Type2 {
        fn method() {
            println!("don't translate this!")
        }
    }

    trait Trait2 {}
    #[verify::start_from]
    impl Trait2 for Type1 {}
}
