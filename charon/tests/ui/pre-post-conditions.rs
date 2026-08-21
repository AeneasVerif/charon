fn function() {
    #[charon::precondition(parent)]
    fn precondition() -> bool {
        true
    }

    #[charon::postcondition(parent)]
    fn postcondition() -> bool {
        true
    }

    fn sibling() {}

    #[charon::precondition(for = "sibling")]
    fn sibling_precondition() -> bool {
        true
    }

    let closure = || {
        #[charon::precondition(parent)]
        fn closure_precondition() -> bool {
            true
        }
    };
    closure();
}

mod other {
    pub fn path_target() {}
}

#[charon::postcondition(for = "crate::other::path_target")]
fn path_postcondition() -> bool {
    true
}

trait Trait {
    fn method();

    #[charon::precondition(for = "method")]
    fn method_precondition() -> bool {
        true
    }
}

#[charon::postcondition(for = "MyType")]
fn type_postcondition() -> bool {
    true
}

struct MyType;
