fn function() {
    #[charon::contract(kind = "pre", parent)]
    fn precondition() -> bool {
        true
    }

    #[charon::contract(kind = "post", for = "crate::function")]
    fn postcondition() -> bool {
        true
    }

    fn sibling() {}

    #[charon::contract(kind = "pre", for = "sibling")]
    fn sibling_precondition() -> bool {
        true
    }

    let closure = || {
        #[charon::contract(kind = "pre", parent)]
        fn closure_precondition() -> bool {
            true
        }
    };
    closure();
}

mod other {
    pub fn path_target() {}
}

#[charon::contract(kind = "post", for = "crate::other::path_target")]
fn path_postcondition() -> bool {
    true
}

#[charon::contract(kind = "invariant", for = "Trait")]
fn trait_contract() -> bool {
    true
}

trait Trait {
    fn method();

    #[charon::contract(kind = "pre", for = "method")]
    fn method_precondition() -> bool {
        true
    }
}

#[charon::contract(kind = "invariant", for = "MyType")]
fn type_invariant() -> bool {
    true
}

struct MyType;
