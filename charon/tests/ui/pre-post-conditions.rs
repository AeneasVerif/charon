//@ charon-args=--start-from=crate::function
fn function() {
    #[charon::precondition]
    fn precondition() -> bool {
        true
    }

    #[charon::postcondition]
    fn postcondition() -> bool {
        true
    }

    let closure = || {
        #[charon::precondition]
        fn closure_precondition() -> bool {
            true
        }
    };
    closure();
}
