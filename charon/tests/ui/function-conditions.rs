//@ charon-args=--start-from=crate::function
fn function() {
    #[charon::precondition]
    fn precondition() -> bool {
        true
    }
}
