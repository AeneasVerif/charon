//@ charon-args=--start-from=crate::function
fn function() {}

#[charon::precondition(name = "function")]
fn precondition() -> bool {
    true
}

#[charon::postcondition(name = "function")]
fn postcondition() -> bool {
    true
}
