//@ charon-args=--start-from=crate::function
fn function(input: i32) -> i32 {
    input + input
}

#[charon::precondition(name = "function")]
fn precondition(input: i32) -> bool {
    input != 0
}

#[charon::postcondition(name = "function")]
fn postcondition(input: i32, output: i32) -> bool {
    output == input + 42
}
