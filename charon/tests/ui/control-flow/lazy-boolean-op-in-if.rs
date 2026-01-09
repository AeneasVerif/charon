fn foo() -> bool {
    true
}
fn bar() -> bool {
    false
}

fn do_something() {}
fn do_something_else() {}
fn do_something_at_the_end() {}

fn main() {
    // `&&` inside `if` is treated specially by Rust: must like for `if let && let`, it is
    // considered as directly being control-flow, instead of computing a boolean first.
    if foo() && bar() {
        do_something()
    } else {
        do_something_else()
    }
    do_something_at_the_end()
}
