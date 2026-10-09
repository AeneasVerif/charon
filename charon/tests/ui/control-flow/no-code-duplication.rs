//@ revisions=duplicate,forward-break
//@[forward-break] charon-args=--no-code-duplication
//! Bodies whose control-flow graph can't be mapped to nested `if`s without duplicating a block.
//! The `duplicate` revision emits one copy of the shared block per incoming branch; the
//! `forward-break` revision emits it once inside an enclosing `loop` that the branches `break` to.
fn do_something() {}
fn do_something_else() {}
fn do_something_at_the_end() {}

// The `else` block is reachable from both of the `&&`'s short-circuit paths.
fn shared_tail(a: &[u8]) -> usize {
    let mut sampled = 0;
    if a[0] < 42 && a[1] < 16 {
        sampled += 100;
    } else {
        sampled += 101;
    }
    sampled
}

// A diamond with a diagonal: the guard failing joins the `_` arm.
fn diamond_with_diagonal(opt: Option<u32>) {
    match opt {
        Some(x) if x >= 42 => do_something(),
        _ => do_something_else(),
    }
    do_something_at_the_end()
}
