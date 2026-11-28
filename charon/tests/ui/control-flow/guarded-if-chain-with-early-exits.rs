//@ revisions=duplicate,forward-break
//@[forward-break] charon-args=--no-code-duplication
//! A chain of `if`s whose bodies can leave the labelled block early, followed by a shared tail
//! (the shape of c2rust-style state machines). The `match` takes the shared tail as its exit, so
//! each `if` must be followed by the next one instead: copying the rest of the chain into both
//! branches of each `if` made the output grow exponentially with the length of the chain.
fn step(_: u32) -> bool {
    true
}
fn finish(_: u32) {}

pub fn chain(mut state: u32) -> u32 {
    let ret = 'ret: {
        state = match state {
            0 => 0,
            1 => 1,
            _ => break 'ret 0,
        };
        if state == 0 {
            if step(0) {
                break 'ret 10;
            }
            state = 1;
        }
        if state == 1 {
            if step(1) {
                break 'ret 11;
            }
            state = 2;
        }
        if state == 2 {
            if step(2) {
                break 'ret 12;
            }
            state = 3;
        }
        20
    };
    finish(state);
    ret
}

// The same with a loop in each stage that can also leave the labelled block. The exit of the loop
// must be the code after it (the rest of the stage), not the shared tail, or the rest of the chain
// ends up inside the loop.
fn pull(_: u32) -> Option<u32> {
    None
}

pub fn chain_with_loops(mut state: u32) -> u32 {
    let ret = 'ret: {
        if state == 0 {
            let x = loop {
                if step(0) {
                    break 0;
                }
                if pull(0).is_none() {
                    break 'ret 10;
                }
            };
            state = x + 1;
        }
        if state == 1 {
            let x = loop {
                if step(1) {
                    break 1;
                }
                if pull(1).is_none() {
                    break 'ret 11;
                }
            };
            state = x + 1;
        }
        if state == 2 {
            let x = loop {
                if step(2) {
                    break 2;
                }
                if pull(2).is_none() {
                    break 'ret 12;
                }
            };
            state = x + 1;
        }
        20
    };
    finish(state);
    ret
}
