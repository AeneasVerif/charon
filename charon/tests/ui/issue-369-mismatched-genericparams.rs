//@ known-failure

fn maybe() -> Option<usize> {
    Some(42)
}

fn pop() -> Option<()> {
    let _ = maybe()?;
    Some(())
}
