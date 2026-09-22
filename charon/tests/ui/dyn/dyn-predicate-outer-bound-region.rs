//@ known-failure

pub fn f<'a>(_: &dyn Fn(&'a ())) {}

fn main() {}
