//@ known-failure
//@ no-check-output

union Foo {
    one: u64,
    two: [u32; 2],
}

fn use_union() {
    let one = Foo { one: 42 };
    let _two = unsafe { one.two };
}
