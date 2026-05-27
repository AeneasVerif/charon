//@ no-default-options
//@ charon-arg=--monomorphize-mut=except-types
//@ charon-arg=--remove-adt-clauses
//@ charon-args=--lift-associated-types=*
#![feature(register_tool)]
#![register_tool(pattern)]

fn identity<T>(x: T) -> T {
    x
}

#[pattern::pass(call[0], "test_crate::identity<&'_ mut @T>")]
#[pattern::pass(call[0], "test_crate::identity<@T>")]
#[pattern::fail(call[0], "test_crate::identity<&'_ @T>")]
#[pattern::pass(call[1], "test_crate::identity<core::option::Option<&'_ mut @T>>")]
fn use_id_mut<A>(mut x: A) {
    let _ = identity(&mut x);
    let _ = identity(Some(&mut x));
}
