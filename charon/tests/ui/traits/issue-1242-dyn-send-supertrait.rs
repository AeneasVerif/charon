//@ charon-args=--monomorphize

trait Trait: Send {}

fn foo(x: &dyn Trait) -> &dyn Send {
    x
}
