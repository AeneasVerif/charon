//@ known-failure
//@ charon-args=--extract-opaque-bodies --desugar-drops --precise-drops --monomorphize

trait Trait: Send {}

fn foo(x: &dyn Trait) -> &dyn Send {
    x
}
