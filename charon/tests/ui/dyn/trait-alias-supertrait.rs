#![feature(trait_alias)]
trait Base {}
trait Alias = Base;
trait Sub: Alias {}

fn needs_alias<T: Alias + ?Sized>(_: &T) {}

fn test(x: &dyn Sub) {
    needs_alias(x);
}
