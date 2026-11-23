# Polymorphic vs Monomorphic Code

By default Charon translates items as they are written, with generic functions, structs, traits staying generic. With `--monomorphize` however, Charon instead translates each item once for each generics it is instantiated with. Generic items are then only instantiated according to their uses; if a generic item is never seen fully instantiated, it is not translated.

## Trait Proofs

Morally, trait proofs are part of the instantiation of an item, such that a `foo::<u32>` using an `impl Tr for u32` to prove `u32: Tr` is _distinct_ from an item using some other proof for `u32: Tr`.

However, coherence ensures this doesn't happen: a monomorphic trait clause has at most one solution. As such, in monomorphic mode we forget which proofs were used.

This only works if the clauses of the item actually hold. With [`#![feature(trivial_bounds)]`](https://github.com/rust-lang/rust/issues/48214), an item can have clauses that don't:

```rust
#![feature(trivial_bounds)]
struct Foo;
trait Tr {}

fn foo() where Foo: Tr {}
fn bar() where Foo: Tr { foo() }
```

Here `foo` and `bar` are not generic, but no instantiation of them exists since `Foo: Tr` doesn't hold. In monomorphic mode, Charon therefore skips monomorphic items whose clauses are unsatisfiable.
