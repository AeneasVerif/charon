# What Charon Does For You

The purpose of Charon is to centralize the efforts of extracting information from rustc internals
and turning them into a uniform and usable shape. Here are some things that Charon does once so you
don't have to do it yourself:

TODO: explain each item

- Trait resolution (explicitly track how each trait bound was proven to hold);
- Reconstruct expressions from all the various constant representations;
- Reconstruct control-flow;
- Hide the distinction between early- and late-bound lifetime variables;
- Make non-overriden default methods in impl blocks appear as normal methods;
- `--expand-associated-types` transforms associated types into type parameters so you can ignore
  their existence in the majority of cases;
- Handle trait method implementations that have a more general signature than as declared in the trait (WIP: https://github.com/AeneasVerif/charon/issues/513);
- Represent closures as normal structs that implement the `Fn*` traits (WIP: https://github.com/AeneasVerif/charon/issues/194);
- Make implied bounds explicit (WIP: https://github.com/AeneasVerif/charon/issues/585)
