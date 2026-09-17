# Frequently Asked Questions

## I can't find a definition/what's this `<opaque>`

Try `--extract-opaque-bodies`; then try `--start-from=path::to::definition`.

Charon by default only translates the items of the current crate.
Any items from other crates are treated as "opaque",
which means that they will be listed but without their contents
(e.g. without a function body, or a type definition).

`--extract-opaque-bodies` is the hammer that removes this filter.
Now all definitions **reachable from the current crate** will be translated in full.

That will still not include a foreign definition if it's not used (even indirectly)
by the current crate.
To translate such a definition, you have to tell Charon explicitly,
using `--start-from=path::to::definition`.
Now instead of starting from the current crate, it will start from the definition listed.
If you want both, pass `--start-from=crate --start-from=path::to::definition`.

Finally, note that `--extract-opaque-bodies` can cause a **lot** of code to be translated,
which can be slow and/or hit some cases that Charon doesn't support.
You can have finer control over what gets translated using `--include`/`--opaque`.

See [What Charon Translates](what_charon_translates.md) for more details on how Charon decides what
to translate and how to control it.


## This trait doesn't have all the methods it should have

Try `--translate-all-methods`.

By default Charon only translates a default method if it is used anywhere.
E.g. this way `Iterator` only has `next` until another of its methods is used[^1].
`--translate-all-methods` instead always translates the full list of methods.

[^1]: The whole "lazy method list" feature was pretty much made specifically for `Iterator` with its
gajillion default methods and helper types.


## What is the difference between Charon and `rustc_public`?

Both projects aim at making it easy to analyze Rust code.
Beyond that, they sit at two ends of the spectrum of "do extra work":
[`rustc_public`](https://doc.rust-lang.org/nightly/nightly-rustc/rustc_public/)
intentionally stays close to the compiler's representations,
adding just enough abstraction to absorb changes as they occur between compiler versions.

In contrast, Charon aims for the most straightforward yet complete representation.
For that, we do quite a lot of work of reconstructing information coming from
various places in the compiler and hiding away any detail that's not relevant to the semantics.

See [What Charon does for you](what_charon_does_for_you.md) and
[Transformations](transformations.md) to get an idea of the kinds of reconstructions we do.

## How much can I trust what Charon outputs

Short answer: a fair amount

Longer answer: it depends on the kind of data.
Some kinds of data are translated pretty much verbatim
from what rustc gives us, and thus can be fully trusted.
Conversely, some bits involve more Charon-specific abstractions,
which leaves more room for errors.

Probably the most reliable part of Charon is the semantics of function bodies:
not only is it converted rather directly from rustc's MIR,
but it is also interpreted and compared against Miri by the [Soteria
Rust](https://soteria-tools.com/docs/features/rust) project,
which uses Charon.

Probably the least reliable part of Charon is lifetime generics:
this is where we do the most work on top of rustc to get what we want;
so mistakes there are likelier.

Another domain that doesn't rely on rustc is layout guarantees.
We compute them ourselves, based on the guarantees given by the Rust Reference.

Overall Charon is well-tested, and its authors are experts in the semantics of Rust.
If you find a bug please report it, so we can incrementally make Charon more robust for everyone!
