# Getting Started

Charon is a CLI tool that helps other tools analyze Rust code.
Its basic function is that you call `charon cargo` on a Rust crate,
and Charon produces a file which contains all the information you could
possibly hope to get from the crate[^1].

This manual is a bare-bones draft that we plan to improve over time.
In the meantime, if there's something you want to know about,
come ask on [Zulip]!
We also welcome help here: writing is hard, a PR that adds even an incomplete page
to this manual can be a good prompt for us to fill the gaps.

## Project Status

Charon is under active development, with one engineer (Nadrieril) employed full-time to work on it.
It is currently beta software, i.e. without major known bugs and nearing a complete feature set.
We're working towards a 1.0, once we settle the last remaining design points, document
everything, and finish a couple features.

Charon supports all Rust features except `async` (tracked
[here](https://github.com/AeneasVerif/charon/issues/609)).

[^1]: Semantic information only however; we do not preserve syntactic information like scopes nor
distinguish say `while` from `loop`.

[Zulip]: https://aeneas-verif.zulipchat.com/#topics/channel/349819-general

<!-- TODO: -->
<!-- multi-targets -->
<!-- layout -->
<!-- vtables -->
<!-- items virtuels -->
<!-- visitors -->
<!-- generics -->
<!-- mono mode -->
<!-- names&filtering -->
<!-- trait proofs -->
<!-- tuto -->
