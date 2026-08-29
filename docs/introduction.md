# Introduction

Charon is a CLI tool that helps other tools analyze Rust code.
Its basic function is that you call `charon cargo` on a Rust crate,
and Charon produces a `crate_name.llbc` file which contains
all the information you could possibly hope to get from the crate[^1].

This manual is a bare-bones draft that we plan to improve over time.
In the meantime, f there's something you want to know about,
come ask on [Zulip]!
We also welcome help here: writing is hard, a PR that adds even an incomplete page
to this manual can be a good prompt for us to fill the gaps.

[^1]: Semantic information only however; we do not preserve syntactic information like scopes nor
distinguish say `while` from `loop`.
[Zulip]: https://aeneas-verif.zulipchat.com/#topics/channel/349819-general
