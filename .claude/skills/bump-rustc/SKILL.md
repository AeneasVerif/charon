---
name: bump-rustc
description: Bump Charon's pinned rustc nightly toolchain; use this when asked to update the rustc version, or when fixing breakage caused by a newer rustc.
---

# Bumping the rustc toolchain

Charon uses `rustc` internal APIs, so we pin an exact nightly version against which to build. The pin is set in `charon/rust-toolchain`; updating that pin means using the latest nightly there. For the nix to build, the oxalica-rust commit in `flake.nix` must also be bumped to the latest.

Updating the toolchain typically requires a series of small edits to adapt to changes happening in the compiler; it rarely requires significant rework. The best way to go about it is to figure out which `rust-lang/rust` commits correspond to the before/after nightlies (you can use `make toolchain-commit` before and after to get it), and grep through the diff to see if e.g. an API we're using got renamed. For more complex changes it's also useful to identify the PR that made the change, in order to understand how to best adapt to it.

Once you've got everything to compile, inspect the diff to the test outputs. There will typically be many small changes to the outputted MIR; we must look out for changes we don't want, for example because one of our reconstruction passes no longer catches the right pattern, or something else changed in rustc internals that we hadn't accounted for.

When you're done, please list out the nontrivial changes you had to make, along with the Rust PR(s) that caused it, so we can have a second look.

If you've encountered a change that seems really complicated to adapt to, let us know! There are several options available to us that are better than you spending a lot of effort working around it: updating to an intermediate nightly, anticipating the change by adapting Charon separately from the toolchain update, and even discusing with rustc devs to find the best solution.
