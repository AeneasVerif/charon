# Installation

> [!NOTE]
> This is about installing the Charon binary. There is no tutorial yet for the OCaml library. <!-- TODO -->

Charon is available via several channels: [Nix](#nix), [prebuilt binaries](#prebuilt-binaries), and [building from source](#building-from-source).

To get the version of the current Charon release, you can run:
```sh
charon version
# 0.1.259 (e4c4510d817097accb931fad0c14f357ce94066d)
```

The version number follows semver; though for now we are still in the `0.1.x` versions. We hope to soon start providing better stability guarantees.

In parentheses is the git commit hash of the Charon source code that was used to build the binary. This is useful for debugging, to know exactly which version of the source code is being run. The version number is always bumped when the AST changes; however we reserve the rights to modify the translation without bumping the version number, e.g. for minor bug fixes.

## Prebuilt Binaries

Charon provides prebuilt binaries for Linux (`aarch64`, `x86_64`) and macOS (`aarch64`). You can download the latest release from the [GitHub releases page](https://github.com/AeneasVerif/charon/releases).

## Nix

To install Charon through Nix, just run:
```bash
nix run github:AeneasVerif/charon
```

## Building from Source

Charon may also be built from source. First, you will need to have [rustup](https://rustup.rs/) installed. Make sure you don't have pre-existing Rust or Cargo installations through means other than rustup (e.g. brew), as this can cause issues with the build.

Then, clone the repository and run the following commands. The resulting binary will be in `bin/charon`:
```bash
git clone https://github.com/AeneasVerif/charon.git
cd charon
make build-charon-rust
```
