# Installation

> [!NOTE]
> This is about installing the Charon binary. There is no tutorial yet for the OCaml or Rust libraries. <!-- TODO -->

Charon is available via several channels: [prebuilt binaries](#prebuilt-binaries), [Nix](#nix), and [building from source](#building-from-source).

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
