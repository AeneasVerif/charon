# Running Charon on Rust-for-Linux's `kernel`

Rust-for-Linux's `kernel` crate is built by Kbuild rather than Cargo.
Running Charon on it requires some acrobatics.

You must be able to build the `kernel` crate, and have `charon` in your `PATH`.

## Setup

The following assumes that the current directory is a clone of the kernel.

Pick an output path and some options to pass to Charon:

```console
$ export CHARON_OUTPUT="$PWD/kernel.llbc"
$ export CHARON_OPTIONS="--extract-opaque-bodies --monomorphize"
```

Find Charon and the toolchain it needs:

```console
$ export CHARON_BIN="$(command -v charon)"
$ export CHARON_RUSTC="$(charon toolchain-path)/bin/rustc"
```

Prepare a build directory and enable rust support:

```console
$ mkdir -p ../linux-build
$ export KERNEL_BUILD_DIR="$(realpath ../linux-build)"
$ make LLVM=1 O="$KERNEL_BUILD_DIR" RUSTC="$CHARON_RUSTC" rustavailable
$ make LLVM=1 O="$KERNEL_BUILD_DIR" RUSTC="$CHARON_RUSTC" defconfig
$ scripts/config --file "$KERNEL_BUILD_DIR/.config" -e RUST
$ make LLVM=1 O="$KERNEL_BUILD_DIR" RUSTC="$CHARON_RUSTC" olddefconfig
```

Write the following script to `$KERNEL_BUILD_DIR/charon-rustc`:

```sh
#!/usr/bin/env sh
set -eu

is_kernel=false
previous=
for argument in "$@"; do
    if [ "$previous" = "--crate-name" ] && [ "$argument" = "kernel" ]; then
        is_kernel=true
        break
    fi
    previous=$argument
done

if [ "$is_kernel" = true ]; then
    export CHARON_EMIT_ARTIFACTS=1
    exec "$CHARON_BIN" rustc \
        $CHARON_OPTIONS \
        --sysroot default \
        --dest-file "$CHARON_OUTPUT" \
        -- "$@"
else
    exec "$CHARON_RUSTC" "$@"
fi
```

and make it executable:

```console
$ chmod +x "$KERNEL_BUILD_DIR/charon-rustc"
```

The wrapper acts just like `rustc` except that if we're compiling a crate called `kernel`, it will
also extract it via Charon into the `$CHARON_OUTPUT` file.

## Run Charon

Build the `kernel` crate with the wrapper:

```console
$ touch rust/kernel/lib.rs
$ make LLVM=1 \
    O="$KERNEL_BUILD_DIR" \
    RUSTC="$KERNEL_BUILD_DIR/charon-rustc" \
    rust/kernel.o
```

The output `llbc` file can then be found in `$CHARON_OUTPUT`.

For example, the layout of Linux's C `struct list_head` can be inspected with:

```console
$ charon pretty-print --include-layouts "$CHARON_OUTPUT" > kernel.pretty
$ rg -A24 \
    'Full name: bindings::bindings_raw::list_head$' \
    kernel.pretty
```
