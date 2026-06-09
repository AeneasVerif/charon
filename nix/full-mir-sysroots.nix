{ lib
, cacert
, runCommand
, rustToolchain
}:

let
  toolchain = builtins.fromTOML (builtins.readFile ../charon/rust-toolchain);
  targets = toolchain.toolchain.targets or [ ];
in

# This has a few hacks to make the output reproducible
runCommand "charon-full-mir-sysroots"
{
  __structuredAttrs = true;
  nativeBuildInputs = [ rustToolchain ];
  outputHashMode = "recursive";
  outputHashAlgo = "sha256";
  outputHash = "sha256-Ha3594AoFhsQWieAa+XdklLV4eBnoL2b4XmfAw2zEBY=";
  # Rust metadata records rust-src paths from rustToolchain; charon supplies that toolchain
  # separately.
  unsafeDiscardReferences.out = true;
}
  ''
    export HOME="/build/home"
    export CARGO_HOME="/build/cargo"
    export TMPDIR="/build/tmp"
    export SSL_CERT_FILE="${cacert}/etc/ssl/certs/ca-bundle.crt"
    unset CHARON_ARGS CHARON_USING_CARGO RUSTC_WORKSPACE_WRAPPER RUSTC_WRAPPER
    mkdir -p "$HOME" "$CARGO_HOME" "$TMPDIR"

    sysroot=
    # This relies on the fact that miri uses the same directory for all sysroots.
    for target in ${lib.escapeShellArgs targets}; do
      sysroot="$(cargo miri setup --target="$target" --print-sysroot)"
    done

    mkdir -p "$out"
    cp -a "$sysroot/." "$out/"
    # Remove some non-reproducible outputs we don't need
    find "$out" -name '*.d' -delete
    find "$out" -name '*custom_local_sysroot-*' -delete
  ''
