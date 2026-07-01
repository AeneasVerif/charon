{ lib
, cacert
, runCommand
, rustToolchain
, stdenv
}:

let
  toolchain = builtins.fromTOML (builtins.readFile ../charon/rust-toolchain);
  targets = toolchain.toolchain.targets or [ ];
in

# This has a few hacks to make the output reproducible
runCommand "charon-full-mir-sysroots"
{
  __structuredAttrs = true;
  nativeBuildInputs = [ rustToolchain cacert ];
  outputHashMode = "recursive";
  outputHashAlgo = "sha256";
  outputHash = {
    x86_64-linux = "sha256-vEow+1ZK6URA5D1zZs2ME8X7ivMwZdF2Z39FXwZJuXI=";
    aarch64-linux = "sha256-Ii5Q83IZEBj7KmSMWbi8tzj7NPdjWt3zLI0/RhgwzPs=";
    aarch64-darwin = "sha256-VyUIg1L3qiSYqXjAd+vq3RB17b8OF2rFgkBlZixh2a8=";
    x86_64-darwin = "sha256-4jGqXtMvMWdrnCfsR1FkCqcTC+zlOSeBl6xfsLa6f2o=";
  }.${stdenv.hostPlatform.system};
  # Rust metadata records rust-src paths from rustToolchain; charon supplies that toolchain
  # separately.
  unsafeDiscardReferences.out = true;
}
  ''
    builddir=/tmp/charon-full-mir-sysroots-build
    export HOME="$builddir/home"
    export CARGO_HOME="$builddir/cargo"
    export TMPDIR="$builddir/tmp"
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

    rm -rf "$builddir"
  ''
