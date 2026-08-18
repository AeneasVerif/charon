{ lib
, runCommand
, rustToolchain
}:

let
  toolchain = builtins.fromTOML (builtins.readFile ../charon/rust-toolchain);
  targets = toolchain.toolchain.targets or [ ];
in

runCommand "charon-full-mir-sysroots"
{
  nativeBuildInputs = [ rustToolchain ];
}
  ''
    export HOME="$NIX_BUILD_TOP/home"
    export CARGO_HOME="$NIX_BUILD_TOP/cargo"
    export CARGO_NET_OFFLINE=true
    unset CHARON_ARGS CHARON_USING_CARGO RUSTC_WORKSPACE_WRAPPER RUSTC_WRAPPER
    mkdir -p "$HOME" "$CARGO_HOME"

    cat > "$CARGO_HOME/config.toml" <<END
    [source.crates-io]
    replace-with = "vendored-sources"
    [source.vendored-sources]
    directory = "$(rustc --print sysroot)/lib/rustlib/src/rust/library/vendor"
    END

    sysroot=
    # This relies on the fact that miri uses the same directory for all sysroots.
    for target in ${lib.escapeShellArgs targets}; do
      sysroot="$(cargo miri setup --target="$target" --print-sysroot)"
    done

    mkdir -p "$out"
    cp -a "$sysroot/." "$out/"
  ''
