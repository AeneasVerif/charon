{
  bintools,
  craneLib,
  lib,
  makeWrapper,
  runCommand,
  rustToolchain,
  stdenv,
  zlib,
}:

let

  cleanedUpSrc = lib.cleanSourceWith {
    src = ../charon;
    filter =
      path: type:
      (craneLib.filterCargoSources path type)
      || (lib.hasPrefix (toString ../charon/tests) path && !lib.hasSuffix ".llbc" path);
  };

  craneArgs = {
    # Copy the `rust-toolchain` file because charon reads it at build time.
    src = runCommand "charon-clean-src" { } ''
      mkdir $out
      cp -r ${cleanedUpSrc}/* $out/
      cp ${../rust-toolchain} $out/rust-toolchain
    '';
    RUSTFLAGS = "-D warnings"; # Turn all warnings into errors.
  };

in

craneLib.buildPackage (
  craneArgs
  // {
    buildInputs = [
      makeWrapper
      zlib
    ];
    # For `install_name_tool`.
    nativeBuildInputs = lib.optionals (stdenv.isDarwin) [ bintools ];
    # It's important to pass the same `RUSTFLAGS` to dependencies otherwise we'll have to rebuild them.
    cargoArtifacts = craneLib.buildDepsOnly craneArgs;
    # Make sure the toolchain is in $PATH so that `cargo` can work
    # properly. On mac we also have to tell `charon-driver` where to find
    # the rustc_driver dynamic library; this is done automatically on
    # linux.
    postFixup =
      ''
        wrapProgram $out/bin/charon \
          --set CHARON_TOOLCHAIN_IS_IN_PATH 1 \
          --prefix PATH : "${lib.makeBinPath [ rustToolchain ]}"
      ''
      + (lib.optionalString stdenv.isDarwin ''
        # Ensures `charon-driver` finds the dylibs correctly.
        install_name_tool -add_rpath "${rustToolchain}/lib" "$out/bin/charon-driver"
      '');
    checkPhaseCargoCommand = ''
      CHARON_TOOLCHAIN_IS_IN_PATH=1 IN_CI=1 cargo test --profile release --locked
      # While running tests we also outputted llbc files. We export them for charon-ml tests.
      mkdir -p $out/tests-llbc
      cp tests/**/*.llbc $out/tests-llbc
    '';

    passthru.check-fmt = craneLib.cargoFmt craneArgs;
  }
)
