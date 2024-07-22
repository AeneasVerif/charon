{ bintools
, cargoLock ? ../charon/Cargo.lock
, craneLib
, lib
, makeWrapper
, runCommand
, rustToolchain
, stdenv
, zlib
,
}:

let

  cleanedUpSrc = lib.cleanSourceWith {
    src = ../charon;
    filter =
      path: type:
      (craneLib.filterCargoSources path type)
      || (lib.hasPrefix (toString ../charon/tests) path && !lib.hasSuffix ".llbc" path)
      || (lib.hasPrefix (toString ../charon/src/bin/generate-ml) path && !lib.hasSuffix ".llbc" path);
  };

  craneArgs = {
    inherit cargoLock;
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
    postPatch = ''
      # These files are symlinks outside of the charon directory. We remove
      # them so that we regenerate fresh files in their place.
      rm -f src/bin/generate-ml/GAst.ml
      rm -f src/bin/generate-ml/Types.ml
      rm -f src/bin/generate-ml/GAstOfJson.ml
    '';
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
      # We also re-generate the ocaml files.
      CHARON_TOOLCHAIN_IS_IN_PATH=1 IN_CI=1 cargo run --release --locked --bin generate-ml

      # While running tests we also outputted llbc files. We export them for charon-ml tests.
      mkdir -p $out/tests-llbc
      cp tests/**/*.llbc $out/tests-llbc
      cp src/bin/generate-ml/charon-itself.llbc $out/tests-llbc

      # Export the generated files to later check if they match the committed files.
      mkdir -p $out/generated-ml
      cp src/bin/generate-ml/*.ml $out/generated-ml
    '';

    passthru.check-fmt = craneLib.cargoFmt craneArgs;
  }
)
