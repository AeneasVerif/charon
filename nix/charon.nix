{ cargoLock ? ../charon/Cargo.lock
, craneLib
, lib
, miriSysroots ? null
, zlib
}:

let

  cleanedUpSrc = lib.cleanSourceWith {
    src = ../charon;
    filter =
      path: type:
      (craneLib.filterCargoSources path type)
      || (lib.hasPrefix (toString ../charon/rust-toolchain) path) # We read it at compile-time
      || (lib.hasPrefix (toString ../charon/tests) path && !lib.hasSuffix ".llbc" path)
      || (lib.hasPrefix (toString ../charon/src/bin/generate-ml) path && !lib.hasSuffix ".llbc" path);
  };

  craneArgs = {
    inherit cargoLock;
    src = cleanedUpSrc;
    RUSTFLAGS = "-D warnings"; # Turn all warnings into errors.
  };

in

craneLib.buildPackage (
  craneArgs
    // rec {
    buildInputs = [
      zlib
    ];
    # It's important to pass the same `RUSTFLAGS` to dependencies otherwise we'll have to rebuild them.
    cargoArtifacts = craneLib.buildDepsOnly craneArgs;
    checkPhaseCargoCommand = ''
      ${lib.optionalString (miriSysroots != null) ''export CHARON_MIRI_SYSROOTS="${miriSysroots}"''}
      CHARON_TOOLCHAIN_IS_IN_PATH=1 IN_CI=1 cargo test --profile release --locked
      # We also re-generate the ocaml files.
      mkdir src/bin/generate-ml/generated
      CHARON_TOOLCHAIN_IS_IN_PATH=1 IN_CI=1 cargo run --release --locked --bin generate-ml

      # While running tests we also outputted llbc files. We export them for charon-ml tests.
      mkdir -p $out
      cp -r tests/ui $out/tests-llbc
      cp src/bin/generate-ml/charon-itself.ullbc $out/tests-llbc

      # Export the generated files to later check if they match the committed files.
      mkdir -p $out/generated-ml
      cp src/bin/generate-ml/generated/*.ml $out/generated-ml
    '';

    passthru.check-fmt = craneLib.cargoFmt craneArgs;
    passthru.check-clippy = craneLib.cargoClippy (craneArgs // {
      inherit cargoArtifacts;
      cargoClippyExtraArgs = "--all-targets -- -D warnings";
    });
    passthru.check-no-rustc = craneLib.mkCargoDerivation (craneArgs // {
      inherit cargoArtifacts;
      pnameSuffix = "-check-no-rustc";
      buildPhaseCargoCommand = "cargoWithProfile check --lib --no-default-features";
    });
  }
)
