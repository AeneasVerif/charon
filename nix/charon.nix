{ cargoLock ? ../charon/Cargo.lock
, charonCommit
, craneLib
, lib
, minirustSrc
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
      || (lib.hasPrefix (toString ../charon/src/bin/generate-asts) path && !lib.hasSuffix ".llbc" path);
  };

  craneArgs = {
    inherit cargoLock;
    src = cleanedUpSrc;
    # RUSTFLAGS overrides .cargo/config.toml, so repeat the recursion limit here.
    RUSTFLAGS = "-D warnings -Zmin-recursion-limit=256";
    postPatch = ''
      mkdir -p ../crates
      cp -r ${../crates/minirust-rs} ../crates/minirust-rs
      cp -r ${minirustSrc} ../crates/minirust
      cp -r ${../crates/miniutil} ../crates/miniutil
    '';
  };

in

craneLib.buildPackage (
  craneArgs
    // rec {
    CHARON_GIT_COMMIT = charonCommit;
    buildInputs = [
      zlib
    ];
    # It's important to pass the same `RUSTFLAGS` to dependencies otherwise we'll have to rebuild them.
    cargoArtifacts = craneLib.buildDepsOnly craneArgs;

    # Build with `cargo test` to avoid building everything twice; Crane
    # installs the binaries from this build log.
    buildPhaseCargoCommand = ''
      cargoBuildLog=$(mktemp cargoBuildLogXXXX.json)
      cargo test --profile release --no-run --locked --message-format json-render-diagnostics >"$cargoBuildLog"
    '';

    checkPhaseCargoCommand = ''
      ${lib.optionalString (miriSysroots != null) ''export CHARON_MIRI_SYSROOTS="${miriSysroots}"''}
      CHARON_TOOLCHAIN_IS_IN_PATH=1 IN_CI=1 cargo test --profile release --locked
      # We also re-generate the generated AST files.
      mkdir -p src/bin/generate-asts/generated
      CHARON_TOOLCHAIN_IS_IN_PATH=1 IN_CI=1 target/release/generate-asts

      # Export the generated files to later check if they match the committed files.
      mkdir -p $out/generated-asts
      cp src/bin/generate-asts/generated/*.ml $out/generated-asts
    '';

    # Export the llbc files after Crane's post-install hook to avoid it looking
    # for path through all these files.
    postFixup = ''
      cp -r tests/ui $out/tests-llbc
      cp src/bin/generate-asts/generated/charon-itself.ullbc $out/tests-llbc
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
