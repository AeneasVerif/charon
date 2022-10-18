{
  description = "Charon";

  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    nixpkgs.url = "nixpkgs/nixos-unstable";
    rust-overlay = {
      url = "github:oxalica/rust-overlay";
      inputs.flake-utils.follows = "flake-utils";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    crane = {
      url = "github:ipetkov/crane";
      inputs.flake-utils.follows = "flake-utils";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs = { self, flake-utils, nixpkgs, rust-overlay, crane }:
    flake-utils.lib.eachSystem [ "x86_64-linux" ] (system:
      let
        pkgs = import nixpkgs {
          inherit system;
          overlays = [ (import rust-overlay) ];
        };
        rustToolchain = pkgs.rust-bin.nightly."2022-01-29".default.override {
          extensions = [ "rust-src" "rustc-dev" "llvm-tools-preview" ];
        };
        craneLib = (crane.mkLib pkgs).overrideToolchain rustToolchain;
        charon = craneLib.buildPackage { src = ./charon; };
        tests = let cargoArtifacts = craneLib.buildDepsOnly { src = ./tests; };
        in craneLib.buildPackage {
          name = "tests";
          src = ./tests;
          inherit cargoArtifacts;
          buildPhase = ''
            # Run the tests for Charon
            DEST=$out CHARON="${charon}/bin/cargo-charon --cargo-no-rust-version" \
            make charon-tests
          '';
          doCheck = false;
          dontInstall = true;
        };

        tests-polonius = let
          cargoArtifacts = craneLib.buildDepsOnly { src = ./tests-polonius; };
        in craneLib.buildPackage {
          name = "tests-polonius";
          src = ./tests-polonius;
          inherit cargoArtifacts;
          # We deactivate the tests performed with Cargo (`cargo test`) as
          # they will fail because we need Polonius
          doCheck = false;
          buildPhase = ''
            # Run the tests for Charon
            DEST=$out CHARON="${charon}/bin/cargo-charon --cargo-no-rust-version" \
            make charon-tests

            # Nix doesn't run the cargo tests, so run them by hand
            make cargo-tests
          '';
          dontInstall = true;
        };
      in {
        packages = {
          inherit charon;
          default = charon;
        };
        hydraJobs = { inherit charon tests tests-polonius; };
      });
}
