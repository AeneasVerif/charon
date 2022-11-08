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
        rustToolchain = pkgs.rust-bin.nightly."2022-10-20".default.override {
          extensions = [ "rust-src" "rustc-dev" "llvm-tools-preview" ];
        };
        craneLib = (crane.mkLib pkgs).overrideToolchain rustToolchain;
        charon =
          let cargoArtifacts = craneLib.buildDepsOnly { src = ./charon; };
          in craneLib.buildPackage {
            src = ./charon;
            inherit cargoArtifacts;
          };
        tests = let cargoArtifacts = craneLib.buildDepsOnly { src = ./tests; };
        in craneLib.buildPackage {
          name = "tests";
          src = ./tests;
          inherit cargoArtifacts;
          buildPhase = ''
            # Run the tests for Charon
            DEST=$out CHARON="${charon}/bin/charon --cargo-no-rust-version" \
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
            DEST=$out CHARON="${charon}/bin/charon --cargo-no-rust-version" \
            make charon-tests

            # Nix doesn't run the cargo tests, so run them by hand
            make cargo-tests
          '';
          dontInstall = true;
        };

        ocamlPackages = pkgs.ocamlPackages;
        easy_logging = ocamlPackages.buildDunePackage rec {
          pname = "easy_logging";
          version = "0.8.2";
          src = pkgs.fetchFromGitHub {
            owner = "sapristi";
            repo = "easy_logging";
            rev = "v${version}";
            sha256 = "sha256-Xy6Rfef7r2K8DTok7AYa/9m3ZEV07LlUeMQSRayLBco=";
          };
          buildInputs = [ ocamlPackages.calendar ];
        };
        charon-ml = ocamlPackages.buildDunePackage {
          pname = "charon";
          version = "0.1.0";
          buildInputs = with ocamlPackages; [
            ppx_deriving
            visitors
            easy_logging
            zarith
            yojson
            calendar
          ];
          src = ./charon-ml;
          doCheck = true;
        };
      in {
        packages = {
          inherit charon charon-ml;
          default = charon;
        };
        checks = { inherit tests tests-polonius; };
        hydraJobs = { inherit charon tests tests-polonius; };
      });
}
