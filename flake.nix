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

        # Small issue here:
        # =================
        # We need extensions to build Charon.
        # However, the dependencies don't build if we use extensions.
        #
        # More precisely, `petgraph` doesn't build because for some reason,
        # when building the dependencies in the Nix derivation, Rustc builds
        # it while considering there is no std library available.
        # As a consequence, in `indexmap` (used by `petgraph`), Rustc uses this
        # definition of `IndexMap` (notice the absence of default value for `S`):
        # [https://github.com/bluss/indexmap/blob/eedabaca9f84e520eab01325b305c08f3773e66c/src/map.rs#L82]
        # while it should use this one:
        # [https://github.com/bluss/indexmap/blob/eedabaca9f84e520eab01325b305c08f3773e66c/src/map.rs#L77]
        #
        # We solve the issue by using extensions only to build Charon (and
        # in particular, not its dependencies).
        rustToolchainWithExt =
          pkgs.rust-bin.fromRustupToolchainFile ./rust-toolchain.template;
        rustToolchainNoExt =
          rustToolchainWithExt.override { extensions = [ ]; };
        craneLibWithExt =
          (crane.mkLib pkgs).overrideToolchain rustToolchainWithExt;
        craneLibNoExt = (crane.mkLib pkgs).overrideToolchain rustToolchainNoExt;
        charon =
          let cargoArtifacts = craneLibWithExt.buildDepsOnly { src = ./charon; };
          in craneLibWithExt.buildPackage {
            src = ./charon;
            inherit cargoArtifacts;
          };
        tests =
          let cargoArtifacts = craneLibNoExt.buildDepsOnly { src = ./tests; };
          in craneLibNoExt.buildPackage {
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
          cargoArtifacts =
            craneLibNoExt.buildDepsOnly { src = ./tests-polonius; };
        in craneLibNoExt.buildPackage {
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
        charon-name_matcher_parser =
          ocamlPackages.buildDunePackage {
            pname = "name_matcher_parser";
            version = "0.1.0";
            duneVersion = "3";
            nativeBuildInputs = with ocamlPackages; [
              menhir
            ];
            propagatedBuildInputs = with ocamlPackages; [
              ppx_deriving
              visitors
              zarith
              menhirLib
            ];
            src = ./charon-ml;
          };
        mk-charon-ml = doCheck:
          ocamlPackages.buildDunePackage {
            pname = "charon";
            version = "0.1.0";
            duneVersion = "3";
            preCheck = if doCheck then ''
              mkdir -p tests/serialized
              cp ${tests}/llbc/* tests/serialized
              cp ${tests-polonius}/llbc/* tests/serialized
            '' else
              "";
            propagatedBuildInputs = with ocamlPackages; [
              ppx_deriving
              visitors
              easy_logging
              zarith
              yojson
              calendar
              charon-name_matcher_parser
            ];
            src = ./charon-ml;
            inherit doCheck;
          };
        charon-ml = mk-charon-ml false;
        charon-ml-tests = mk-charon-ml true;
      in {
        packages = {
          inherit charon charon-ml;
          default = charon;
        };
        checks = { inherit tests tests-polonius charon-ml-tests; };
      });
}
