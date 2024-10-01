{
  description = "Charon";

  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    flake-compat.url = "github:nix-community/flake-compat";
    nixpkgs.url = "nixpkgs/nixos-unstable";
    rust-overlay = {
      url = "github:oxalica/rust-overlay";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    crane.url = "github:ipetkov/crane";
  };

  outputs = { self, flake-utils, nixpkgs, rust-overlay, crane, flake-compat }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {
          inherit system;
          overlays = [ (import rust-overlay) ];
        };

        rustToolchain = pkgs.rust-bin.fromRustupToolchainFile ./rust-toolchain;
        craneLib = (crane.mkLib pkgs).overrideToolchain rustToolchain;

        charon = pkgs.callPackage ./nix/charon.nix { inherit craneLib rustToolchain; };

        # Check rust files are correctly formatted.
        charon-check-fmt = charon.passthru.check-fmt;

        # A utility that extracts the llbc of a crate using charon. This uses
        # `crane` to handle dependencies and toolchain management.
        extractCrateWithCharon = { name, src, charonFlags ? "", craneExtraArgs ? { } }:
          craneLib.buildPackage ({
            inherit name;
            src = pkgs.lib.cleanSourceWith {
              inherit src;
              filter = path: type: (craneLib.filterCargoSources path type);
            };
            cargoArtifacts = craneLib.buildDepsOnly { inherit src; };
            buildPhase = ''
              ${charon}/bin/charon ${charonFlags} --dest $out/llbc
            '';
            dontInstall = true;
          } // craneExtraArgs);

        # Runs charon on the whole rustc ui test suite.
        rustc-tests = pkgs.callPackage ./nix/rustc-tests.nix { inherit charon rustToolchain; };

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
            OCAMLPARAM = "_,warn-error=+A"; # Turn all warnings into errors.
            preCheck =
              if doCheck then ''
                mkdir -p tests/serialized
                cp ${charon}/tests-llbc/* tests/serialized
              '' else
                "";
            propagatedBuildInputs = with ocamlPackages; [
              core
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

        charon-ml-check-fmt = pkgs.stdenv.mkDerivation {
          name = "charon-ml-check-fmt";
          src = ./charon-ml;
          buildInputs = [
            ocamlPackages.dune_3
            ocamlPackages.ocaml
            ocamlPackages.ocamlformat
          ];
          buildPhase = ''
            if ! dune build @fmt; then
              echo 'ERROR: Ocaml code is not formatted. Run `make format` to format the project files'.
              exit 1
            fi
          '';
          installPhase = "touch $out";
        };

        # Check that the generated ocaml files match what is committed to the repo.
        check-generated-ml = pkgs.runCommand "check-generated-ml" { } ''
          mkdir generated
          cp ${charon}/generated-ml/* generated
          chmod u+w generated/*
          ${pkgs.ocamlPackages.ocamlformat}/bin/ocamlformat --doc-comments=before --exp-grouping=preserve --inplace --enable-outside-detected-project generated/*.ml

          mkdir committed
          cp ${./charon-ml/src}/GAst.ml committed
          cp ${./charon-ml/src}/LlbcAst.ml committed
          cp ${./charon-ml/src}/UllbcAst.ml committed
          cp ${./charon-ml/src}/Expressions.ml committed
          cp ${./charon-ml/src}/Meta.ml committed
          cp ${./charon-ml/src}/Types.ml committed
          cp ${./charon-ml/src}/Values.ml committed
          cp ${./charon-ml/src}/GAstOfJson.ml committed
          cp ${./charon-ml/src}/LlbcOfJson.ml committed
          cp ${./charon-ml/src}/UllbcOfJson.ml committed

          if diff -rq committed generated; then
            echo "Ok: the regenerated ocaml files are the same as the checked out files"
          else
            echo "Error: the regenerated ocaml files differ from the checked out files"
            diff -ru committed generated
            exit 1
          fi
          touch $out
        '';
      in
      {
        packages = {
          inherit charon charon-ml rustToolchain;
          inherit (rustc-tests) toolchain_commit rustc-tests;
          default = charon;
        };
        devShells.default = pkgs.mkShell {
          # Tell charon that the right toolchain is in PATH. It is added to PATH by the `charon` in `inputsFrom`.
          CHARON_TOOLCHAIN_IS_IN_PATH = 1;
          # To run `cargo outdated` and `cargo udeps`
          LD_LIBRARY_PATH =
            pkgs.lib.makeLibraryPath [ pkgs.stdenv.cc.cc.lib pkgs.openssl pkgs.curl pkgs.zlib ];

          packages = [
            pkgs.ocamlPackages.ocaml
            pkgs.ocamlPackages.ocamlformat
            pkgs.ocamlPackages.menhir
            pkgs.ocamlPackages.odoc
            # ocamllsp's version must match the ocaml version used, hence we
            # can't an use externally-provided ocamllsp.
            pkgs.ocamlPackages.ocaml-lsp
          ];

          nativeBuildInputs = [
            pkgs.pkg-config
          ];

          # To compile some rust crates that need system dependencies.
          buildInputs = [
            pkgs.openssl
            pkgs.glibc.out
            pkgs.glibc.static
          ];

          inputsFrom = [
            self.packages.${system}.charon
            self.packages.${system}.charon-ml
          ];
        };
        checks = { inherit charon-ml-tests charon-check-fmt charon-ml-check-fmt check-generated-ml; };

        # Export this function so that users of charon can use it in nix. This
        # fits in none of the standard flake output categories hace why it is
        # exported directly like that.
        inherit extractCrateWithCharon;
      });
}
