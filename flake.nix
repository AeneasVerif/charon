{
  description = "Charon";

  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    flake-compat.url = "github:nix-community/flake-compat";
    nixpkgs.url = "nixpkgs/nixos-unstable";
    rust-overlay = {
      url = "github:oxalica/rust-overlay";
      inputs.flake-utils.follows = "flake-utils";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    crane = {
      url = "github:ipetkov/crane";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs = { self, flake-utils, nixpkgs, rust-overlay, crane, flake-compat }:
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
            src = pkgs.lib.cleanSourceWith {
              src = ./charon;
              # Don't include the `target` directory in the nix inputs.
              filter = path: type: !pkgs.lib.hasPrefix (toString ./target) path;
            };
            inherit cargoArtifacts;
            # Check the `ui_llbc` files are correct instead of overwriting them.
            cargoTestCommand = "IN_CI=1 cargo test --profile release";
          };
        tests =
          let cargoArtifacts = craneLibNoExt.buildDepsOnly { src = ./tests; };
          in craneLibNoExt.buildPackage {
            name = "tests";
            src = ./tests;
            inherit cargoArtifacts;
            buildPhase = ''
              # Run the tests for Charon
              DEST=$out CARGO_NO_RUST_VERSION=1 CHARON_DRIVER="${charon}/bin/charon-driver" \
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

        # Runs charon on the whole rustc ui test suite. This returns the tests
        # directory with a bunch of `<file>.rs.charon-output` files that store
        # the charon output when it failed. It also adds a `charon-results`
        # file that records `success|expected-failure|failure|panic|timeout`
        # for each file we processed.
        rustc-tests = let
          analyze_test_file = pkgs.writeScript "charon-analyze-test-file" ''
            #!${pkgs.bash}/bin/bash
            FILE="$1"
            echo -n "$FILE: "

            ${pkgs.coreutils}/bin/timeout 5s ${charon}/bin/charon-driver rustc "$FILE" -- --no-serialize > "$FILE.charon-output" 2>&1
            status=$?
            if [ $status -eq 124 ]; then
                result=timeout
            elif [ $status -eq 101 ]; then
                result=panic
            elif [ $status -eq 0 ]; then
                result=success
                # Only keep the informative outputs.
                rm "$FILE.charon-output"
            elif [ -f ${"$"}{FILE%.rs}.stderr ]; then
                result=expected-failure
                # Only keep the informative outputs.
                rm "$FILE.charon-output"
            else
                result=failure
            fi
            echo $result
          '';
          run_ui_tests = pkgs.writeScript "charon-analyze-test-file" ''
            PARALLEL="${pkgs.parallel}/bin/parallel"
            PV="${pkgs.pv}/bin/pv"
            FD="${pkgs.fd}/bin/fd"

            SIZE="$($FD -e rs | wc -l)"
            echo "Running $SIZE tests..."
            $FD -e rs \
                | $PARALLEL ${analyze_test_file} \
                | $PV -l -s "$SIZE" \
                > charon-results
          '';
        in pkgs.runCommand "charon-rustc-tests" {
          src = pkgs.fetchFromGitHub {
            owner = "rust-lang";
            repo = "rust";
            # The commit that corresponds to our nightly-2023-06-02 pin.
            rev = "d59363ad0b6391b7fc5bbb02c9ccf9300eef3753";
            sha256 = "sha256-fpPMSzKc/Dd1nXAX7RocM/p22zuFoWtIL6mVw7XTBDo=";
          };
          buildInputs = [ rustToolchainWithExt ];
        } ''
          mkdir $out
          cp -r $src/tests/ui/* $out
          chmod -R u+w $out
          cd $out
          ${run_ui_tests}
        '';

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
          inherit charon charon-ml rustc-tests;
          default = charon;
        };
        devShells.default = pkgs.mkShell {
          # To prevent Charon to add the `+nightly` identifier
          # which works only with `rustup`.
          CARGO_NO_RUST_VERSION = 1;

          packages = [
            pkgs.ocamlPackages.ocaml
            pkgs.ocamlPackages.ocamlformat
            pkgs.ocamlPackages.menhir
            pkgs.ocamlPackages.odoc
          ];

          inputsFrom = [
            self.packages.${system}.charon
            self.packages.${system}.charon-ml
          ];
        };
        checks = { inherit tests tests-polonius charon-ml-tests; };
      });
}
