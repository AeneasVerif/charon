{
  description = "Charon";

  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    crane.url = "github:ipetkov/crane";
    nixpkgs.follows = "crane/nixpkgs";
    rust-overlay.url = "github:oxalica/rust-overlay";
  };

  outputs = { self, flake-utils, crane, nixpkgs, rust-overlay }:
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
        charon =
          craneLib.buildPackage { src = craneLib.cleanCargoSource ./charon; };
        tests = let
          deps =
            craneLib.buildDepsOnly { src = craneLib.cleanCargoSource ./tests; };
        in pkgs.stdenv.mkDerivation {
          name = "tests";
          src = ./tests;
          nativeBuildInputs = [ pkgs.gnutar pkgs.zstd rustToolchain ];
          configurePhase = ''
            tar -xf ${deps}/target.tar.zst
            mkdir -p $out/llbc
          '';
          buildPhase = ''
            ${charon}/bin/charon --dest $out/llbc --no-code-duplication src/nested_borrows.rs
            ${charon}/bin/charon --dest $out/llbc --no-code-duplication src/loops.rs
            ${charon}/bin/charon --dest $out/llbc --opaque=hashmap_utils src/hashmap_main.rs
          '';
          dontInstall = true;
        };
        tests-nll = let
          deps = craneLib.buildDepsOnly {
            src = craneLib.cleanCargoSource ./tests-nll;
          };
        in pkgs.stdenv.mkDerivation {
          name = "tests-nll";
          src = ./tests-nll;
          nativeBuildInputs = [ pkgs.gnutar pkgs.zstd rustToolchain ];
          configurePhase = ''
            tar -xf ${deps}/target.tar.zst
            mkdir -p $out/llbc
          '';
          buildPhase = ''
            ${charon}/bin/charon --dest $out/llbc --opaque=betree_utils src/betree_main.rs
          '';
          dontInstall = true;
        };
      in {
        packages = {
          inherit charon;
          default = charon;
        };
        hydraJobs = { inherit charon tests tests-nll; };
      });
}
