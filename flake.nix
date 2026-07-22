{
  description = "Charon";

  inputs = {
    flake-compat.url = "github:edolstra/flake-compat"; # For ./shell.nix
    flake-utils.url = "github:numtide/flake-utils";
    nixpkgs.url = "nixpkgs/nixos-unstable";
    rust-overlay = {
      # We pin a specific commit because we require a relatively recent version
      # and flake dependents don't look at our flake.lock.
      url = "github:oxalica/rust-overlay/51390d0bfca0a68a8c337d215a4bbeddc2ca616e";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    crane.url = "github:ipetkov/crane";
    jail-nix.url = "sourcehut:~alexdavid/jail.nix";
  };

  outputs = { self, flake-utils, nixpkgs, rust-overlay, crane, jail-nix, ... }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {
          inherit system;
          overlays = [ (import rust-overlay) ];
        };
        inherit (pkgs) lib stdenv makeWrapper bintools;

        rustToolchain = pkgs.rust-bin.fromRustupToolchainFile ./rust-toolchain;
        craneLib = (crane.mkLib pkgs).overrideToolchain rustToolchain;
        ocamlformat = pkgs.ocamlPackages.ocamlformat_0_27_0;

        # Glibc version that the Linux release binaries are lowered to after building
        # to ensure compatibility with older Linux systems
        releaseGlibcVersion = "2.35";
        polyfill-glibc = pkgs.callPackage ./nix/polyfill-glibc.nix { };

        fullMirSysroots = pkgs.callPackage ./nix/full-mir-sysroots.nix { inherit rustToolchain; };
        charon-unwrapped = pkgs.callPackage ./nix/charon.nix {
          inherit craneLib;
          miriSysroots = fullMirSysroots;
        };
        charon = pkgs.runCommand "charon"
          {
            nativeBuildInputs = [ makeWrapper ]
              # For `install_name_tool`.
              ++ lib.optionals stdenv.isDarwin [ bintools ];
            passthru = charon-unwrapped.passthru;
          }
          (''
            cp -r ${charon-unwrapped} $out
            chmod -R u+w $out

            # Make sure the toolchain is in $PATH so that `cargo` can work
            # properly. On mac we also have to tell `charon-driver` where to
            # find the rustc_driver dynamic library; this is done automatically
            # on linux.
            wrapProgram $out/bin/charon \
              --set CHARON_TOOLCHAIN_IS_IN_PATH 1 \
              --set CHARON_MIRI_SYSROOTS "${fullMirSysroots}" \
              --prefix LD_LIBRARY_PATH : "${lib.makeLibraryPath [ rustToolchain ]}" \
              --prefix PATH : "${lib.makeBinPath [ rustToolchain ]}"
          ''
          + (lib.optionalString stdenv.isDarwin ''
            # Ensures `charon-driver` finds the dylibs correctly.
            install_name_tool -add_rpath "${rustToolchain}/lib" "$out/bin/charon-driver"
          ''));
        charon-portable = pkgs.runCommand "charon-portable" { } (''
          mkdir -p $out/bin
          cp ${charon-unwrapped}/bin/charon $out/bin/charon
          cp ${charon-unwrapped}/bin/charon-driver $out/bin/charon-driver
        ''
        + (lib.optionalString stdenv.isLinux ''
          for f in $out/bin/*; do
            chmod +w $f
            ${pkgs.patchelf}/bin/patchelf --set-interpreter ${
              {
                x86_64-linux = "/lib64/ld-linux-x86-64.so.2";
                aarch64-linux = "/lib/ld-linux-aarch64.so.1";
              }.${system}
            } $f || true
            ${pkgs.patchelf}/bin/patchelf --remove-rpath $f || true
          done
        ''));
        charon-release = pkgs.runCommand "charon-release"
          {
            nativeBuildInputs = lib.optionals stdenv.isLinux [ pkgs.binutils ];
          }
          (''
          mkdir $out
          cd $out
          cp ${charon-portable}/bin/charon ${charon-portable}/bin/charon-driver .
          cp ${./charon/rust-toolchain} rust-toolchain
        ''
        # Lower the glibc version the binaries require, so the release runs on
        # any host with glibc >= ${releaseGlibcVersion} regardless of the
        # (newer) glibc it was built against.
        #
        # We need to use `--clear-symbol-version` for `pidfd_getpid` and `pidfd_spawnp` because
        # `polyfill-glibc` has no polyfill for them and refuses to process the binary when they
        # carry a symbol version above ${releaseGlibcVersion}. Glibc versions before 2.39 did not
        # have these symbols at all, but Rust only imports them weakly and will fall back to a
        # different mechanism when these symbols are not available.
        + lib.optionalString stdenv.isLinux ''
          chmod +w charon charon-driver
          for f in charon charon-driver; do
            ${polyfill-glibc}/bin/polyfill-glibc \
              --clear-symbol-version=pidfd_getpid,pidfd_spawnp \
              --target-glibc=${releaseGlibcVersion} "$f"
          done

          # Sanity-check that the release binaries don't require a glibc newer
          # than `releaseGlibcVersion`.
          max="$(objdump -T charon charon-driver \
            | grep -oE 'GLIBC_[0-9]+(\.[0-9]+)+' | sed 's/GLIBC_//' | sort -V | tail -1)"
          echo "Highest required glibc symbol version: ''${max:-none}"
          if [ -n "$max" ] && [ "$(printf '%s\n${releaseGlibcVersion}\n' "$max" | sort -V | tail -1)" != "${releaseGlibcVersion}" ]; then
            echo "ERROR: charon-release requires glibc $max > ${releaseGlibcVersion}." >&2
            exit 1
          fi
        '');
        charon-ml = pkgs.callPackage ./nix/charon-ml.nix { inherit charon; };

        # Check rust files are correctly formatted.
        charon-check-fmt = charon.passthru.check-fmt;
        # Check rust files are clippy-clean.
        charon-check-clippy = charon.passthru.check-clippy;
        # Check that the crate builds with the "rustc" feature off.
        charon-check-no-rustc = charon.passthru.check-no-rustc;
        # Check ocaml files are correctly formatted.
        charon-ml-check-fmt = charon-ml.charon-ml-check-fmt;
        # Run ocaml tests
        charon-ml-tests = charon-ml.charon-ml-tests;

        # Runs charon on the whole rustc ui test suite.
        rustc-tests = pkgs.callPackage ./nix/rustc-tests.nix { inherit charon rustToolchain; };

        zulip_bot = pkgs.callPackage ./nix/zulip_bot.nix {
          inherit charon pkgs;
          jailNixLib = jail-nix.lib;
        };

        # Check that the generated ocaml files match what is committed to the repo.
        check-generated-ml = pkgs.runCommand "check-generated-ml" { } ''
          mkdir generated
          cp ${charon}/generated-ml/* generated
          chmod u+w generated/*
          cp ${./charon-ml/.ocamlformat} .ocamlformat
          ${ocamlformat}/bin/ocamlformat --inplace --enable-outside-detected-project generated/*.ml

          mkdir committed
          cp ${./charon-ml/src/generated}/*.ml committed

          if diff -rq committed generated; then
            echo "Ok: the regenerated ocaml files are the same as the checked out files"
          else
            echo "Error: the regenerated ocaml files differ from the checked out files"
            diff -ru committed generated
            exit 1
          fi
          touch $out
        '';

        # Test usage of charon via nix, to ensure the paths are set up correctly.
        test-charon-via-nix = pkgs.runCommand "test-charon-via-nix" { } ''
          echo "fn main() {}" > foo.rs
          ${charon}/bin/charon rustc --no-serialize --print-llbc -- foo.rs > $out
        '';

        # A utility that extracts the llbc of a crate using charon. This uses
        # `crane` to handle dependencies and toolchain management.
        extractCrateWithCharon = { name, src, charonArgs ? "", cargoArgs ? "", craneExtraArgs ? { } }:
          craneLib.buildPackage ({
            name = "${name}.llbc";
            src = pkgs.lib.cleanSourceWith {
              inherit src;
              filter = path: type: (craneLib.filterCargoSources path type);
            };
            cargoArtifacts = craneLib.buildDepsOnly { inherit src; };
            buildPhase = ''
              ${charon}/bin/charon cargo ${charonArgs} --dest-file $out -- ${cargoArgs}
            '';
            dontInstall = true;
            doCheck = false;
          } // craneExtraArgs);
      in
      {
        packages = {
          inherit charon charon-unwrapped charon-portable charon-release charon-ml polyfill-glibc rustToolchain zulip_bot;
          charon-full-mir-sysroots = fullMirSysroots;
          inherit (rustc-tests) rustc-tests;
          default = charon;
        };
        devShells.default = pkgs.mkShell {
          # Tell charon that the right toolchain is in PATH. It is added to PATH by the `charon` in `inputsFrom`.
          CHARON_TOOLCHAIN_IS_IN_PATH = 1;
          # To run `cargo outdated` and `cargo udeps`
          LD_LIBRARY_PATH =
            pkgs.lib.makeLibraryPath [ pkgs.stdenv.cc.cc.lib pkgs.openssl pkgs.curl pkgs.zlib ];
          OCAMLRUNPARAM = "b"; # Get backtrace on ocaml exception

          packages = [
            pkgs.ocamlPackages.ocaml
            ocamlformat
            pkgs.ocamlPackages.menhir
            pkgs.ocamlPackages.odoc
            # ocamllsp's version must match the ocaml version used, hence we
            # can't an use externally-provided ocamllsp.
            pkgs.ocamlPackages.ocaml-lsp
          ];

          nativeBuildInputs = [
            pkgs.pkg-config
            pkgs.rlwrap
          ];

          # To compile some rust crates that need system dependencies.
          buildInputs = [
            pkgs.openssl
            pkgs.glibc.out
            pkgs.glibc.static
          ] ++ lib.optionals stdenv.isLinux [
            pkgs.glibc.bin
          ];

          inputsFrom = [
            self.packages.${system}.charon
            self.packages.${system}.charon-ml
          ];
        };
        devShells.ci = pkgs.mkShell {
          packages = [
            pkgs.gh
            pkgs.jq
            pkgs.python3
            pkgs.toml2json
          ];
        };
        devShells.bench = pkgs.mkShell {
          buildInputs = [
            pkgs.openssl
            pkgs.glibc.out
            pkgs.glibc.static
            pkgs.protobuf
            pkgs.jq
            pkgs.linuxPackages.perf
            pkgs.time
            self.packages.${system}.charon
          ];
          # Include the rust toolchain
          inputsFrom = [
            self.packages.${system}.charon
          ];
        };
        checks = {
          default = charon-ml-tests;
          inherit charon-ml-tests charon-check-fmt charon-check-no-rustc
            charon-ml-check-fmt check-generated-ml test-charon-via-nix
            charon-check-clippy;
        };

        # Export this function so that users of charon can use it in nix. This
        # fits in none of the standard flake output categories hace why it is
        # exported directly like that.
        inherit extractCrateWithCharon;
      });
}
