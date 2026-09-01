{
  description = "Charon";

  inputs = {
    flake-compat.url = "github:edolstra/flake-compat"; # For ./shell.nix
    flake-utils.url = "github:numtide/flake-utils";
    nixpkgs.url = "nixpkgs/nixos-unstable";
    rust-overlay = {
      # We pin a specific commit because we require a relatively recent version
      # and flake dependents don't look at our flake.lock.
      url = "github:oxalica/rust-overlay/b32685dd7c5a965aa8273adb7ddaf7f5b40d0faa";
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
        inherit (pkgs) lib stdenv makeWrapper;

        rustToolchain = pkgs.rust-bin.fromRustupToolchainFile ./rust-toolchain;
        craneLib = (crane.mkLib pkgs).overrideToolchain rustToolchain;

        # nixpkgs marks ocamlformat broken for OCaml 5.4, so build it with 5.3 instead
        ocamlformat = pkgs.ocaml-ng.ocamlPackages_5_3.ocamlformat_0_27_0;

        # Glibc version that the Linux release binaries are lowered to after building
        # to ensure compatibility with older Linux systems
        releaseGlibcVersion = "2.35";
        polyfill-glibc = pkgs.callPackage ./nix/polyfill-glibc.nix { };

        fullMirSysroots = pkgs.callPackage ./nix/full-mir-sysroots.nix { inherit rustToolchain; };
        charon-unwrapped = pkgs.callPackage ./nix/charon.nix {
          inherit craneLib;
          charonCommit = self.rev or (lib.removeSuffix "-dirty" (self.dirtyRev or "unknown"));
          miriSysroots = fullMirSysroots;
        };
        charon = pkgs.runCommand "charon"
          {
            nativeBuildInputs = [ makeWrapper ]
              # For `install_name_tool`.
              ++ lib.optionals stdenv.isDarwin [ pkgs.darwin.binutils-unwrapped ];
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
        charon-portable = pkgs.runCommand "charon-portable"
          {
            # For `otool` and `install_name_tool`.
            nativeBuildInputs = lib.optionals stdenv.isDarwin [ pkgs.darwin.binutils-unwrapped ];
          }
          (''
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
        '')
        # The macOS equivalent of the `patchelf` pass above: a nix-built Mach-O
        # binary records absolute `/nix/store` paths for its dependencies, so it
        # dies with `Library not loaded: /nix/store/...` on a machine without a
        # nix store. Rewrite every such reference:
        #  * libraries macOS itself ships are taken from `/usr/lib`;
        #  * rust toolchain libraries (`librustc_driver-*.dylib` & co, which the
        #    driver needs) are referred to by bare filename, so that the loader
        #    finds them via `DYLD_FALLBACK_LIBRARY_PATH`. `rustup run`, which is
        #    how the released `charon` invokes `charon-driver`, sets that to the
        #    `lib` directory of the pinned toolchain. This mirrors what happens
        #    on linux, where we drop the rpath and let `LD_LIBRARY_PATH` do the
        #    same job.
        + (lib.optionalString stdenv.isDarwin ''
          # Provides `signIfRequired`. Note that `runCommand` skips `fixupPhase`,
          # so `autoSignDarwinBinariesHook` would not run here.
          source ${pkgs.darwin.signingUtils}

          # Collect everything we don't know how to make portable, so that one
          # build reports all of it rather than one library at a time.
          unhandled=""
          unhandled_dep() {
            unhandled="$unhandled
            $(basename "$1"): $2"
          }

          for f in $out/bin/*; do
            chmod +w "$f"

            for dep in $(otool -L "$f" | tail -n +2 | awk '{ print $1 }'); do
              leaf="$(basename "$dep")"
              case "$dep" in
                ${rustToolchain}/lib/*)
                  install_name_tool -change "$dep" "$leaf" "$f"
                  ;;
                @rpath/*)
                  # Rust records its own dylibs as `@rpath/lib<foo>.dylib`, and
                  # the rpaths that resolve them are removed below, so these have
                  # to be rewritten as well.
                  if [ -e "${rustToolchain}/lib/$leaf" ]; then
                    install_name_tool -change "$dep" "$leaf" "$f"
                  else
                    unhandled_dep "$f" "$dep"
                  fi
                  ;;
                /nix/store/*)
                  # Take the copy macOS itself ships.
                  case "$leaf" in
                    libSystem.B.dylib)  sys_lib=/usr/lib/libSystem.B.dylib ;;
                    libcharset.1.dylib) sys_lib=/usr/lib/libcharset.1.dylib ;;
                    libiconv.2.dylib)   sys_lib=/usr/lib/libiconv.2.dylib ;;
                    libobjc.A.dylib)    sys_lib=/usr/lib/libobjc.A.dylib ;;
                    libresolv.9.dylib)  sys_lib=/usr/lib/libresolv.9.dylib ;;
                    libz.dylib | libz.1.dylib) sys_lib=/usr/lib/libz.1.dylib ;;
                    *) unhandled_dep "$f" "$dep"; continue ;;
                  esac
                  install_name_tool -change "$dep" "$sys_lib" "$f"
                  ;;
              esac
            done

            # Drop rpaths pointing into the nix store: they'd be dangling, and
            # any `@rpath/` dependency that still needs them was rewritten above.
            for rpath in $(otool -l "$f" | awk '$1 == "path" { print $2 }'); do
              case "$rpath" in
                /nix/store/*) install_name_tool -delete_rpath "$rpath" "$f" ;;
              esac
            done

            # Editing a Mach-O invalidates its (ad-hoc) code signature, and
            # aarch64-darwin refuses to run an incorrectly signed binary.
            signIfRequired "$f"
          done

          if [ -n "$unhandled" ]; then
            echo "ERROR: the release depends on libraries that won't resolve on a machine" >&2
            echo "that has no nix store:$unhandled" >&2
            echo "If macOS ships one of them in /usr/lib, map it to the system copy in" >&2
            echo "the \`case\` in flake.nix; otherwise it has to be shipped next to the" >&2
            echo "binaries." >&2
            exit 1
          fi
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
        ocamlPackages = pkgs.ocamlPackages.overrideScope (_: prev: {
          visitors = (prev.visitors.override { version = "20260520"; }).overrideAttrs (_: {
            src = pkgs.fetchFromGitLab {
              owner = "fpottier";
              repo = "visitors";
              tag = "20260520";
              domain = "gitlab.inria.fr";
              hash = "sha256-QR/kxwojyFOFLeu1JKjBfgmq2xaGZHq8hB1YwVpRVYI=";
            };
          });
        });

        charon-ml = pkgs.callPackage ./nix/charon-ml.nix { inherit charon ocamlPackages; };

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
        check-generated-asts = pkgs.runCommand "check-generated-asts" { } ''
          mkdir generated
          cp ${charon}/generated-asts/* generated
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
            charon-ml-check-fmt check-generated-asts test-charon-via-nix
            charon-check-clippy;
        };

        # Export this function so that users of charon can use it in nix. This
        # fits in none of the standard flake output categories hace why it is
        # exported directly like that.
        inherit extractCrateWithCharon;
      });
}
