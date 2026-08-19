{ lib
, charon
, ocaml-ng
, ocamlPackages
, runCommand
, stdenv
}:
let
  # We need both `charon-ml` and the `dune-project` file.
  src = lib.cleanSourceWith {
    src = ./..;
    filter =
      path: type:
      (lib.hasPrefix (toString ../charon-ml) path)
      || (lib.hasPrefix (toString ../dune-project) path);
  };

  charon-name_matcher_parser =
    ocamlPackages.buildDunePackage {
      pname = "name_matcher_parser";
      version = "0.1.0";
      duneVersion = "3";
      inherit src;

      nativeBuildInputs = with ocamlPackages; [
        menhir
      ];
      propagatedBuildInputs = with ocamlPackages; [
        ppx_deriving
        visitors
        zarith
        menhirLib
      ];
    };

  charon-ml-check-fmt = stdenv.mkDerivation {
    name = "charon-ml-check-fmt";
    inherit src;

    buildInputs = [
      ocamlPackages.dune_3
      ocamlPackages.ocaml
      ocaml-ng.ocamlPackages_5_3.ocamlformat_0_27_0
    ];
    buildPhase = ''
      if ! dune build @fmt; then
        echo 'ERROR: Ocaml code is not formatted. Run `make format` to format the project files'.
        exit 1
      fi
    '';
    installPhase = "touch $out";
  };

  mk-charon-ml = doCheck:
    ocamlPackages.buildDunePackage ({
      pname = "charon";
      version = "0.1.0";
      duneVersion = "3";
      inherit src;

      propagatedBuildInputs = with ocamlPackages; [
        core
        ppx_deriving
        visitors
        logs
        zarith
        yojson
        charon-name_matcher_parser
        unionFind
        ocaml-ng.ocamlPackages_4_14.ppx_tools # to view the output of visitor derivation
      ];

      OCAMLPARAM = "_,warn-error=+A"; # Turn all warnings into errors.

      inherit doCheck;
      preBuild = ''
        # This refers to a directory that doesn't exist in the current
        # environment. We don't need dune here because tests can access the
        # files directly, so we remove the dependency clause.
        sed -i 's#(glob_files_rec [^)]*)##' charon-ml/tests/dune
      '';

      passthru = { inherit charon-ml-tests charon-ml-check-fmt; };
    } // lib.optionalAttrs doCheck {
      checkInputs = [ ocamlPackages.re ]; # Used by the tests only.
      CHARON_TESTS_DIR = "${charon}/tests-llbc"; # Tell the tests where to find the llbc files.
      CHARON_BIN = "${charon}/bin/charon";
    });

  charon-ml = mk-charon-ml false;
  charon-ml-tests = mk-charon-ml true;

in
charon-ml
