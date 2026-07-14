# polyfill-glibc (https://github.com/corsix/polyfill-glibc): a post-processing
# tool that rewrites an ELF's glibc symbol-version requirements down to a chosen
# version, so a binary built against a newer glibc runs on older ones.
# Not (yet) packaged in nixpkgs, hence this small derivation.
{ stdenv, fetchFromGitHub, ninja }:

stdenv.mkDerivation {
  pname = "polyfill-glibc";
  version = "0-unstable-2024-10-30";

  src = fetchFromGitHub {
    owner = "corsix";
    repo = "polyfill-glibc";
    rev = "dd59051faaa10ee63c1b96f1b47bf9fcd3770ee2";
    hash = "sha256-Qkzy33dIGnv9BOmRwql+LpYaEukZZIADSux09Fz3h7E=";
  };

  nativeBuildInputs = [ ninja ];

  buildPhase = ''
    runHook preBuild
    ninja polyfill-glibc
    runHook postBuild
  '';

  installPhase = ''
    runHook preInstall
    install -Dm755 polyfill-glibc $out/bin/polyfill-glibc
    runHook postInstall
  '';
}
