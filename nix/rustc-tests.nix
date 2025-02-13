{ bash
, charon
, coreutils
, fd
, fetchFromGitHub
, lib
, parallel
, pv
, runCommand
, rustToolchain
, writeScript
}:

let
  # The rustc commit we use to get the tests. We should update it every now and
  # then to match the version of rustc we're using.
  tests_commit = "65ea825f4021eaf77f1b25139969712d65b435a4";
  tests_hash = "sha256-0dsWuGcWjQpj/N4iG6clCzM8kjrDjE+dQfyL3iuBGiY=";

  rustc-test-suite = fetchFromGitHub {
    owner = "rust-lang";
    repo = "rust";
    rev = tests_commit;
    sha256 = tests_hash;
  };

  # The commit that corresponds to our nightly pin, for when we want to update the pinned commit.
  toolchain_commit = runCommand "get-rustc-commit" { } ''
    # This is sad but I don't know a better way.
    cat ${rustToolchain}/share/doc/rust/html/version_info.html \
      | grep 'github.com' \
      | sed 's#.*"https://github.com/rust-lang/rust/commit/\([^"]*\)".*#\1#' \
      > $out
  '';

  analyze_test_file = writeScript "charon-analyze-test-file" ''
    #!${bash}/bin/bash
    FILE="$1"
    echo -n "$FILE: "

    has_magic_comment() {
      # Checks for `// magic-comment` and `//@ magic-comment` instructions in files.
      grep -q "^// \?@\? \?$1:" "$2"
    }

    ${coreutils}/bin/timeout 10s ${charon}/bin/charon --no-cargo --input "$FILE" --dest-file "$FILE.llbc" > "$FILE.charon-output" 2>&1
    status=$?
    if has_magic_comment 'aux-build' "$FILE" \
      || has_magic_comment 'compile-flags' "$FILE" \
      || has_magic_comment 'revisions' "$FILE" \
      || has_magic_comment 'known-bug' "$FILE" \
      || has_magic_comment 'edition' "$FILE"; then
        # We can't handle these for now
        result="⊘ unsupported-build-settings"
    elif [ $status -eq 124 ]; then
        result="❌ timeout"
    elif [ $status -eq 101 ]; then
        result="❌ charon-panic"
    elif [ -f ${"$"}{FILE%.rs}.stderr ]; then
        # This is a test that should fail
        if [ $status -eq 0 ]; then
            result="❌ success-when-failure-expected"
        else
            result="✅ expected-failure"
        fi
    elif [ $status -eq 0 ]; then
        if [ -e "$FILE.llbc" ]; then
            result="✅ expected-success"
        else
            result="❌ success-but-no-llbc-output"
        fi
    else
        if [ -e "$FILE.llbc" ]; then
            result="❌ failure-when-success-expected (with llbc output)"
        else
            result="❌ failure-when-success-expected (without llbc output)"
        fi
    fi

    echo "$result"
  '';
  run_ui_tests = writeScript "charon-analyze-test-file" ''
    PARALLEL="${parallel}/bin/parallel"
    PV="${pv}/bin/pv"
    FD="${fd}/bin/fd"

    SIZE="$($FD -e rs | wc -l)"
    echo "Running $SIZE tests..."
    $FD -e rs \
        | $PARALLEL ${analyze_test_file} \
        | $PV -l -s "$SIZE" \
        > charon-results

    cat charon-results | cut -d':' -f 2 | sort | uniq -c > charon-summary
  '';

  # Runs charon on the whole rustc ui test suite. This returns the tests
  # directory with a bunch of `<file>.rs.charon-output` files that store
  # the charon output when it failed. It also adds a `charon-results`
  # file that records `success|expected-failure|failure|panic|timeout`
  # for each file we processed.
  rustc-tests = runCommand "charon-rustc-tests"
    {
      src = rustc-test-suite;
      buildInputs = [ rustToolchain ];
    } ''
    mkdir $out
    cp -r $src/tests/ui/* $out
    chmod -R u+w $out
    cd $out
    ${run_ui_tests}
  '';

in
{
  inherit toolchain_commit rustc-test-suite rustc-tests;
}
