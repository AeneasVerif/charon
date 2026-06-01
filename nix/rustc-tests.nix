{ charon
, fd
, fetchFromGitHub
, parallel
, python3
, pv
, runCommand
, rustToolchain
}:

let
  # The rustc commit we use to get the tests. We should update it every now and
  # then to match the version of rustc we're using.
  tests_commit = "14210df0e27ccd7d9e6a05b8085cbd438e4bbc65";
  tests_hash = "sha256-LMTeJ85z9ZGuQThD4922ZvAc97CV2ZGY1/c18RvodWg=";

  rustc-test-suite = fetchFromGitHub {
    owner = "rust-lang";
    repo = "rust";
    rev = tests_commit;
    sha256 = tests_hash;
  };

  rustc-tests-harness = ./rustc-tests.py;

  # Runs charon on the whole rustc ui test suite. This returns the tests
  # directory with a bunch of `<file>.rs[.<revision>].charon-output` and
  # `<file>.rs[.<revision>].charon-status` files.
  run_rustc_tests = runCommand "charon-run-rustc-tests"
    {
      src = rustc-test-suite;
      buildInputs = [ rustToolchain parallel pv fd ];
    } ''
    mkdir $out
    cp -r $src/tests/ui/* $out
    chmod -R u+w $out
    cd $out

    SIZE="$(fd -e rs | wc -l)"
    echo "Running $SIZE tests..."
    fd -e rs \
        | parallel ${python3}/bin/python3 ${rustc-tests-harness} run --charon ${charon}/bin/charon \
        | pv -l -s "$SIZE"
  '';

  # Adds a `charon-results` file that records
  # `success|expected-failure|failure|panic|timeout` for each file we
  # processed.
  analyze_test_outputs = runCommand "charon-analyze-test-outputs"
    {
      src = run_rustc_tests;
      buildInputs = [ parallel pv fd ];
    } ''
    mkdir $out
    chmod -R u+w $out
    cd $out
    ln -s $src test-results

    SIZE="$(fd --follow -e rs | wc -l)"
    echo "Running $SIZE tests..."
    fd --follow -e rs \
        | parallel ${python3}/bin/python3 ${rustc-tests-harness} analyze \
        | pv -l -s "$SIZE" \
        > charon-results

    cat charon-results | cut -d':' -f 2- | sort | uniq -c > charon-summary

    function gather_errors() {
        expected="$1"
        got="$2"
        echo '<details><summary>'"❌ expected: $expected; got: $got"'</summary>'
        grep "expected: $expected.*got: $got" charon-results | cut -d':' -f1 | while read f; do
            echo
            echo '`'"$f"'`:'
            head -3 "$f.charon-output"
        done || true
        echo
        echo '</details>'
    }
    gather_errors "success" "failure in rustc" >> charon-grouped-results
    gather_errors "success" "internal compiler error" >> charon-grouped-results
    gather_errors "success" "panic" >> charon-grouped-results
  '';

in
{
  inherit rustc-test-suite;
  rustc-tests = analyze_test_outputs;
}
