#!/usr/bin/env bash
# Benchmark charon by measuring instruction counts on a set of crates.
# Requires: perf, jq, and charon in PATH.
#
# Usage: ci-bench.sh <output.json>
set -euo pipefail

output_file="${1:?Usage: ci-bench.sh <output.json>}"

tmpdir=$(mktemp -d)
trap 'rm -rf "$tmpdir"' EXIT

declare -A crates=(
  [SparsePostQuantumRatchet]="https://github.com/signalapp/SparsePostQuantumRatchet"
  [libsignal-crypto]="https://github.com/signalapp/libsignal rust/crypto"
)

for crate_name in "${!crates[@]}"; do
  read -r repo_url subdir <<< "${crates[$crate_name]}"
  crate_dir="$tmpdir/$crate_name"

  echo "::group::$crate_name"

  git clone --depth 1 "$repo_url" "$crate_dir"
  manifest="$crate_dir/${subdir:+$subdir/}Cargo.toml"

  # We run charon twice: once to get everything compiled, and a second time
  # under perf to count instructions spent on the root crate only.
  # perf stat --inherit (the default) counts all child processes,
  # so this captures charon + cargo + charon_driver.
  charon cargo --preset=fast --no-serialize -- --manifest-path "$manifest"
  perf stat -e instructions -x ';' \
    -o "$tmpdir/perf_${crate_name}.txt" \
    -- charon cargo --preset=fast --dest-file "$tmpdir/${crate_name}.llbc" -- --manifest-path "$manifest"

  # perf -x ';' output: <count>;<unit>;<event>;...
  icount=$(grep 'instructions' "$tmpdir/perf_${crate_name}.txt" \
           | head -1 | cut -d';' -f1 | tr -d ' ')
  echo "  $crate_name: $icount instructions"

  jq -n --arg name "$crate_name" --argjson val "$icount" \
    '{"name": $name, "unit": "instructions", "value": $val}' \
    >> "$tmpdir/bench_results.jsonl"

  echo "::endgroup::"
done

jq --slurp . "$tmpdir/bench_results.jsonl" > "$output_file"
echo "Results written to $output_file:"
cat "$output_file"
