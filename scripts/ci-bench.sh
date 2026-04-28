#!/usr/bin/env bash
# Benchmark charon by measuring instruction counts on a set of crates.
# Requires: perf, jq, GNU time, and charon in PATH.
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
  echo "::group::$crate_name"

  read -r repo_url subdir <<< "${crates[$crate_name]}"
  crate_dir="$tmpdir/$crate_name"
  llbc_file="$tmpdir/${crate_name}.llbc"
  perf_file="$tmpdir/perf_${crate_name}.txt"
  time_file="$tmpdir/time_${crate_name}.txt"

  git clone --depth 1 "$repo_url" "$crate_dir"
  manifest="$crate_dir/${subdir:+$subdir/}Cargo.toml"

  # We run charon twice: once to get everything compiled, and a second time
  # under perf to count instructions spent on the root crate only.
  charon cargo --preset=fast --no-serialize -- --manifest-path "$manifest"

  # perf stat --inherit (the default) counts all child processes, so this
  # captures charon + cargo + charon_driver. We use GNU time for max RSS.
  command time -v -o "$time_file" \
    perf stat -e instructions -x ';' \
      -o "$perf_file" \
      -- charon cargo --preset=fast --dest-file "$llbc_file" -- --manifest-path "$manifest"

  # perf -x ';' output: <count>;<unit>;<event>;...
  icount=$(grep 'instructions' "$perf_file" \
           | head -1 | cut -d';' -f1 | tr -d ' ')
  # Wall-clock time from GNU time (format: [h:]mm:ss.ss), converted to seconds.
  wall_raw=$(grep 'Elapsed (wall clock)' "$time_file" | grep -oP '[\d:.]+$')
  wall_secs=$(echo "$wall_raw" | awk -F: '{s=$NF; for(i=NF-1;i>=1;i--) s+=$i*60^(NF-i)} END{printf "%.2f",s}')
  # Max RSS in MB (GNU time reports KB).
  max_rss_kb=$(grep 'Maximum resident' "$time_file" | grep -oP '\d+')
  max_rss_mb=$(awk "BEGIN{printf \"%.1f\", $max_rss_kb/1024}")
  # Output file size in MB.
  file_size_bytes=$(stat --printf='%s' "$llbc_file")
  file_size_mb=$(awk "BEGIN{printf \"%.1f\", $file_size_bytes/1048576}")

  echo "  $crate_name: $icount instructions, ${wall_secs}s, ${max_rss_mb} MB RSS, ${file_size_mb} MB output"

  for metric in \
    "instructions $icount" \
    "wall-clock(s) $wall_secs" \
    "max-rss(MB) $max_rss_mb" \
    "output-size(MB) $file_size_mb"; do
    read -r unit val <<< "$metric"
    jq -n --arg name "$crate_name" --arg unit "$unit" --argjson val "$val" \
      '{"name": $name, "unit": $unit, "value": $val}' \
      >> "$tmpdir/bench_results.jsonl"
  done

  echo "::endgroup::"
done

jq --slurp . "$tmpdir/bench_results.jsonl" > "$output_file"
echo "Results written to $output_file:"
cat "$output_file"
