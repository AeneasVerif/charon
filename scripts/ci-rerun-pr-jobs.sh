#!/usr/bin/env bash

# `get_run_ids <repo>` lists the workflow runs associated with open PRs on the
# repo.
function get_run_ids() {
    repo="$1"
    gh pr list --repo "$repo" --base main --json isDraft,statusCheckRollup \
        | jq -r '.[]
            | select(.isDraft | not)
            | .statusCheckRollup[]
            | .detailsUrl
            | capture("https://github.com/'"$repo"'/actions/runs/(?<run_id>[0-9]+)/job/(?<job_id>[0-9]+)")
            | .run_id' \
        | sort | uniq
}

# `get_job_ids <repo> <jq filter>` returns the job+run ids of jobs selected by the jq filter.
function get_job_ids() {
    repo="$1"
    filter="$2"
    get_run_ids "$repo" \
        | while read run; do
            gh --repo "$repo" run view "$run" --json jobs \
                | jq '.jobs[]
                        | '"$filter"'
                        | { run_id: '"$run"', job_id: .databaseId }
                    '
        done
}

# `rerun_jobs <repo> <jq filter>` reruns the jobs selected by the jq filter.
function rerun_jobs() {
    repo="$1"
    filter="$2"
    get_job_ids "$repo" "$filter" \
        | jq -r '"\(.run_id) \(.job_id)"' \
        | while read run job; do
            gh --repo "$repo" run rerun "$run" --job "$job"
        done
}

# Rerun all the PR jobs of charon.
get_run_ids "AeneasVerif/charon" \
    | while read run; do gh run rerun "$run"; done

# Rerun the failed charon-pin-is-merged jobs in eurydice and aeneas
rerun_jobs "AeneasVerif/eurydice" 'select(.name == "charon-pin-is-merged" and .conclusion == "failure")'
rerun_jobs "AeneasVerif/aeneas" 'select(.name == "charon-pin-is-merged" and .conclusion == "failure")'
