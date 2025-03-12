#!/usr/bin/env bash
# Lists the workflow runs associated with open PRs and re-runs them all
gh pr list --base main --json isDraft,statusCheckRollup \
    | jq -r '.[]
        | select(.isDraft | not)
        | .statusCheckRollup[].detailsUrl
        | capture("https://github.com/AeneasVerif/charon/actions/runs/(?<run_id>[0-9]+)/job/[0-9]+")
        | .run_id' \
    | sort | uniq \
    | while read run; do gh run rerun "$run"; done
