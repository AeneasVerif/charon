#!/usr/bin/env python
import re

project_refs = {
    "aeneas": "main",
    "eurydice": "main",
    "libcrux": "main",
}

# TODO: if $CI_EVENT == "pull_request" or "merge_group"
# TODO: gh pr view "$PR_NUMBER" --json body
description = """
"""


for line in description.splitlines():
    if r := re.match("^ci: *([a-z]*) ([0-9]*)", line):
        project = r.group(1)
        pr = r.group(2)
        project_refs[project] = f"pull/{pr}/head"

# Emit lines that will be piped to `$GITHUB_OUTPUT`
for project, ref in project_refs.items():
    print(f"{project}={ref}")
