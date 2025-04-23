#!/usr/bin/env python
import re, sys, os, json, subprocess

def eprint(*args):
    print(*args, file=sys.stderr)

DEPENDENT_PROJECTS = ["aeneas", "eurydice", "libcrux"]
# Don't set a default value to libcrux so that by default we reuse the last-known-good
# commit. For aeneas and eurydice by default we want to use the latest commit.
project_refs = {
    "aeneas": "main",
    "eurydice": "main",
}

ci_event = os.environ.get('CI_EVENT')
if ci_event in ["pull_request", "merge_group"]:
    pr_number = os.environ.get('PR_NUMBER')
    if pr_number is None:
        eprint("ERROR: $PR_NUMBER is None")
        sys.exit(1)

    output = subprocess.check_output([
        'gh', 'pr', 'view', pr_number, '--json', 'body'
    ])
    description = json.loads(output)['body']

    eprint(f"Found PR description for PR {pr_number}:")
    eprint(description)

    for line in description.splitlines():
        if line.startswith("ci:"):
            r = re.match("^ci: use https://github.com/[A-Za-z]*/([A-Za-z]*)/pull/([0-9]*)", line)
            if r is None:
                eprint(f"ERROR: could not parse command: `{line}`")
                sys.exit(1)
            project = r.group(1)
            pr = r.group(2)
            project_refs[project] = f"pull/{pr}/head"

# Emit lines that will be piped to `$GITHUB_OUTPUT`
for project, ref in project_refs.items():
    if project not in DEPENDENT_PROJECTS:
        eprint(f"ERROR: repo `{project}` is not a dependent project. Accepted values are:",
               ", ".join(DEPENDENT_PROJECTS))
        sys.exit(1)
    print(f"{project}={ref}")
