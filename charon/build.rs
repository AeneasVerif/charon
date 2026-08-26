use std::{env, process::Command};

fn git(args: &[&str]) -> Option<String> {
    let output = Command::new("git").args(args).output().ok()?;
    output
        .status
        .success()
        .then(|| String::from_utf8_lossy(&output.stdout).trim().to_owned())
}

fn main() {
    println!("cargo::rerun-if-env-changed=CHARON_GIT_COMMIT");

    // Re-run when either a detached HEAD or the currently checked-out branch moves.
    for path in [
        git(&["rev-parse", "--git-path", "HEAD"]),
        git(&["symbolic-ref", "-q", "HEAD"])
            .and_then(|reference| git(&["rev-parse", "--git-path", &reference])),
    ]
    .into_iter()
    .flatten()
    {
        println!("cargo::rerun-if-changed={path}");
    }

    // Packaged sources may not include `.git`; packagers can provide the revision explicitly.
    let commit = env::var("CHARON_GIT_COMMIT")
        .ok()
        .or_else(|| git(&["rev-parse", "HEAD"]))
        .unwrap_or_else(|| "unknown".to_owned());
    println!("cargo::rustc-env=CHARON_GIT_COMMIT={commit}");
}
