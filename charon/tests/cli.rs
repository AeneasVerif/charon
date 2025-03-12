use anyhow::{ensure, Context, Result};
use assert_cmd::prelude::CommandCargoExt;
use itertools::Itertools;
use std::process::Command;

fn charon<T>(args: &[&str], f: impl FnOnce(String) -> Result<T>) -> Result<T> {
    let cmd_str = || {
        std::iter::once("charon")
            .chain(args.iter().copied())
            .join(" ")
    };

    let mut cmd = Command::cargo_bin("charon")?;
    let output = cmd.args(args).output()?;
    let stdout = String::from_utf8(output.stdout).with_context(|| {
        format!(
            "`{}`:\nthe content of stdout is not UTF8 encoded.",
            cmd_str()
        )
    })?;
    let stderr = String::from_utf8(output.stderr).with_context(|| {
        format!(
            "`{}`:\nthe content of stderr is not UTF8 encoded.",
            cmd_str()
        )
    })?;

    let status = output.status;
    ensure!(
        status.success(),
        "Error when executing `{}`:\nstderr={stderr:?}\nstdout={stdout:?}",
        cmd_str()
    );

    f(stdout)
}

#[test]
fn charon_pretty_print() -> Result<()> {
    // charon --rustc-flag=--crate-type=rlib --no-cargo --input tests/ui/arrays.rs
    charon(
        &[
            "--rustc-flag=--crate-type=rlib",
            "--no-cargo",
            "--input",
            "tests/ui/arrays.rs",
        ],
        |_| {
            // arrays.llbc is generated
            let llbc = "arrays.llbc";
            ensure!(std::fs::exists(llbc)?, "{llbc} doesn't exist!");

            charon(&["pretty-print", llbc], |stdout| {
                let search = "pub fn arrays::";
                ensure!(
                    stdout.contains(search),
                    "Output of pretty-printing {llbc} is:\n{stdout:?}\nIt doesn't contain {search:?}."
                );
                Ok(())
            })
        },
    )
}
