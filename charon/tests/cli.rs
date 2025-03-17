use anyhow::{ensure, Context, Result};
use assert_cmd::prelude::CommandCargoExt;
use itertools::Itertools;
use std::process::Command;

fn charon<T>(args: &[&str], dir: &str, f: impl FnOnce(String, String) -> Result<T>) -> Result<T> {
    let cmd_str = std::iter::once("charon")
        .chain(args.iter().copied())
        .join(" ");

    let mut cmd = Command::cargo_bin("charon")?;
    cmd.current_dir(dir);
    let output = cmd.args(args).output()?;

    let stdout = String::from_utf8(output.stdout)
        .with_context(|| format!("`{cmd_str}`:\nthe content of stdout is not UTF8 encoded."))?;
    let stderr = String::from_utf8(output.stderr)
        .with_context(|| format!("`{cmd_str}`:\nthe content of stderr is not UTF8 encoded."))?;

    let status = output.status;
    ensure!(
        status.success(),
        "Error when executing `{cmd_str}`:\nstderr={stderr:?}\nstdout={stdout:?}",
    );

    f(stdout, cmd_str)
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
        ".",
        |_, _| {
            // arrays.llbc is generated
            let llbc = "arrays.llbc";
            ensure!(std::fs::exists(llbc)?, "{llbc} doesn't exist!");

            charon(&["pretty-print", llbc], ".", |stdout, _| {
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

#[test]
fn charon_cargo_p_crate2() -> Result<()> {
    charon(
        &["cargo", "--print-llbc", "--", "-p", "crate2", "--quiet"],
        "tests/cargo/workspace",
        |stdout, cmd| {
            let search = "pub fn crate2::";
            ensure!(
                stdout.contains(search),
                "Output of `{cmd}` is:\n{stdout:?}\nIt doesn't contain {search:?}."
            );
            Ok(())
        },
    )
}

#[test]
fn charon_cargo_features() -> Result<()> {
    let dir = "tests/cargo/dependencies";
    let main = "fn test_cargo_dependencies::main";
    let take_mut = "pub fn take_mut::take";

    charon(
        &["cargo", "--print-llbc", "--", "-F", "test_feature"],
        dir,
        |stdout, cmd| {
            ensure!(
                stdout.contains(main),
                "Output of `{cmd}` is:\n{stdout:?}\nIt doesn't contain {main:?}."
            );
            ensure!(
                stdout.contains(take_mut),
                "Output of `{cmd}` is:\n{stdout:?}\nIt doesn't contain {take_mut:?}."
            );
            Ok(())
        },
    )?;

    charon(&["cargo", "--print-llbc"], dir, |stdout, cmd| {
        ensure!(
            stdout.contains(main),
            "Output of `{cmd}` is:\n{stdout:?}\nIt doesn't contain {main:?}."
        );

        let count_fn = stdout.matches("fn").count();
        ensure!(
            count_fn == 1,
            "Output of `{cmd}` is:\n{stdout:?}\nThe count of `fn` should only be one."
        );

        ensure!(
            !stdout.contains(take_mut),
            "Output of `{cmd}` is:\n{stdout:?}\nIt shouldn't contain {take_mut:?}."
        );
        Ok(())
    })
}

fn rustup_install_target(target: &str) -> Result<()> {
    // e.g. rustup target add riscv64gc-unknown-none-elf
    let mut cmd = Command::new("rustup");
    let output = cmd.args(["target", "add", target]).output()?;
    ensure!(
        output.status.success(),
        "`rustup target add {target}` failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    Ok(())
}

#[test]
#[ignore = "Network is inaccessible in nix"]
fn charon_cargo_target() -> Result<()> {
    let target = "riscv64gc-unknown-none-elf";
    rustup_install_target(target)?;

    let dir = "tests/cargo/multi-targets";
    let fn_ = "pub fn multi_targets::";

    #[cfg(target_family = "unix")]
    charon(&["cargo", "--print-llbc"], dir, |stdout, cmd| {
        let main = "pub fn multi_targets::on_unix";
        ensure!(
            stdout.contains(main),
            "Output of `{cmd}` is:\n{stdout:?}\nIt doesn't contain {main:?}."
        );

        let count_fn = stdout.matches(fn_).count();
        ensure!(
            count_fn == 1,
            "Output of `{cmd}` is:\n{stdout:?}\nThe count of {fn_:?} should only be one."
        );
        Ok(())
    })?;

    #[cfg(target_os = "windows")]
    charon(&["cargo", "--print-llbc"], dir, |stdout, cmd| {
        let main = "pub fn multi_targets::on_windows";
        ensure!(
            stdout.contains(main),
            "Output of `{cmd}` is:\n{stdout:?}\nIt doesn't contain {main:?}."
        );

        let count_fn = stdout.matches(fn_).count();
        ensure!(
            count_fn == 1,
            "Output of `{cmd}` is:\n{stdout:?}\nThe count of {fn_:?} should only be one."
        );
        Ok(())
    })?;

    let args = &["cargo", "--print-llbc", "--", "--target", target];
    charon(args, dir, |stdout, cmd| {
        let main = "pub fn multi_targets::no_os";
        ensure!(
            stdout.contains(main),
            "Output of `{cmd}` is:\n{stdout:?}\nIt doesn't contain {main:?}."
        );

        let count_fn = stdout.matches(fn_).count();
        ensure!(
            count_fn == 1,
            "Output of `{cmd}` is:\n{stdout:?}\nThe count of {fn_:?} should only be one."
        );
        Ok(())
    })
}

#[test]
fn charon_rustc() -> Result<()> {
    let path = "tests/cargo/workspace/crate1/src/lib.rs";
    let args = &["rustc", "--print-llbc", "--", "--crate-type=lib", path];

    // Call rustc without specifying --crate-name, so default to lib as the name.
    let fn_ = "pub fn lib::random_number";

    charon(args, ".", |stdout, cmd| {
        ensure!(
            stdout.contains(fn_),
            "Output of `{cmd}` is:\n{stdout:?}\nIt doesn't contain {fn_:?}."
        );

        let count_fn = stdout.matches("fn").count();
        ensure!(
            count_fn == 1,
            "Output of `{cmd}` is:\n{stdout:?}\nThe count of `fn` should only be one."
        );
        Ok(())
    })
}

#[test]
#[ignore = "Network is inaccessible in nix"]
fn charon_rust_target() -> Result<()> {
    let target = "riscv64gc-unknown-none-elf";
    rustup_install_target(target)?;

    let path = "tests/cargo/multi-targets/src/lib.rs";
    let args = &[
        "rustc",
        "--print-llbc",
        "--",
        "--crate-type=lib",
        path,
        "--crate-name",
        "multi_targets",
        "--target",
        target,
    ];
    let [stdout, rustc_cmd] = charon(args, ".", |stdout, cmd| Ok([stdout, cmd]))?;

    let dir = "tests/cargo/multi-targets";
    let args = &["cargo", "--print-llbc", "--", "--target", target];
    // Suppose outputs from cargo and rustc queries are the same...
    charon(args, dir, |desired, cargo_cmd| {
        ensure!(
            desired == stdout,
            "LLBC output differs between `charon cargo` and `charon rustc`\n\
            `{cargo_cmd}` emits:\n{desired:?}\n\
            `{rustc_cmd}` emits:\n{stdout:?}"
        );
        Ok(())
    })
}
