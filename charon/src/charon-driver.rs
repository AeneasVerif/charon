//! The Charon driver, which calls Rustc with callbacks to compile some Rust
//! crate to LLBC.

use charon_lib::cli_options;
use charon_lib::driver::{
    arg_value, get_args_crate_index, get_args_source_index, CharonCallbacks, CharonFailure,
    RunCompilerNormallyCallbacks,
};
use charon_lib::export::CrateData;
use charon_lib::logger;
use charon_lib::trace;

fn main() {
    // Initialize the logger
    logger::initialize_logger();

    // Retrieve the executable path - this is not considered an argument,
    // and won't be parsed by CliOpts
    let origin_args: Vec<String> = std::env::args().collect();
    assert!(
        !origin_args.is_empty(),
        "Impossible: zero arguments on the command-line!"
    );
    trace!("original arguments (computed by cargo): {:?}", origin_args);

    // Compute the sysroot (the path to the executable of the compiler):
    // - if it is already in the command line arguments, just retrieve it from there
    // - otherwise retrieve the sysroot from a call to rustc
    let sysroot_arg = arg_value(&origin_args, "--sysroot", |_| true);
    let has_sysroot_arg = sysroot_arg.is_some();
    let sysroot = if has_sysroot_arg {
        sysroot_arg.unwrap().to_string()
    } else {
        let out = std::process::Command::new("rustc")
            .arg("--print=sysroot")
            .current_dir(".")
            .output()
            .unwrap();
        let sysroot = std::str::from_utf8(&out.stdout).unwrap().trim();
        sysroot.to_string()
    };

    // Compute the compiler arguments for Rustc.
    // We first use all the arguments received by charon-driver, except the first two.
    // Rem.: the first argument is the path to the charon-driver executable.
    // Rem.: the second argument is "rustc" (passed by Cargo because RUSTC_WRAPPER is set).
    assert!(origin_args[1].ends_with("rustc"));
    let mut compiler_args: Vec<String> = origin_args[2..].to_vec();

    // Retrieve the Charon options by deserializing them from the environment variable
    // (cargo-charon serialized the arguments and stored them in a specific environment
    // variable before calling cargo with RUSTC_WORKSPACE_WRAPPER=charon-driver).
    let options: cli_options::CliOpts = match std::env::var(cli_options::CHARON_ARGS) {
        Ok(opts) => serde_json::from_str(opts.as_str()).unwrap(),
        Err(_) => {
            // Parse any arguments after `--` as charon arguments.
            if let Some((i, _)) = compiler_args.iter().enumerate().find(|(_, s)| *s == "--") {
                use clap::Parser;
                let mut charon_args = compiler_args.split_off(i);
                charon_args[0] = origin_args[0].clone(); // Replace `--` with the name of the binary
                cli_options::CliOpts::parse_from(charon_args)
            } else {
                Default::default()
            }
        }
    };

    if !has_sysroot_arg {
        compiler_args.extend(vec!["--sysroot".to_string(), sysroot]);
    }
    if options.use_polonius {
        compiler_args.push("-Zpolonius".to_string());
    }

    // Cargo calls the driver twice. The first call to the driver is with "--crate-name ___" and no
    // source file, for Cargo to retrieve some information about the crate.
    let is_dry_run = arg_value(&origin_args, "--crate-name", |s| s == "___").is_some();
    // When called using cargo, we tell cargo to use `charon-driver` by setting the
    // `RUSTC_WORKSPACE_WRAPPER` env var. This uses `charon-driver` for all the crates in the
    // workspace. We may however not want to be calling charon on all crates;
    // `CARGO_PRIMARY_PACKAGE` tells us whether the crate was specifically selected or is a
    // dependency.
    let is_workspace_dependency = std::env::var("CHARON_USING_CARGO").is_ok()
        && !std::env::var("CARGO_PRIMARY_PACKAGE").is_ok();

    if is_dry_run || is_workspace_dependency {
        trace!("Skipping charon; running compiler normally instead.");
        // In this case we run the compiler normally.
        RunCompilerNormallyCallbacks
            .run_compiler(compiler_args)
            .unwrap();
        return;
    }

    // In order to have some flexibility in our tests, we give the possibility
    // of specifying the source (the input file which gives the entry to the
    // crate), and of changing the crate name. This allows us to group multiple
    // tests in one crate and call Charon on subsets of this crate (which makes
    // things a lot easier from a maintenance point of view). For instance,
    // we don't extract the whole Charon `tests` (`charon/tests`) crate at once,
    // but rather: `no_nested_borrows`, `hasmap`, `hashmap_main`... Note that
    // this is very specific to the test suite for Charon, so we might remove
    // this in the future. Also, we wouldn't need to do this if we could define
    // several libraries in a single `Cargo.toml` file.
    //
    // If such options are present, we need to update the arguments giving
    // the crate name and the source file.

    // First replace the source name
    let source_index = get_args_source_index(&compiler_args);
    if let Some(source_index) = source_index {
        trace!("source ({}): {}", source_index, compiler_args[source_index]);

        if options.input_file.is_some() {
            compiler_args[source_index] = options
                .input_file
                .as_ref()
                .unwrap()
                .to_str()
                .unwrap()
                .to_string();
        }

        // We replace the crate name only if there is a source name *in the arguments*:
        // we do so because sometimes the driver is called with a crate name but no
        // source. This happens when Cargo needs to retrieve information about
        // the crate.
        if options.crate_name.is_some() {
            let crate_name_index = get_args_crate_index(&compiler_args);
            if let Some(crate_name_index) = crate_name_index {
                trace!(
                    "crate name ({}): {}",
                    crate_name_index,
                    compiler_args[crate_name_index]
                );

                compiler_args[crate_name_index] = options.crate_name.as_ref().unwrap().clone();
            }
            // If there was no crate name given as parameter, introduce one
            else {
                compiler_args.push("--crate-name".to_string());
                compiler_args.push(options.crate_name.as_ref().unwrap().clone());
            }
        }
    }

    trace!("Compiler arguments: {:?}", compiler_args);

    // Call the Rust compiler with our custom callback.
    let errors_as_warnings = options.errors_as_warnings;
    let mut callback = CharonCallbacks::new(options);
    let mut res = callback.run_compiler(compiler_args);
    if !callback.options.no_serialize {
        // # Final step: generate the files.
        res = res.and_then(|()| {
            // `crate_data` is set by our callbacks when there is no fatal error.
            let crate_data = callback.crate_data.as_ref().unwrap();
            let dest_file = match callback.options.dest_file.clone() {
                Some(f) => f,
                None => {
                    let mut target_filename = callback.options.dest_dir.clone().unwrap_or_default();
                    let (crate_name, extension) = match crate_data {
                        CrateData::ULLBC(d) => (&d.name, "ullbc"),
                        CrateData::LLBC(d) => (&d.name, "llbc"),
                    };
                    target_filename.push(format!("{crate_name}.{extension}"));
                    target_filename
                }
            };
            trace!("Target file: {:?}", dest_file);
            crate_data
                .serialize_to_file(&dest_file)
                .map_err(|()| CharonFailure::Serialize)
        });
    }

    match res {
        Ok(()) => {
            if callback.error_count > 0 {
                assert!(errors_as_warnings);
                let msg = format!("The extraction generated {} warnings", callback.error_count);
                log::warn!("{}", msg);
            }
        }
        Err(CharonFailure::Panic) => {
            // Standard rust panic error code.
            std::process::exit(101);
        }
        Err(CharonFailure::RustcError(_) | CharonFailure::Serialize) => {
            assert!(!errors_as_warnings);
            let msg = format!("The extraction encountered {} errors", callback.error_count);
            log::error!("{}", msg);
            std::process::exit(1);
        }
    }
}
