#![feature(rustc_private, register_tool)]
#![feature(box_syntax, box_patterns)]
#![feature(cell_leak)] // For Ref::leak
// For rustdoc: prevents overflows
#![recursion_limit = "256"]

extern crate env_logger;
extern crate hashlink;
extern crate im;
extern crate linked_hash_set;
extern crate log;
extern crate rustc_ast;
extern crate rustc_borrowck;
extern crate rustc_const_eval;
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_mir_dataflow;
extern crate rustc_mir_transform;
extern crate rustc_monomorphize;
extern crate rustc_resolve;
extern crate rustc_session;
extern crate rustc_span;
extern crate rustc_target;

#[macro_use]
mod common;
mod assumed;
mod cfim_ast;
mod cfim_ast_utils;
mod cfim_export;
mod divergent;
mod expressions;
mod expressions_utils;
mod formatter;
mod get_mir;
mod graphs;
mod id_vector;
mod im_ast;
mod im_ast_utils;
mod im_to_cfim;
mod insert_assign_return_unit;
mod reconstruct_asserts;
mod regions_hierarchy;
mod register;
mod reorder_decls;
mod rust_to_local_ids;
mod simplify_binops;
mod translate_functions_to_im;
mod translate_types;
mod types;
mod types_utils;
mod values;
mod values_utils;
mod vars;

use rustc_driver::{Callbacks, Compilation, RunCompiler};
use rustc_interface::{interface::Compiler, Queries};
use rustc_middle::ty::TyCtxt;
use rustc_session::Session;
use std::path::PathBuf;
use structopt::StructOpt;

struct ToInternal {
    dest_dir: Option<PathBuf>,
    source_file: PathBuf,
}

impl Callbacks for ToInternal {
    fn after_analysis<'tcx>(&mut self, c: &Compiler, queries: &'tcx Queries<'tcx>) -> Compilation {
        // TODO: extern crates
        queries
            .global_ctxt()
            .unwrap()
            .peek_mut()
            .enter(|tcx| {
                let session = c.session();
                translate(session, tcx, &self.dest_dir, &self.source_file)
            })
            .unwrap();
        Compilation::Stop
    }
}

/// Initialize the logger. We use a custom initialization to add some
/// useful debugging information, including the line number in the file.
fn initialize_logger() {
    use chrono::offset::Local;
    use env_logger::fmt::Color;
    use env_logger::Builder;
    use std::io::Write;

    // Initialize the log builder in the default way - we do this in
    // particular to let the user choose the log level (i.e.: trace,
    // debug, warning, etc.)
    let mut builder = Builder::from_default_env();

    // Modify the output format - we add the line number
    builder.format(|buf, record| {
        // Retreive the path (CRATE::MODULE) and the line number
        let path = match record.module_path() {
            Some(s) => s,
            None => "",
        };
        let line = match record.line() {
            Some(l) => l.to_string(),
            None => "".to_string(),
        };

        // Style for the brackets (change the color)
        let mut bracket_style = buf.style();
        bracket_style.set_color(Color::Rgb(120, 120, 120));

        writeln!(
            buf,
            "{}{} {} {}:{}{} {}",
            bracket_style.value("["),
            Local::now().format("%H:%M:%S"), // Rk.: use "%Y-%m-%d" to also have the date
            buf.default_styled_level(record.level()), // Print the level with colors
            path,
            line,
            bracket_style.value("]"),
            record.args()
        )
    });

    builder.init();
}

/// This structure is used to store the command-line instructions.
/// We automatically derive a command-line parser based on this structure.
#[derive(StructOpt)]
#[structopt(name = "Charon")]
struct CliOpts {
    /// The input file.
    #[structopt(parse(from_os_str))]
    input_file: PathBuf,
    /// The destination directory, if we don't want to generate the output
    /// in the same directory as the input file.
    #[structopt(short = "dest", long = "dest", parse(from_os_str))]
    dest_dir: Option<PathBuf>,
    /// If `true`, use Polonius' non-lexical lifetimes (NLL) analysis.
    #[structopt(short = "nll", long = "nll")]
    use_polonius: bool,
}

fn main() {
    // Initialize the logger
    initialize_logger();

    // Retrieve the executable path - this is not considered an argument,
    // and won't be parsed by CliOpts
    let exec_path = match std::env::args().next() {
        Some(s) => s.to_owned(),
        None => panic!("Impossible: zero arguments on the command-line!"),
    };

    // Parse the command-line
    let args = CliOpts::from_args();

    // Retrieve the sysroot (the path to the executable of the compiler extended
    // with our analysis).
    let out = std::process::Command::new("rustc")
        .arg("--print=sysroot")
        .current_dir(".")
        .output()
        .unwrap();
    let sysroot = std::str::from_utf8(&out.stdout).unwrap().trim();
    let sysroot_arg = format!("--sysroot={}", sysroot).to_owned();

    let mut compiler_args = vec![
        exec_path,
        sysroot_arg,
        args.input_file.as_path().to_str().unwrap().to_string(),
        "--crate-type=lib".to_string(),
        "--edition=2018".to_string(),
    ];
    if args.use_polonius {
        compiler_args.push("-Zpolonius".to_string());
    }

    RunCompiler::new(
        &compiler_args,
        &mut ToInternal {
            dest_dir: args.dest_dir,
            source_file: args.input_file,
        },
    )
    .run()
    .unwrap();
}

type TranslationResult<T> = Result<T, ()>;

fn translate(
    sess: &Session,
    tcx: TyCtxt,
    dest_dir: &Option<PathBuf>,
    source_file: &PathBuf,
) -> TranslationResult<()> {
    trace!();
    // Retrieve the crate name.
    let crate_name = tcx
        .crate_name(rustc_span::def_id::LOCAL_CRATE)
        .to_ident_string();
    trace!("# Crate: {}", crate_name);

    // # Step 1: check and register all the definitions, to build the graph
    // of dependencies between them (we need to know in which
    // order to extract the definitions, and which ones are mutually
    // recursive). While building this graph, we perform as many checks as
    // we can to make sure the code is in the proper rust subset. Those very
    // early steps mostly involve checking whether some features are used or
    // not (ex.: raw pointers, inline ASM, etc.). More complex checks are
    // performed later. In general, whenever there is ambiguity on the potential
    // step in which a step could be performed, we perform it as soon as possible.
    // Building the graph of dependencies allows us to translate the definitions
    // in the proper order, and to figure out which definitions are mutually
    // recursive.
    // We iterate over the HIR items, and explore their MIR bodies/ADTs/etc.
    // (when those exist - for instance, type aliases don't have MIR translations
    // so we just ignore them).
    let registered_decls = register::register_crate(sess, tcx)?;

    // # Step 2: reorder the graph of dependencies and compute the strictly
    // connex components (i.e.: the mutually recursive definitions).
    let ordered_decls = reorder_decls::reorder_declarations(&registered_decls)?;

    // # Step 3: generate identifiers for the types and functions, and compute
    // the mappings from rustc identifiers to our own identifiers.
    let ordered_decls = rust_to_local_ids::rust_to_local_ids(&ordered_decls);

    // # Step 4: translate the types.
    let (types_constraints, type_defs) = translate_types::translate_types(tcx, &ordered_decls)?;

    // # Step 5: translate the functions to IM (our Internal representation of MIR)
    let im_defs = translate_functions_to_im::translate_functions(
        tcx,
        &ordered_decls,
        &types_constraints,
        &type_defs,
    )?;

    // # Step 6: go from IM to CFIM (Control-Flow Internal MIR) by reconstructing
    // the control flow.
    //
    // Note that from now onwards, we don't interact with rustc anymore.
    let cfim_defs = im_to_cfim::translate_functions(&type_defs, &im_defs);

    // # Step 7: simplify the calls to binops
    // Note that we assume that the sequences have been flattened.
    let cfim_defs = simplify_binops::simplify(cfim_defs);

    for def in &cfim_defs {
        trace!(
            "# After binop simplification:\n{}\n",
            def.fmt_with_defs(&type_defs, &cfim_defs)
        );
    }

    // # Step 8: reconstruct the asserts
    let cfim_defs = reconstruct_asserts::simplify(cfim_defs);

    for def in &cfim_defs {
        trace!(
            "# After asserts reconstruction:\n{}\n",
            def.fmt_with_defs(&type_defs, &cfim_defs)
        );
    }

    // # Step 9: add the missing assignments to the return value.
    // When the function's return type is unit, the generated MIR doesn't
    // set the return value to `()`. This can be a concern: in the case
    // of AENEAS, it means the return variable contains ⊥ upon returning.
    // For this reason, when the function has return type unit, we insert
    // an extra assignment just before returning.
    let cfim_defs = insert_assign_return_unit::transform(cfim_defs);

    // # Step 10: compute which functions are potentially divergent. A function
    // is potentially divergent if it is recursive or transitively calls a
    // potentially divergent function.
    // Note that in the future, we may complement this basic analysis with a
    // finer analysis to detect recursive functions which are actually total
    // by construction.
    let _divergent = divergent::compute_divergent_functions(&ordered_decls, &cfim_defs);

    // # Step 11: generate the files.
    cfim_export::export(
        crate_name,
        &ordered_decls,
        &type_defs,
        &cfim_defs,
        dest_dir,
        source_file,
    )?;

    trace!("Done");

    Ok(())
}
