#![feature(rustc_private, register_tool)]
#![feature(box_syntax, box_patterns)]
#![register_tool(creusot)]
#![feature(const_panic)]
#![feature(cell_leak)] // For Ref::leak
// For rustdoc: prevents overflows
#![recursion_limit = "256"]

extern crate env_logger;
extern crate hashlink;
extern crate im;
extern crate linked_hash_set;
extern crate log;
extern crate rustc_ast;
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_mir;
extern crate rustc_resolve;
extern crate rustc_session;
extern crate rustc_span;
extern crate rustc_target;

#[macro_use]
mod common;
mod cfim_ast;
mod divergent;
mod expressions;
mod formatter;
mod get_mir;
mod graphs;
mod id_vector;
mod im_ast;
mod im_to_cfim;
mod register;
mod reorder_decls;
mod translate_functions_to_im;
mod translate_types;
mod types;
mod values;
mod vars;

use rustc_driver::{abort_on_err, Callbacks, Compilation, RunCompiler};
use rustc_interface::{
    interface::{BoxedResolver, Compiler},
    Queries,
};
use rustc_middle::ty::TyCtxt;
use rustc_session::Session;
use std::{cell::RefCell, rc::Rc};

struct ToInternal {}

impl Callbacks for ToInternal {
    fn after_expansion<'tcx>(&mut self, c: &Compiler, queries: &'tcx Queries<'tcx>) -> Compilation {
        let session = c.session();
        let resolver = {
            let parts = abort_on_err(queries.expansion(), session).peek();
            let resolver = parts.1.borrow();
            resolver.clone()
        };

        // TODO: extern crates
        queries
            .global_ctxt()
            .unwrap()
            .peek_mut()
            .enter(|tcx| {
                let session = c.session();
                translate(session, tcx, resolver)
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
    // particular to let the user choose how to filter the log.
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

use structopt::StructOpt;

#[derive(StructOpt)]
#[structopt(name = "Charon")]
struct CliOpts {
    #[structopt(parse(from_os_str))]
    path: std::path::PathBuf,
}

fn main() {
    // Initialize the logger
    initialize_logger();

    let args = CliOpts::from_args();

    let myself = match std::env::args().next() {
        Some(s) => s.to_owned(),
        None => panic!("Impossible: zero arguments on the command-line!"),
    };

    // Retrieve the sysroot (the path to the executable of the compiler extended
    // with our analysis).
    let out = std::process::Command::new("rustc")
        .arg("--print=sysroot")
        .current_dir(".")
        .output()
        .unwrap();
    let sysroot = std::str::from_utf8(&out.stdout).unwrap().trim();
    let sysroot_arg = format!("--sysroot={}", sysroot).to_owned();

    let input_file = match args.path.to_str() {
        Some(s) => s.to_owned(),
        None => panic!("Illegal path for the input file argument"),
    };

    let args = vec![
        myself,
        sysroot_arg,
        input_file,
        "--crate-type=lib".to_owned(),
        "--edition=2018".to_owned(),
    ];
    RunCompiler::new(&args, &mut ToInternal {}).run().unwrap();
}

type TranslationResult<T> = Result<T, ()>;

fn translate(
    sess: &Session,
    tcx: TyCtxt,
    _resolver: Rc<RefCell<BoxedResolver>>,
) -> TranslationResult<()> {
    trace!();

    // Explore the modules in the crate, then items in the modules.
    // We can iterate over the items directly, but we want to do it module
    // by module.

    // # Step 1: check and register all the declarations, to build the graph
    // of dependencies between them (we need to know in which
    // order to extract the definitions, and which ones are mutually
    // recursive). While building this graph, we perform as many checks as
    // we can to make sure the code is in the proper rust subset. Those very
    // early steps mostly involve checking whether some features are used or
    // not (ex.: raw pointers, inline ASM, etc.). More complex checks are
    // performed later. In general, whenever there is ambiguity on the potential
    // step in which a step could be performed, we perform it as soon as possible.
    // Building the graph of dependencies allows us to translate the declarations
    // in the proper order, and to figure out which definitions are mutually
    // recursive.
    // We iterate over the HIR items, and explore their MIR bodies/ADTs/etc.
    // (when those exist - for instance, type aliases don't have MIR translations
    // so we just ignore them).
    let registered_decls = register::register_crate(sess, tcx)?;

    // # Step 2: reorder the graph of dependencies and compute the strictly
    // connex components (i.e.: the mutually recursive definitions).
    let ordered_decls = reorder_decls::reorder_declarations(&registered_decls)?;

    // # Step 3: compute which functions are potentially divergent. A function
    // is potentially divergent if it is recursive or transitively calls a
    // potentially divergent function.
    // Note that in the future, we may complement this basic analysis with a
    // finer analysis to detect recursive functions which are actually total
    // by construction.
    let divergent = divergent::compute_divergent_functions(&registered_decls, &ordered_decls);

    // TODO: check if can panic

    // # Step 4: translate the types.
    let tt_ctx = translate_types::translate_types(&tcx, &ordered_decls)?;

    // # Step 5: translate the functions to IM (our Internal representation of MIR)
    let im_decls =
        translate_functions_to_im::translate_functions(&tcx, tt_ctx, &ordered_decls, divergent)?;

    // # Step 6: go from IM to CFIM (Control-Flow Internal MIR) by reconstructing
    // the control flow.
    // Note that from now onwards, we don't interact with rustc anymore.
    let _cfim_decls = im_to_cfim::translate_functions(&im_decls);

    // TODO: simplify the calls to unops or binops
    // TODO: reconstruct asserts

    // # Step ?: generate the files.
    Ok(())
}
