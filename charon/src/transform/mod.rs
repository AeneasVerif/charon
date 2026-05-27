pub mod ctx;
pub mod typecheck_and_unify;
pub mod utils;

/// Passes that finish translation, i.e. required for the output to be a valid output.
pub mod finish_translation {
    pub mod filter_invisible_trait_impls;
    pub mod insert_assign_return_unit;
    pub mod insert_ptr_metadata;
    pub mod insert_storage_lives;
}

/// Passes that compute extra info to be stored in the crate.
pub mod add_missing_info {
    pub mod compute_short_names;
    pub mod recover_body_comments;
    pub mod reorder_decls;
    pub mod sccs;
}

/// Passes that effect some kind of normalization on the crate.
pub mod normalize {
    pub mod desugar_drops;
    pub mod expand_associated_types;
    pub mod filter_unreachable_blocks;
    pub mod partial_monomorphization;
    pub mod skip_trait_refs_when_known;
    pub mod transform_dyn_trait_calls;
}

/// Passes that undo some lowering done by rustc to recover an operation closer to what the user
/// wrote.
pub mod resugar {
    pub mod inline_local_panic_functions;
    pub mod move_asserts_to_statements;
    pub mod reconstruct_asserts;
    pub mod reconstruct_boxes;
    pub mod reconstruct_fallible_operations;
    pub mod reconstruct_intrinsics;
    pub mod reconstruct_matches;
}

/// Passes that make the output simpler/easier to consume.
pub mod simplify_output {
    pub mod filter_trivial_drops;
    pub mod hide_allocator_param;
    pub mod index_intermediate_assigns;
    pub mod index_to_function_calls;
    pub mod inline_anon_consts;
    pub mod lift_associated_item_clauses;
    pub mod ops_to_function_calls;
    pub mod remove_adt_clauses;
    pub mod remove_nops;
    pub mod remove_unit_locals;
    pub mod remove_unused_locals;
    pub mod remove_unused_self_clause;
    pub mod simplify_constants;
    pub mod unbind_item_vars;
    pub mod update_block_indices;
}

/// Passes that manipulate the control flow and reconstruct its structure.
pub mod control_flow {
    pub mod duplicate_return;
    pub mod merge_goto_chains;
    pub mod prettify_cfg;
    pub mod ullbc_to_llbc;
}

pub use ctx::TransformCtx;
use ctx::{LlbcPass, TransformPass, UllbcPass};

use crate::options::CliOpts;

/// Run transformation passes on the crate before outputting it.
pub fn run_transformation_passes(options: &CliOpts, ctx: &mut TransformCtx) {
    let non_body = |x| Pass::NonBody(CowBox::Borrowed(x));

    ctx.run_pass(Pass::NonBody(PrintCtxPass::new(
        options.print_original_ullbc,
        "# ULLBC after translation from MIR".to_string(),
    )));

    // Item and type cleanup passes.
    ctx.run_passes([
        // Compute short names. We do it early to make pretty-printed output more legible in traces.
        non_body(&add_missing_info::compute_short_names::Transform),
        // Check that translation emitted consistent types, and unify body lifetimes (best-effort).
        non_body(&typecheck_and_unify::Check::PostTranslation),
        // Filter the trait impls that were marked invisible since we couldn't filter them out
        // earlier.
        non_body(&finish_translation::filter_invisible_trait_impls::Transform),
        // Move clauses on associated types to be implied clauses of the trait.
        non_body(&simplify_output::lift_associated_item_clauses::Transform),
        // Remove the explicit `Self: Trait` clause of methods/assoc const declaration items if
        // they're not used. This simplifies the graph of dependencies between definitions.
        non_body(&simplify_output::remove_unused_self_clause::Transform),
        // Change trait associated types to be type parameters instead. See the module for details.
        // This also normalizes any use of an associated type that we can resolve.
        non_body(&normalize::expand_associated_types::Transform),
        // `--remove-adt-clauses`: Remove all trait clauses from type declarations.
        non_body(&simplify_output::remove_adt_clauses::Transform),
    ]);

    // Body cleanup passes on the ullbc.
    let pass = Pass::FusedUnstructuredBody(Box::new([
        // Compute the metadata & insert for Rvalue
        CowBox::Borrowed(&finish_translation::insert_ptr_metadata::Transform),
        // Add the missing assignments to the return value.
        // When the function return type is unit, the generated MIR doesn't set the return value to
        // `()`. This can be a concern: in the case of Aeneas, it means the return variable
        // contains ⊥ upon returning. For this reason, when the function has return type unit, we
        // insert an extra assignment just before returning.
        CowBox::Borrowed(&finish_translation::insert_assign_return_unit::Transform),
        // Insert `StorageLive` for locals that don't have one (that's allowed in MIR).
        CowBox::Borrowed(&finish_translation::insert_storage_lives::Transform),
        // Transform Drops into Calls to drop_in_place.
        CowBox::Borrowed(&normalize::desugar_drops::Transform),
        // Whenever we reference a trait method on a known type, refer to the method `FunDecl`
        // directly instead of going via a `TraitRef`. This is done before `reorder_decls` to
        // remove some sources of mutual recursion.
        CowBox::Borrowed(&normalize::skip_trait_refs_when_known::Transform),
        // Transform dyn trait method calls to vtable function pointer calls.
        // This should be early to handle the calls before other transformations.
        CowBox::Borrowed(&normalize::transform_dyn_trait_calls::Transform),
        // Inline promoted and inline consts into their parent bodies.
        simplify_output::inline_anon_consts::Transform::new(ctx),
        // `panic!()` expands to a new function definition each time. This pass cleans those up.
        resugar::inline_local_panic_functions::Transform::new(ctx),
        // Remove drop statements that are noops.
        CowBox::Borrowed(&simplify_output::filter_trivial_drops::Transform),
        // Inline all asserts that correspond to dynamic checks into statements.
        // The following pass will then merge the generated gotos as part of this substitution,
        // and [reconstruct_fallible_operations] can then use the inlined asserts to
        // reconstruct the fallible operations.
        CowBox::Borrowed(&resugar::move_asserts_to_statements::Transform),
        // Merge single-origin gotos into their parent. This drastically reduces the graph size
        // of the CFG.
        // This must be done early as some resugaring passes depend on it.
        CowBox::Borrowed(&control_flow::merge_goto_chains::Transform),
        // Remove overflow/div-by-zero/bounds checks since they are already part of the
        // arithmetic/array operation in the semantics of (U)LLBC.
        // **WARNING**: this pass uses the fact that the dynamic checks introduced by Rustc use a
        // special "assert" construct. Because of this, it must happen *before* the
        // [reconstruct_asserts] pass. See the comments in [crate::remove_dynamic_checks].
        // **WARNING**: this pass relies on a precise structure of the MIR statements. Because of this,
        // it must happen before passes that insert statements like [simplify_constants].
        CowBox::Borrowed(&resugar::reconstruct_fallible_operations::Transform),
        // Recognize calls to the `offset_of` intrinsics and replace them with the
        // corresponding `NullOp`.
        CowBox::Borrowed(&resugar::reconstruct_intrinsics::Transform),
        // Reconstruct the special `Box::new` operations inserted e.g. in the `vec![]` macro.
        // **WARNING**: this pass relies on a precise structure of the MIR statements. Because of this,
        // it must happen before passes that insert statements like [simplify_constants].
        // **WARNING**: this pass works across calls, hence must happen after `merge_goto_chains`,
        CowBox::Borrowed(&resugar::reconstruct_boxes::Transform),
        // Reconstruct the asserts
        CowBox::Borrowed(&resugar::reconstruct_asserts::Transform),
        // Desugar the constants to other values/operands as much as possible.
        CowBox::Borrowed(&simplify_output::simplify_constants::Transform),
        // Introduce intermediate assignments in preparation of the [`index_to_function_calls`]
        // pass.
        CowBox::Borrowed(&simplify_output::index_intermediate_assigns::Transform),
        // Remove locals of type `()` which show up a lot.
        CowBox::Borrowed(&simplify_output::remove_unit_locals::Transform),
        // Duplicate the return blocks
        CowBox::Borrowed(&control_flow::duplicate_return::Transform),
        // Remove the locals which are never used.
        CowBox::Borrowed(&simplify_output::remove_unused_locals::Transform),
        // Another round.
        CowBox::Borrowed(&control_flow::merge_goto_chains::Transform),
        // Filter the "dangling" blocks. Those might have been introduced by, for instance,
        // [`merge_goto_chains`].
        CowBox::Borrowed(&normalize::filter_unreachable_blocks::Transform),
        // Make sure the block ids used in the ULLBC are consecutive
        CowBox::Borrowed(&simplify_output::update_block_indices::Transform),
    ]));
    ctx.run_pass(pass);

    if !options.ullbc {
        // If we're reconstructing control-flow, print the ullbc here.
        ctx.run_pass(Pass::NonBody(PrintCtxPass::new(
            options.print_ullbc,
            "# Final ULLBC before control-flow reconstruction".to_string(),
        )));
    }

    if !options.ullbc {
        // Go from ULLBC to LLBC (Low-Level Borrow Calculus) by reconstructing the control flow.
        ctx.run_pass(non_body(&control_flow::ullbc_to_llbc::Transform));
        // Body cleanup passes after control flow reconstruction.
        let pass = Pass::FusedStructuredBody(Box::new([
            // Reconstruct matches on enum variants.
            resugar::reconstruct_matches::Transform::new(ctx),
            // Cleanup the cfg.
            CowBox::Borrowed(&control_flow::prettify_cfg::Transform),
            // Replace some unops/binops and the array aggregates with
            // function calls (introduces: ArrayToSlice, etc.)
            CowBox::Borrowed(&simplify_output::ops_to_function_calls::Transform),
            // Replace the arrays/slices index operations with function
            // calls.
            // (introduces: ArrayIndexShared, ArrayIndexMut, etc.)
            CowBox::Borrowed(&simplify_output::index_to_function_calls::Transform),
        ]));
        ctx.run_pass(pass);
    }
    // Cleanup passes useful for both llbc and ullbc.
    ctx.run_passes([
        // Remove the locals which are never used.
        non_body(&simplify_output::remove_unused_locals::Transform),
        // Remove the useless `StatementKind::Nop`s.
        non_body(&simplify_output::remove_nops::Transform),
        // Take all the comments found in the original body and assign them to statements. This must be
        // last after all the statement-affecting passes to avoid losing comments.
        non_body(&add_missing_info::recover_body_comments::Transform),
        // Hide the `A` type parameter on standard library containers (`Box`, `Vec`, etc).
        non_body(&simplify_output::hide_allocator_param::Transform),
        // Partially monomorphize items so that no item is ever instanciated with a mutable reference
        // or a type containing one.
        non_body(&normalize::partial_monomorphization::Transform),
        // Reorder the graph of dependencies and compute the strictly connex components to:
        // - compute the order in which to extract the definitions
        // - find the recursive definitions
        // - group the mutually recursive definitions
        // This is done last to account for the final item graph, not the initial one.
        non_body(&add_missing_info::reorder_decls::Transform),
    ]);

    if options.ullbc {
        // If we're not reconstructing control-flow, print the ullbc after finalizing passes.
        ctx.run_pass(Pass::NonBody(PrintCtxPass::new(
            options.print_ullbc,
            "# Final ULLBC before serialization".to_string(),
        )));
    } else {
        ctx.run_pass(Pass::NonBody(PrintCtxPass::new(
            options.print_llbc,
            "# Final LLBC before serialization".to_string(),
        )));
    }

    // Run the final passes after pretty-printing so that we get some output even if check_generics
    // fails.
    ctx.run_passes([
        // Check that types are still consistent after the transformation passes.
        non_body(&typecheck_and_unify::Check::PostTransformation),
        // Use `DeBruijnVar::Free` for the variables bound in item signatures.
        non_body(&simplify_output::unbind_item_vars::Check),
    ]);
}

pub enum CowBox<T: ?Sized + 'static> {
    Borrowed(&'static T),
    Owned(Box<T>),
}

impl<T: ?Sized + 'static> std::ops::Deref for CowBox<T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        match self {
            CowBox::Borrowed(x) => x,
            CowBox::Owned(x) => x.as_ref(),
        }
    }
}

pub enum Pass {
    NonBody(CowBox<dyn TransformPass>),
    FusedUnstructuredBody(Box<[CowBox<dyn UllbcPass>]>),
    FusedStructuredBody(Box<[CowBox<dyn LlbcPass>]>),
}

impl TransformCtx {
    fn run_pass(&mut self, mut pass: Pass) {
        match &mut pass {
            Pass::NonBody(pass) => {
                if pass.should_run(&self.options) {
                    trace!("# Starting pass {}", pass.name());
                    pass.transform_ctx(self)
                }
            }
            Pass::FusedUnstructuredBody(passes) => {
                // Some passes carry function bodies, which must also be transformed. This applies
                // all the passes before pass `p` to the bodies potentially carried by pass `p`.
                for i in 0..passes.len() {
                    if let (first_passes, [pass, ..]) = passes.split_at_mut(i) {
                        if let CowBox::Owned(pass) = pass {
                            pass.apply_preceding_passes(self, first_passes);
                        }
                    }
                }
                self.for_each_item_mut(|ctx, mut item| {
                    for pass in passes.iter() {
                        if pass.should_run(&ctx.options) {
                            trace!("# Starting pass {}", pass.name());
                            pass.transform_item(ctx, item.reborrow());
                        }
                    }
                });
                for pass in passes.iter() {
                    pass.finalize(self);
                }
            }
            Pass::FusedStructuredBody(passes) => {
                self.for_each_fun_decl(|ctx, decl| {
                    for pass in passes.iter() {
                        if pass.should_run(&ctx.options) {
                            trace!("# Starting pass {}", pass.name());
                            pass.transform_function(ctx, decl);
                        }
                    }
                });
            }
        };
    }
    fn run_passes(&mut self, passes: impl IntoIterator<Item = Pass>) {
        for pass in passes {
            self.run_pass(pass);
        }
    }
}

pub struct PrintCtxPass {
    pub message: String,
    /// Whether we're printing to stdout or only logging.
    pub to_stdout: bool,
}

impl PrintCtxPass {
    pub fn new(to_stdout: bool, message: String) -> CowBox<dyn TransformPass> {
        let ret = Self { message, to_stdout };
        CowBox::Owned(Box::new(ret))
    }
}

impl TransformPass for PrintCtxPass {
    fn transform_ctx(&self, ctx: &mut TransformCtx) {
        let message = &self.message;
        if self.to_stdout {
            println!("{message}:\n\n{ctx}\n");
        } else {
            trace!("{message}:\n\n{ctx}\n");
        }
    }
}
