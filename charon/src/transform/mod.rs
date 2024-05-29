pub mod ctx;
pub mod graphs;
pub mod index_to_function_calls;
pub mod insert_assign_return_unit;
pub mod ops_to_function_calls;
pub mod reconstruct_asserts;
pub mod remove_arithmetic_overflow_checks;
pub mod remove_drop_never;
pub mod remove_dynamic_checks;
pub mod remove_nops;
pub mod remove_read_discriminant;
pub mod remove_unused_locals;
pub mod reorder_decls;
pub mod simplify_constants;
pub mod skip_trait_refs_when_known;
pub mod ullbc_to_llbc;
pub mod update_closure_signatures;

pub use ctx::TransformCtx;

pub static ULLBC_PASSES: &[&dyn ctx::UllbcPass] = &[
    // # Micro-pass: Remove overflow/div-by-zero/bounds checks since they are already part of the
    // arithmetic/array operation in the semantics of (U)LLBC.
    // **WARNING**: this pass uses the fact that the dynamic checks introduced by Rustc use a
    // special "assert" construct. Because of this, it must happen *before* the
    // [reconstruct_asserts] pass. See the comments in [crate::remove_dynamic_checks].
    // **WARNING**: this pass relies on a precise structure of the MIR statements. Because of this,
    // it must happen before passes that insert statements like [simplify_constants].
    &remove_dynamic_checks::Transform,
    // # Micro-pass: desugar the constants to other values/operands as much
    // as possible.
    &simplify_constants::Transform,
    // # Micro-pass: whenever we call a trait method on a known type, refer to the method `FunDecl`
    // directly instead of going via a `TraitRef`. This is done before `reorder_decls` to remove
    // some sources of mutual recursion.
    &skip_trait_refs_when_known::Transform,
];

pub static LLBC_PASSES: &[&dyn ctx::LlbcPass] = &[
    // # Micro-pass: the first local variable of closures is the
    // closure itself. This is not consistent with the closure signature,
    // which ignores this first variable. This micro-pass updates this.
    &update_closure_signatures::Transform,
    // # Micro-pass: remove the dynamic checks we couldn't remove in [`remove_dynamic_checks`].
    // **WARNING**: this pass uses the fact that the dynamic checks
    // introduced by Rustc use a special "assert" construct. Because of
    // this, it must happen *before* the [reconstruct_asserts] pass.
    &remove_arithmetic_overflow_checks::Transform,
    // # Micro-pass: reconstruct the asserts
    &reconstruct_asserts::Transform,
    // # Micro-pass: replace some unops/binops and the array aggregates with
    // function calls (introduces: ArrayToSlice, etc.)
    &ops_to_function_calls::Transform,
    // # Micro-pass: replace the arrays/slices index operations with function
    // calls.
    // (introduces: ArrayIndexShared, ArrayIndexMut, etc.)
    &index_to_function_calls::Transform,
    // # Micro-pass: Remove the discriminant reads (merge them with the switches)
    &remove_read_discriminant::Transform,
    // # Micro-pass: add the missing assignments to the return value.
    // When the function return type is unit, the generated MIR doesn't
    // set the return value to `()`. This can be a concern: in the case
    // of Aeneas, it means the return variable contains ⊥ upon returning.
    // For this reason, when the function has return type unit, we insert
    // an extra assignment just before returning.
    // This also applies to globals (for checking or executing code before
    // the main or at compile-time).
    &insert_assign_return_unit::Transform,
    // # Micro-pass: remove the drops of locals whose type is `Never` (`!`). This
    // is in preparation of the next transformation.
    &remove_drop_never::Transform,
    // # Micro-pass: remove the locals which are never used. After doing so, we
    // check that there are no remaining locals with type `Never`.
    &remove_unused_locals::Transform,
    // # Micro-pass (not necessary, but good for cleaning): remove the
    // useless no-ops.
    &remove_nops::Transform,
];
