/// [`Formatter`](Formatter) is a trait for converting objects to string.
///
/// We need it because pretty-printing data structures often requires some
/// context. For instance, because values use value ids to point to other values,
/// we need a context to give us the mapping from value ids to values when pretty
/// printing. As the `EvalContext` data structure handles such a mapping, we
/// implement the `Formatter<ValueId::Id>` trait for it.
///
/// Our way of implementing pretty-printing for data-structures while factorizing
/// the code is as follows:
/// - for every data structure which requires formatting, we implement a
///   function `fn fmt_with_ctx(&self, ctx: T) -> String`, with proper trait
///   constraints on the context type T. We implement this kind of functions
///   for values, types, places, operands, rvalues, statements, etc, and
///   the formatting trait constraints often require the context to implement
///   `Formatter` for a various set of indices (type variable index, variable
///   index, type definition index, etc.).
/// - later on, whenever we have a suitable context type (like `EvalContext`),
///   we implement the `Formatter` trait for all the index types we need, and
///   then can easily implement it for all the above data-structures (values,
///   types, places, etc.) by calling the appropriate `fmt_with_ctx` functions.
/// The advantage of using auxiliary `fmt_with_ctx` functions is that we can
/// easily reuse those functions to implement pretty-printing with different
/// contexts, without duplicating the "non-trivial" code.
pub trait Formatter<T> {
    fn format_object(&self, x: T) -> String;
}
