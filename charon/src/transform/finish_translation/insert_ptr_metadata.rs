use crate::transform::TransformCtx;
use crate::transform::ctx::BodyTransformCtx;
use crate::{transform::ctx::UllbcPass, ullbc_ast::*};

pub struct Transform;

/// This pass computes the metadata for Rvalue, which is used to create references and raw pointers.
/// E.g., in cases like:
/// ```ignore
/// let x = &[mut] (*some_v).field;
/// ```
/// If the `(*some_v).field` is a DST, like `[i32]`, we will need to fetch the metadata, i.e., the length of the slice,
/// and store it in a local variable, then we have:
/// ```ignore
/// let x = Rvalue::Ref { place:(*some_v).field, kind: [mut], ptr_metadata: PtrMetadata(some_v) };
/// ```
/// There should be a new local variable introduced to store `PtrMetadata(some_v)`.
impl UllbcPass for Transform {
    fn transform_function(&self, ctx: &mut TransformCtx, decl: &mut FunDecl) {
        decl.transform_ullbc_statements(ctx, |ctx, st: &mut Statement| {
            st.dyn_visit_in_body_mut(|x: &mut Rvalue| {
                if let Rvalue::Ref {
                    place,
                    ptr_metadata,
                    ..
                }
                | Rvalue::RawPtr {
                    place,
                    ptr_metadata,
                    ..
                } = x
                {
                    *ptr_metadata = ctx.compute_place_metadata(place);
                }
            });
        })
    }
}
