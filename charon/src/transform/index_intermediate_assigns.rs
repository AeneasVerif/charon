//! This micro-pass introduces intermediate assignments in preparation of
//! [`index_to_function_calls`], so as to avoid borrow-checking errors.
//!
//! The problem comes from "and assignments" like in the snippet of code below:
//! ```text
//! x[0] += 1; // Desugars to: x[0] = copy x[0] + 1
//! ```
//!
//! If we don't introduce an intermediate assignment, then the micro-pass which
//! transforms the index operations into function calls generates the following
//! LLBC:
//! ```text
//! dest = &mut x[0];
//! src = & x[0]; // Invalidates dest
//! *dest = copy (*src) + 1; // Can't dereference dest!
//! ```
//! (also note that the problem remains if we introduce `src` *then* `dest`).
//!
//! Our solution is to introduce a temporary variable for the assignment.
//! We first transform the code to:
//! ```text
//! tmp = copy x[0] + 1;
//! x[0] = move tmp;
//! ```
//!
//! Which then allows us to transform it to:
//! ```text
//! // RHS:
//! src = & x[0];
//! tmp = copy (*src) + 1;
//! // LHS:
//! dest = &mut x[0];
//! *dest = move tmp;
//! ```

use crate::llbc_ast::*;
use crate::transform::TransformCtx;
use derive_visitor::{visitor_enter_fn, Drive};

use super::ctx::LlbcPass;

fn contains_index_proj<T: Drive>(x: &T) -> bool {
    let mut contains_index = false;
    x.drive(&mut visitor_enter_fn(|proj: &ProjectionElem| {
        use ProjectionElem::*;
        if let Index { .. } | Subslice { .. } = proj {
            contains_index = true;
        }
    }));
    contains_index
}

impl Place {
    fn contains_index_proj(&self) -> bool {
        contains_index_proj(self)
    }
}

impl Rvalue {
    fn contains_index_proj(&self) -> bool {
        contains_index_proj(self)
    }
}

fn introduce_intermediate_let_binding(
    ctx: &mut TransformCtx<'_>,
    span: Span,
    locals: &mut Locals,
    lhs: &mut Place,
    rhs: &mut Rvalue,
) -> Vec<Statement> {
    // Compute the type of the lhs
    let Ok(lhs_ty) = lhs.ty(&ctx.translated.type_decls, locals) else {
        use crate::pretty::fmt_with_ctx::FmtWithCtx;
        use crate::pretty::formatter::IntoFormatter;
        let msg = format!(
            "Could not compute the type of place: {}",
            lhs.fmt_with_ctx(&ctx.into_fmt())
        );
        crate::register_error_or_panic!(ctx, span, msg);
        return vec![];
    };

    // Introduce a fresh local variable, for the temporary assignment
    let tmp_var = locals.new_var(None, lhs_ty);

    // Update the rhs
    let tmp_rhs = std::mem::replace(rhs, Rvalue::Use(Operand::Move(tmp_var.clone())));

    // Introduce the intermediate let-binding
    vec![Statement::new(span, RawStatement::Assign(tmp_var, tmp_rhs))]
}

pub struct Transform;

impl LlbcPass for Transform {
    fn transform_body(&self, ctx: &mut TransformCtx<'_>, b: &mut ExprBody) {
        b.body.transform(&mut |st: &mut Statement| {
            match &mut st.content {
                RawStatement::Assign(lhs, rhs)
                    if lhs.contains_index_proj() && rhs.contains_index_proj() =>
                {
                    // Introduce an intermediate statement if both the rhs and the lhs contain an
                    // "index" projection element (this way we avoid introducing too many
                    // intermediate assignments).
                    introduce_intermediate_let_binding(ctx, st.span, &mut b.locals, lhs, rhs)
                }
                _ => vec![],
            }
        });
    }
}
