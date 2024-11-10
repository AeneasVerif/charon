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

use crate::ids::Vector;
use crate::llbc_ast::*;
use crate::transform::TransformCtx;
use derive_visitor::{Drive, Visitor};

use super::ctx::LlbcPass;

impl Place {
    fn contains_index(&self) -> bool {
        for pe in &self.projection {
            use ProjectionElem::*;
            if let Index { .. } | Subslice { .. } = pe {
                return true;
            };
        }
        return false;
    }
}

#[derive(Visitor)]
#[visitor(Place(enter))]
struct RvalueVisitor {
    contains_index: bool,
}

impl RvalueVisitor {
    fn enter_place(&mut self, p: &Place) {
        self.contains_index = self.contains_index || p.contains_index();
    }
}

impl Rvalue {
    fn contains_index(&self) -> bool {
        let mut v = RvalueVisitor {
            contains_index: false,
        };
        self.drive(&mut v);
        v.contains_index
    }
}

fn introduce_intermediate_let_binding(
    ctx: &mut TransformCtx<'_>,
    span: Span,
    locals: &mut Vector<VarId, Var>,
    lhs: &mut Place,
    rhs: &mut Rvalue,
) -> Vec<Statement> {
    // Compute the type of the lhs
    let Ok(lhs_ty) = lhs.compute_projected_type(&ctx.translated.type_decls, locals) else {
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
    let tmp_var = locals.push_with(|index| Var {
        index,
        name: None,
        ty: lhs_ty,
    });

    // Update the rhs
    let tmp_rhs = std::mem::replace(rhs, Rvalue::Use(Operand::Move(Place::new(tmp_var))));

    // Introduce the intermediate let-binding
    vec![Statement {
        span,
        content: RawStatement::Assign(Place::new(tmp_var), tmp_rhs),
        comments_before: vec![],
    }]
}

pub struct Transform;

impl LlbcPass for Transform {
    fn transform_body(&self, ctx: &mut TransformCtx<'_>, b: &mut ExprBody) {
        b.body.transform(&mut |st: &mut Statement| {
            let locals = &mut b.locals;

            //
            match &mut st.content {
                RawStatement::Assign(lhs, rhs) => {
                    // Introduce an intermediate statement if and only
                    // if both the rhs and the lhs contain an "index"
                    // projection element (this way we avoid introducing
                    // too many intermediate assignments).
                    if lhs.contains_index() && rhs.contains_index() {
                        introduce_intermediate_let_binding(ctx, st.span, locals, lhs, rhs)
                    } else {
                        vec![]
                    }
                }
                _ => vec![],
            }
        });
    }
}