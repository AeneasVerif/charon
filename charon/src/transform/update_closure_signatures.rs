//! # Micro-pass: the first local variable of closures is (a borrow to) the closure itself. This is
//! not consistent with the closure signature, which represents the captured state as a tuple. This
//! micro-pass updates this.
use crate::ids::Vector;
use crate::transform::TransformCtx;
use crate::ullbc_ast::*;
use derive_generic_visitor::{Continue, ControlFlow, Visitor};

use super::ctx::UllbcPass;

#[derive(Visitor)]
struct InsertRegions<'a> {
    regions: &'a mut Vector<RegionId, RegionVar>,
    // The number of region groups we dived into (we don't count the regions
    // at the declaration level). We use this for the DeBruijn indices.
    depth: usize,
}

impl VisitAstMut for InsertRegions<'_> {
    fn exit_region(&mut self, r: &mut Region) {
        if r == &Region::Erased {
            // Insert a fresh region
            let index = self
                .regions
                .push_with(|index| RegionVar { index, name: None });
            *r = Region::Var(DeBruijnVar::free(index));
        }
    }

    fn visit_region_binder<T: AstVisitable>(
        &mut self,
        x: &mut RegionBinder<T>,
    ) -> ControlFlow<Self::Break> {
        self.depth += 1;
        self.visit_inner(x)?;
        self.depth -= 1;
        Continue(())
    }
}

fn transform_function(
    _ctx: &TransformCtx,
    def: &mut FunDecl,
    body: Option<&mut ExprBody>,
) -> Result<(), Error> {
    let FunSig {
        closure_info,
        inputs,
        generics,
        ..
    } = &mut def.signature;
    if let Some(info) = closure_info {
        // Explore the state and introduce fresh regions for the erased regions we find.
        let mut visitor = InsertRegions {
            regions: &mut generics.regions,
            depth: 0,
        };
        inputs[0].drive_mut(&mut visitor);

        // Update the body.
        // We change the type of the local variable of index 1, which is a reference to the closure
        // itself, so that it has the type of (a reference to) the state of the closure.
        //
        // For instance, in the example below:
        // ```text
        // pub fn test_closure_capture(x: u32, y: u32) -> u32 {
        //   let f = &|z| x + y + z;
        //   (f)(0)
        // }
        // ```
        //
        // The first local variable in the body of the closure has type:
        // `&'_ (fn(u32) -> u32)`
        // We change it to:
        // ```
        // &'_ (&u32, &u32)
        // ```
        // We also update the corresponding field accesses in the body of
        // the function.
        if let Some(body) = body {
            // Update the type of the local 1 (which is the closure)
            assert!(body.locals.vars.len() > 1);
            let state_var = &mut body.locals.vars[1];
            state_var.ty = inputs[0].clone();
            state_var.name = Some("state".to_string());

            // Update the body, and in particular the accesses to the states
            // TODO: translate to ADT field access
            // TODO: handle directly during translation
            let num_fields = info.state.len();
            body.body.dyn_visit_in_body_mut(|pe: &mut ProjectionElem| {
                if let ProjectionElem::Field(pk @ FieldProjKind::ClosureState, _) = pe {
                    *pk = FieldProjKind::Tuple(num_fields);
                }
            });
        }

        Ok(())
    } else {
        Ok(())
    }
}

pub struct Transform;
impl UllbcPass for Transform {
    fn transform_function(
        &self,
        ctx: &mut TransformCtx,
        def: &mut FunDecl,
        body: Result<&mut ExprBody, Opaque>,
    ) {
        // Ignore the errors, which should have been reported
        let _ = transform_function(ctx, def, body.ok());
    }
}
