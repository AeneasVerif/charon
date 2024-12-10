//! # Micro-pass: the first local variable of closures is (a borrow to) the
//! closure itself. This is not consistent with the closure signature,
//! which ignores this first variable. This micro-pass updates this.
use derive_visitor::{visitor_enter_fn_mut, DriveMut, VisitorMut};

use crate::ids::Vector;
use crate::transform::TransformCtx;
use crate::ullbc_ast::*;

use super::ctx::UllbcPass;

#[derive(VisitorMut)]
#[visitor(Region(exit), Ty(enter, exit))]
struct InsertRegions<'a> {
    regions: &'a mut Vector<RegionId, RegionVar>,
    // The number of region groups we dived into (we don't count the regions
    // at the declaration level). We use this for the DeBruijn indices.
    depth: usize,
}

impl<'a> InsertRegions<'a> {
    fn exit_region(&mut self, r: &mut Region) {
        if r == &Region::Erased {
            // Insert a fresh region
            let index = self
                .regions
                .push_with(|index| RegionVar { index, name: None });
            *r = Region::Var(DeBruijnVar::bound(DeBruijnId::new(self.depth), index));
        }
    }

    fn enter_ty(&mut self, ty: &mut Ty) {
        if let TyKind::Arrow(..) = ty.kind() {
            self.depth += 1;
        }
    }

    fn exit_ty(&mut self, ty: &mut Ty) {
        if let TyKind::Arrow(..) = ty.kind() {
            self.depth -= 1;
        }
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
        // Update the signature.
        // We add as first parameter the state of the closure, that is
        // a borrow to a tuple (of borrows, usually).
        // Remark: the types used in the closure state may contain erased
        // regions. In particular, the regions coming from the parent
        // function are often erased. TODO:
        // However, we introduce fresh regions for the state (in particular
        // because it is easy to do so).

        // Group the types into a tuple
        let num_fields = info.state.len();
        let state = TyKind::Adt(
            TypeId::Tuple,
            GenericArgs::new_from_types(info.state.clone()),
        )
        .into_ty();
        // Depending on the kind of the closure, add a reference
        let mut state = match &info.kind {
            ClosureKind::FnOnce => state,
            ClosureKind::Fn | ClosureKind::FnMut => {
                // We introduce an erased region, that we replace later
                //let index = RegionId::new(generics.regions.len());
                //generics.regions.push_back(RegionVar { index, name: None });

                let mutability = if info.kind == ClosureKind::Fn {
                    RefKind::Shared
                } else {
                    RefKind::Mut
                };
                //let r = Region::BVar(DeBruijnId::new(0), index);
                TyKind::Ref(Region::Erased, state, mutability).into_ty()
            }
        };

        // Explore the state and introduce fresh regions for the erased
        // regions we find.
        let mut visitor = Ty::visit_inside(InsertRegions {
            regions: &mut generics.regions,
            depth: 0,
        });
        state.drive_mut(&mut visitor);

        // Update the inputs (slightly annoying to push to the front of
        // a vector...).
        let mut original_inputs = std::mem::take(inputs);
        let mut ninputs = vec![state.clone()];
        ninputs.append(&mut original_inputs);
        *inputs = ninputs;

        // Update the body.
        // We change the type of the local variable of index 1, which is
        // a reference to the closure itself, so that it has the type of
        // (a reference to) the state of the closure.
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
            body.locals.arg_count += 1;

            // Update the type of the local 1 (which is the closure)
            assert!(body.locals.vars.len() > 1);
            let state_var = &mut body.locals.vars[1];
            state_var.ty = state;
            state_var.name = Some("state".to_string());

            // Update the body, and in particular the accesses to the states
            body.body
                .drive_mut(&mut visitor_enter_fn_mut(|pe: &mut ProjectionElem| {
                    if let ProjectionElem::Field(pk @ FieldProjKind::ClosureState, _) = pe {
                        *pk = FieldProjKind::Tuple(num_fields);
                    }
                }));
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
