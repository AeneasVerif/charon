//! # Micro-pass: the first local variable of closures is (a borrow to) the
//! closure itself. This is not consistent with the closure signature,
//! which ignores this first variable. This micro-pass updates this.
use crate::common::*;
use crate::llbc_ast::*;
use crate::translate_ctx::TransCtx;
use crate::types::*;

struct InsertRegions<'a> {
    regions: &'a mut RegionId::Vector<RegionVar>,
    /// The number of region groups we dived into (we don't count the regions
    /// at the declaration level). We use this for the DeBruijn indices.
    depth: usize,
}

impl<'a> MutTypeVisitor for InsertRegions<'a> {
    fn visit_region(&mut self, r: &mut Region) {
        if r == &Region::Erased {
            // Insert a fresh region
            let index = self
                .regions
                .push_with(|index| RegionVar { index, name: None });
            *r = Region::BVar(DeBruijnId::new(self.depth), index);
        }
    }

    fn enter_region_group(
        &mut self,
        _regions: &mut RegionId::Vector<RegionVar>,
        visitor: &mut dyn FnMut(&mut Self),
    ) {
        self.depth += 1;
        visitor(self);
        self.depth -= 1;
    }
}

struct ClosureStateAccess {
    num_fields: usize,
}

impl MutTypeVisitor for ClosureStateAccess {}

impl MutExprVisitor for ClosureStateAccess {
    fn visit_projection_elem(&mut self, pe: &mut ProjectionElem) {
        if let ProjectionElem::Field(pk @ FieldProjKind::ClosureState, _) = pe {
            *pk = FieldProjKind::Tuple(self.num_fields);
        } else {
            self.default_visit_projection_elem(pe)
        }
    }
}

impl MutAstVisitor for ClosureStateAccess {
    fn spawn(&mut self, visitor: &mut dyn FnMut(&mut Self)) {
        visitor(self)
    }

    fn merge(&mut self) {}
}

fn transform_function(_ctx: &TransCtx, def: &mut FunDecl) -> Result<(), Error> {
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
        let state = Ty::Adt(
            TypeId::Tuple,
            GenericArgs::new_from_types(info.state.clone()),
        );
        // Depending on the kind of the closure, add a reference
        let mut state = match &info.kind {
            ClosureKind::FnOnce => state,
            ClosureKind::Fn | ClosureKind::FnMut => {
                // We introduce an erased region, that we replace later
                //let index = RegionId::Id::new(generics.regions.len());
                //generics.regions.push_back(RegionVar { index, name: None });

                let mutability = if info.kind == ClosureKind::Fn {
                    RefKind::Shared
                } else {
                    RefKind::Mut
                };
                //let r = Region::BVar(DeBruijnId::new(0), index);
                Ty::Ref(Region::Erased, Box::new(state), mutability)
            }
        };

        // Explore the state and introduce fresh regions for the erased
        // regions we find.
        let mut visitor = InsertRegions {
            regions: &mut generics.regions,
            depth: 0,
        };
        visitor.visit_ty(&mut state);

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

        if let Some(body) = &mut def.body {
            body.arg_count += 1;

            // Update the type of the local 1 (which is the closure)
            assert!(body.locals.len() > 1);
            let state_var = &mut body.locals[1];
            state_var.ty = state;
            state_var.name = Some("state".to_string());

            // Update the body, and in particular the accesses to the states
            let mut visitor = ClosureStateAccess { num_fields };
            visitor.visit_statement(&mut body.body);
        }

        Ok(())
    } else {
        Ok(())
    }
}

pub fn transform(ctx: &TransCtx, funs: &mut FunDecls) {
    // Ignore the errors, which should have been reported
    funs.iter_mut().for_each(|d| {
        let _ = transform_function(ctx, d);
    });
}
