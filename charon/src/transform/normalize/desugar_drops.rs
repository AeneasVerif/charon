use super::super::ctx::UllbcPass;
use crate::{
    errors::Error,
    raise_error, register_error,
    transform::{
        TransformCtx,
        ctx::{BodyTransformCtx, UllbcStatementTransformCtx},
    },
    ullbc_ast::*,
};

fn is_noop_destruct(tref: &TraitRef) -> bool {
    matches!(
        &tref.kind,
        TraitRefKind::BuiltinOrAuto {
            builtin_data: BuiltinImplData::NoopDestruct,
            ..
        }
    )
}

impl<'a> UllbcStatementTransformCtx<'a> {
    /// Transform a Drop to a Call that calls the drop_in_place method.
    fn transform_drop_to_call(&mut self, term: &mut Terminator) -> Result<(), Error> {
        if let TerminatorKind::Drop {
            place,
            tref,
            target,
            on_unwind,
        } = &mut term.kind
        {
            // check if this drop is noop
            if is_noop_destruct(tref) {
                term.kind = TerminatorKind::Goto {
                    target: target.clone(),
                };
                return Ok(());
            }

            let ref_drop_arg = TyKind::RawPtr(place.ty().clone(), RefKind::Mut).into_ty();
            let drop_arg = self.fresh_var(Some("drop_arg".into()), ref_drop_arg);
            let drop_ret = self.fresh_var(Some("drop_ret".into()), Ty::mk_unit());

            let ptr_metadata = self.compute_place_metadata(&place);
            let rval = Rvalue::RawPtr {
                place: place.clone(),
                kind: RefKind::Mut,
                ptr_metadata: ptr_metadata,
            };
            // assign &raw mut place to drop_arg
            self.insert_assn_stmt(drop_arg.clone(), rval);

            // Get the declaration id of drop_in_place from tref
            let trait_id = tref.trait_decl_ref.skip_binder.id;
            let Some(tdecl) = self.ctx.translated.trait_decls.get(trait_id) else {
                return Ok(());
            };
            let method_name = TraitItemName("drop_in_place".into());
            let Some(bound_method) = tdecl.methods.iter().find(|m| m.name() == method_name) else {
                raise_error!(
                    self.ctx,
                    self.span,
                    "Could not find a method with name \
                    `{method_name}` in trait `{:?}`",
                    trait_id,
                )
            };
            let method_decl_id = bound_method.skip_binder.item.id;

            let fn_ptr = FnPtr::new(
                FnPtrKind::Trait(tref.clone(), method_name, method_decl_id),
                GenericArgs::empty(),
            );
            let call = Call {
                func: FnOperand::Regular(fn_ptr),
                args: Vec::from([Operand::Move(drop_arg)]),
                dest: drop_ret,
            };
            term.kind = TerminatorKind::Call {
                call,
                target: target.clone(),
                on_unwind: on_unwind.clone(),
            };
        }
        Ok(())
    }
}

pub struct Transform;

impl UllbcPass for Transform {
    fn transform_function(&self, ctx: &mut TransformCtx, decl: &mut FunDecl) {
        if !ctx.options.desugar_drops {
            return;
        }
        decl.transform_ullbc_terminators(ctx, |ctx, term| {
            let _ = ctx.transform_drop_to_call(term);
        });
    }
}
