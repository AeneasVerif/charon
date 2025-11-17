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
            let ref_drop_arg =
                { TyKind::Ref(Region::Erased, place.ty().clone(), RefKind::Mut).into_ty() };
            let drop_arg = self.fresh_var(Some("drop_arg".into()), ref_drop_arg);
            let drop_ret = self.fresh_var(Some("drop_ret".into()), Ty::mk_unit());

            let unit_metadata = self.fresh_var(None, Ty::mk_unit());
            let rval = Rvalue::Ref {
                place: place.clone(),
                kind: BorrowKind::Mut,
                ptr_metadata: Operand::Move(unit_metadata),
            };
            // assign &mut place to drop_arg
            self.statements.push(Statement {
                span: self.span,
                kind: StatementKind::Assign(drop_arg.clone(), rval),
                comments_before: Vec::new(),
            });

            let item_name = TraitItemName("drop_in_place".into());

            match &tref.kind {
                TraitRefKind::TraitImpl(impl_ref) => {
                    let Some(item) = self.ctx.translated.get_item(impl_ref.id) else {
                        raise_error!(
                            self.ctx,
                            self.span,
                            "Could not find TraitImpl item for Destruct trait."
                        );
                    };
                    let ItemRef::TraitImpl(trait_impl) = item else {
                        raise_error!(
                            self.ctx,
                            self.span,
                            "Expected TraitImpl item for the trait item in Destruct."
                        );
                    };
                    let Some(item_binder) = trait_impl.methods().find(|&x| x.0 == item_name) else {
                        raise_error!(
                            self.ctx,
                            self.span,
                            "Could not find drop_in_place method in Destruct trait impl."
                        );
                    };
                    let method_id = item_binder.1.skip_binder.id;

                    let fn_ptr = FnPtr::new(
                        FnPtrKind::Trait(tref.clone(), item_name, method_id),
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
                    }
                }
                TraitRefKind::BuiltinOrAuto { builtin_data, .. } => {
                    match builtin_data {
                        BuiltinImplData::NoopDestruct => {
                            // Remove drop statements that are noops.
                            term.kind = TerminatorKind::Goto {
                                target: target.clone(),
                            }
                        }
                        BuiltinImplData::UntrackedDestruct => {
                            // It should not happend with --add-drop-bounds
                        }
                        _ => {
                            raise_error!(
                                self.ctx,
                                self.span,
                                "desugar_drops: Expected NoopDestruct or UntrackedDestruct kind in BuiltinOrAuto."
                            );
                        }
                    }
                }
                TraitRefKind::Clause(_) => {
                    // Call the trait method
                    let fn_ptr = FnPtr::new(
                        FnPtrKind::Trait(tref.clone(), item_name, FunDeclId::new(0)),
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
                    }
                }
                _ => {
                    raise_error!(
                        self.ctx,
                        self.span,
                        "Expected TraitImpl, BuiltinOrAuto or Clause in Drop terminator, but encounter {:?}",
                        tref.kind
                    );
                }
            }
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
