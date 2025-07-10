use super::translate_ctx::*;
use charon_lib::ast::*;
use hax_frontend_exporter as hax;

impl ItemTransCtx<'_, '_> {
    pub fn check_at_most_one_pred_has_methods(
        &self,
        span: Span,
        preds: &Vec<hax::Binder<hax::ExistentialPredicate>>,
    ) -> Result<(), Error> {
        let all_ex_trait_ref = preds.iter().filter_map(|bound| {
            if let hax::ExistentialPredicate::Trait(trait_ref) = &bound.value {
                Some(trait_ref)
            } else {
                None
            }
        });
        if all_ex_trait_ref.count() > 1 {
            raise_error!(
                self,
                span,
                "`dyn Trait` with multiple method-bearing predicates is not supported"
            );
        }
        Ok(())
    }

    /// Translate generics for an exitential predicate. These generics are missing a `Self` type,
    /// which we add here, represented with `ExistentialPlaceholder`.
    fn translate_ex_generics(
        &mut self,
        span: Span,
        args: &[hax::GenericArg],
    ) -> Result<Box<GenericArgs>, Error> {
        let mut generics = Box::new(self.translate_generic_args(span, args, &[])?);
        generics.types.insert_and_shift_ids(
            TypeVarId::from_usize(0),
            TyKind::ExistentialPlaceholder.into_ty(),
        );
        Ok(generics)
    }

    pub fn translate_existential_predicate(
        &mut self,
        span: Span,
        pred: &hax::ExistentialPredicate,
    ) -> Result<DynPredicate, Error> {
        Ok(match pred {
            hax::ExistentialPredicate::Trait(tref) => DynPredicate::Trait(TraitDeclRef {
                id: self.register_trait_decl_id(span, &tref.def_id),
                generics: self.translate_ex_generics(span, &tref.args)?,
            }),
            hax::ExistentialPredicate::AutoTrait(def_id) => {
                let trait_id = self.register_trait_decl_id(span, def_id);
                let ty = TyKind::ExistentialPlaceholder.into_ty();
                let tref = TraitDeclRef {
                    id: trait_id,
                    generics: Box::new(GenericArgs::new_types([ty].into())),
                };
                DynPredicate::Trait(tref)
            }
            hax::ExistentialPredicate::Projection(proj) => {
                // TODO: this is incorrect if the projection doesn't apply to the principal.
                let args = self.translate_ex_generics(span, &proj.args)?;
                let name = self.t_ctx.translate_trait_item_name(&proj.def_id)?;
                let term = match &proj.term {
                    hax::Term::Ty(ty) => self.translate_ty(span, ty)?,
                    hax::Term::Const(_) => {
                        raise_error!(
                            self,
                            span,
                            "`dyn Trait` with associated const constraints are not supported",
                        )
                    }
                };
                DynPredicate::Projection(DynTypeConstraint {
                    trait_item: name,
                    generics: args,
                    term,
                })
            }
        })
    }
}
