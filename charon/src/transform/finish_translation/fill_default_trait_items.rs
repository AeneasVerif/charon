//! Fill in default assoc items in impls by copying the default value stored in the trait decl.
use crate::ast::*;
use crate::options::TranslateOptions;
use crate::transform::{TransformCtx, ctx::TransformPass};

pub struct Transform;

impl TransformPass for Transform {
    fn should_run(&self, options: &TranslateOptions) -> bool {
        // In mono mode, impls deliberately have no associated items.
        !options.monomorphize_with_hax
    }

    fn transform_ctx(&self, ctx: &mut TransformCtx) {
        for timpl in ctx.translated.trait_impls.iter_mut() {
            if !matches!(timpl.src, TraitImplSource::Normal) {
                continue;
            }
            let Some(tdecl) = ctx.translated.trait_decls.get(timpl.impl_trait.id) else {
                continue;
            };
            let self_predicate = TraitRef::new(
                TraitRefKind::TraitImpl(TraitImplRef {
                    id: timpl.def_id,
                    generics: Box::new(timpl.generics.identity_args()),
                }),
                timpl.impl_trait.clone(),
            );
            for (id, method) in tdecl.methods.iter_indexed() {
                if timpl.methods.get(id).is_none() && method.skip_binder.default.is_some() {
                    let method = method
                        .clone()
                        .substitute_with_tref(&self_predicate)
                        .map(|method| method.default.unwrap());
                    timpl.methods.set_slot_extend(id, method);
                }
            }
            for (id, ty) in tdecl.types.iter_indexed() {
                if timpl.types.get(id).is_none() && ty.skip_binder.default.is_some() {
                    let ty = ty
                        .clone()
                        .substitute_with_tref(&self_predicate)
                        .map(|ty| ty.default.unwrap());
                    timpl.types.set_slot_extend(id, ty);
                }
            }
        }
    }
}
