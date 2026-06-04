//! `--duplicate-defaulted-methods`: copy trait default methods into impls that use them.
use crate::ast::*;
use crate::options::TranslateOptions;
use crate::transform::{TransformCtx, ctx::TransformPass};

pub struct Transform;

impl Transform {
    fn prepare_defaulted_method_duplicate(
        ctx: &TransformCtx,
        trait_impl: &TraitImpl,
        method_id: TraitMethodId,
        method: &Binder<FunDeclRef>,
    ) -> Option<(FunDecl, Binder<GenericArgs>)> {
        let original_method_id = method.skip_binder.id;
        let original_method = ctx.translated.fun_decls.get(original_method_id)?;
        let ItemSource::TraitDecl {
            item_id,
            has_default: true,
            ..
        } = &original_method.src
        else {
            return None;
        };
        let item_id = *item_id;
        let original_method = original_method.clone();
        let method_name = ctx
            .translated
            .assoc_item_name(trait_impl.impl_trait.id, method_id);
        let mut name = ctx.translated.item_name(trait_impl.def_id).clone();
        name.name.push(PathElem::Ident(
            method_name.to_string(),
            Disambiguator::ZERO,
        ));

        // Flatten the impl binder and the method binder. The resulting substitution maps the
        // trait default method into the generic context of the duplicated impl method.
        let subst: Binder<FunDeclRef> = Binder {
            params: trait_impl.generics.clone(),
            skip_binder: method.clone(),
            kind: BinderKind::Other,
        }
        .flatten();
        let mut fun_decl = original_method.substitute_params(subst.map(|x| *x.generics));

        let ItemSource::TraitDecl { trait_ref, .. } = fun_decl.src else {
            unreachable!()
        };
        fun_decl.def_id = FunDeclId::MAX; // We fix it up on insertion
        fun_decl.item_meta = ItemMeta {
            name,
            opacity: trait_impl.item_meta.opacity,
            is_local: trait_impl.item_meta.is_local,
            span: trait_impl.item_meta.span,
            source_text: fun_decl.item_meta.source_text,
            attr_info: fun_decl.item_meta.attr_info,
            lang_item: fun_decl.item_meta.lang_item,
        };
        fun_decl.src = ItemSource::TraitImpl {
            impl_ref: TraitImplRef {
                id: trait_impl.def_id,
                generics: Box::new(trait_impl.generics.identity_args()),
            },
            trait_ref,
            item_id,
            reuses_default: true,
        };
        if !trait_impl.item_meta.opacity.is_transparent() {
            fun_decl.body = Body::Opaque;
        }

        let generics = trait_impl
            .generics
            .identity_args_at_depth(DeBruijnId::one())
            .concat(&method.params.identity_args_at_depth(DeBruijnId::zero()));
        let generics = method.map_ref(|_| generics);

        Some((fun_decl, generics))
    }
}

impl TransformPass for Transform {
    fn should_run(&self, options: &TranslateOptions) -> bool {
        options.duplicate_defaulted_methods
    }

    fn transform_ctx(&self, ctx: &mut TransformCtx) {
        let duplicated_methods: IndexMap<
            TraitImplId,
            Vec<(TraitMethodId, FunDecl, Binder<GenericArgs>)>,
        > = ctx.translated.trait_impls.map_ref(|trait_impl| {
            trait_impl
                .methods
                .iter_indexed()
                .filter_map(|(method_id, method)| {
                    let (fun_decl, generics) = Transform::prepare_defaulted_method_duplicate(
                        ctx, trait_impl, method_id, method,
                    )?;
                    Some((method_id, fun_decl, generics))
                })
                .collect()
        });

        let mut methods_to_insert: Vec<(TraitMethodId, Binder<FunDeclRef>)> = Vec::new();
        for (trait_impl_id, duplicates) in duplicated_methods.into_iter_indexed() {
            if duplicates.is_empty() {
                continue;
            }
            for (method_id, mut fun_decl, generics) in duplicates {
                let new_id = ctx.translated.fun_decls.reserve_slot();
                fun_decl.def_id = new_id;
                // Takes care of adding to the names map as well.
                ctx.translated
                    .set_new_item_slot(ItemId::Fun(new_id), ItemByVal::Fun(fun_decl));

                let method = generics.map(|generics| FunDeclRef {
                    id: new_id,
                    generics: Box::new(generics),
                });
                methods_to_insert.push((method_id, method));
            }
            let Some(trait_impl) = ctx.translated.trait_impls.get_mut(trait_impl_id) else {
                continue;
            };
            for (method_id, method) in methods_to_insert.drain(..) {
                trait_impl.methods.insert(method_id, method);
            }
        }
    }
}
