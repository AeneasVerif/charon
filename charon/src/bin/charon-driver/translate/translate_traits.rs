use super::translate_ctx::*;
use annotate_snippets::Level;
use charon_lib::ast::*;
use charon_lib::formatter::IntoFormatter;
use charon_lib::meta::ItemMeta;
use charon_lib::pretty::FmtWithCtx;
use charon_lib::ullbc_ast as ast;
use hax_frontend_exporter as hax;
use itertools::Itertools;
use rustc_hir::def_id::DefId;
use std::collections::HashMap;
use std::mem;
use std::sync::Arc;

/// The context in which we are translating a clause, used to generate the appropriate ids and
/// trait references.
pub(crate) enum PredicateLocation {
    /// We're translating the parent clauses of this trait.
    Parent,
    /// We're translating the item clauses of this trait.
    Item(TraitItemName),
    /// We're translating anything else.
    Base,
}

impl<'tcx, 'ctx> TranslateCtx<'tcx> {
    /// Remark: this **doesn't** register the def id (on purpose)
    pub(crate) fn translate_trait_item_name(
        &mut self,
        def_id: &hax::DefId,
    ) -> Result<TraitItemName, Error> {
        // Translate the name
        let name = self.hax_def_id_to_name(def_id)?;
        let (name, id) = name.name.last().unwrap().as_ident().unwrap();
        assert!(id.is_zero());
        Ok(TraitItemName(name.to_string()))
    }
}

impl BodyTransCtx<'_, '_> {
    #[tracing::instrument(skip(self, rust_id, item_meta))]
    pub fn translate_trait_decl(
        mut self,
        def_id: TraitDeclId,
        rust_id: DefId,
        item_meta: ItemMeta,
        def: &hax::FullDef,
    ) -> Result<TraitDecl, Error> {
        trace!("About to translate trait decl:\n{:?}", rust_id);
        trace!("Trait decl id:\n{:?}", def_id);

        let span = item_meta.span;

        if let hax::FullDefKind::TraitAlias { .. } = def.kind() {
            error_or_panic!(self, span, &format!("Trait aliases are not supported"));
        }

        let hax::FullDefKind::Trait { items, .. } = &def.kind else {
            error_or_panic!(self, span, &format!("Unexpected definition: {def:?}"));
        };
        let items: Vec<(TraitItemName, &hax::AssocItem, Arc<hax::FullDef>)> = items
            .iter()
            .map(|(item, def)| {
                let name = TraitItemName(item.name.clone());
                (name, item, def.clone())
            })
            .collect_vec();

        // Translate the generics
        // Note that in the generics returned by [translate_def_generics], the trait refs only
        // contain the local trait clauses. The parent clauses are stored in
        // `self.parent_trait_clauses`.
        // TODO: Distinguish between required and implied trait clauses?
        self.translate_def_generics(span, def)?;

        // Translate the associated items
        // We do something subtle here: TODO: explain
        let mut consts = Vec::new();
        let mut const_defaults = HashMap::new();
        let mut types = Vec::new();
        let mut type_clauses = Vec::new();
        let mut type_defaults = HashMap::new();
        let mut required_methods = Vec::new();
        let mut provided_methods = Vec::new();
        for (item_name, hax_item, hax_def) in &items {
            let item_def_id = DefId::from(&hax_item.def_id);
            let item_span = self.def_span(item_def_id);
            match &hax_def.kind {
                hax::FullDefKind::AssocFn { .. } => {
                    let fun_def = self.t_ctx.hax_def(item_def_id)?;
                    let fn_ref = self.translate_binder_for_def(item_span, &fun_def, |bt_ctx| {
                        let fun_id = bt_ctx.register_fun_decl_id(item_span, item_def_id);
                        // TODO: there's probably a cleaner way to write this
                        assert_eq!(bt_ctx.binding_levels.len(), 2);
                        let fun_generics = bt_ctx
                            .outermost_binder()
                            .params
                            .identity_args_at_depth(DeBruijnId::one())
                            .concat(
                                &bt_ctx
                                    .innermost_binder()
                                    .params
                                    .identity_args_at_depth(DeBruijnId::zero()),
                            );
                        Ok(FunDeclRef {
                            id: fun_id,
                            generics: fun_generics,
                        })
                    })?;
                    if hax_item.has_value {
                        // This is a provided method,
                        provided_methods.push((item_name.clone(), fn_ref));
                    } else {
                        // This is a required method (no default implementation)
                        required_methods.push((item_name.clone(), fn_ref));
                    }
                }
                hax::FullDefKind::AssocConst { ty, .. } => {
                    // Check if the constant has a value (i.e., a body).
                    if hax_item.has_value {
                        // The parameters of the constant are the same as those of the item that
                        // declares them.
                        let gref = GlobalDeclRef {
                            id: self.register_global_decl_id(item_span, item_def_id),
                            generics: self.the_only_binder().params.identity_args(),
                        };
                        const_defaults.insert(item_name.clone(), gref);
                    };
                    let ty = self.translate_ty(item_span, ty)?;
                    consts.push((item_name.clone(), ty));
                }
                hax::FullDefKind::AssocTy { generics, .. } if !generics.params.is_empty() => {
                    error_or_panic!(
                        self,
                        item_span,
                        &format!("Generic associated types are not supported")
                    );
                }
                hax::FullDefKind::AssocTy { value, .. } => {
                    // TODO: handle generics (i.e. GATs).
                    if let Some(clauses) = self.item_trait_clauses.get(item_name) {
                        type_clauses.push((item_name.clone(), clauses.clone()));
                    }
                    if let Some(ty) = value {
                        let ty = self.translate_ty(item_span, &ty)?;
                        type_defaults.insert(item_name.clone(), ty);
                    };
                    types.push(item_name.clone());
                }
                _ => panic!("Unexpected definition for trait item: {hax_def:?}"),
            }
        }

        if item_meta.opacity.is_opaque() {
            let ctx = self.into_fmt();
            self.t_ctx.errors.display_error(
                &self.t_ctx.translated,
                item_meta.span,
                Level::Warning,
                format!(
                    "Trait declarations cannot be \"opaque\"; the trait `{}` will be translated as normal.",
                    item_meta.name.fmt_with_ctx(&ctx)
                ),
            )
        }
        // In case of a trait implementation, some values may not have been
        // provided, in case the declaration provided default values. We
        // check those, and lookup the relevant values.
        Ok(ast::TraitDecl {
            def_id,
            item_meta,
            parent_clauses: mem::take(&mut self.parent_trait_clauses),
            generics: self.into_generics(),
            type_clauses,
            consts,
            const_defaults,
            types,
            type_defaults,
            required_methods,
            provided_methods,
        })
    }

    #[tracing::instrument(skip(self, rust_id, item_meta))]
    pub fn translate_trait_impl(
        mut self,
        def_id: TraitImplId,
        rust_id: DefId,
        item_meta: ItemMeta,
        def: &hax::FullDef,
    ) -> Result<TraitImpl, Error> {
        trace!("About to translate trait impl:\n{:?}", rust_id);
        trace!("Trait impl id:\n{:?}", def_id);

        let span = item_meta.span;

        self.translate_def_generics(span, def)?;

        let hax::FullDefKind::TraitImpl {
            trait_pred,
            required_impl_exprs,
            items: impl_items,
            ..
        } = &def.kind
        else {
            unreachable!()
        };

        // Retrieve the information about the implemented trait.
        let implemented_trait_id = &trait_pred.trait_ref.def_id;
        let trait_id = self.register_trait_decl_id(span, implemented_trait_id);
        let implemented_trait = {
            let implemented_trait = &trait_pred.trait_ref;
            let generics =
                self.translate_generic_args(span, &implemented_trait.generic_args, &[], None)?;
            TraitDeclRef { trait_id, generics }
        };

        // The trait refs which implement the parent clauses of the implemented trait decl.
        let parent_trait_refs = self.translate_trait_impl_exprs(span, &required_impl_exprs)?;

        {
            // Debugging
            let ctx = self.into_fmt();
            let refs = parent_trait_refs
                .iter()
                .map(|c| c.fmt_with_ctx(&ctx))
                .collect::<Vec<String>>()
                .join("\n");
            trace!("Trait impl: {:?}\n- parent_trait_refs:\n{}", rust_id, refs);
        }

        // Explore the associated items
        let mut consts = Vec::new();
        let mut types: Vec<(TraitItemName, Ty)> = Vec::new();
        let mut required_methods = Vec::new();
        let mut provided_methods = Vec::new();
        let mut type_clauses = Vec::new();

        for impl_item in impl_items {
            use hax::ImplAssocItemValue::*;
            let name = TraitItemName(impl_item.name.clone());
            let item_def = impl_item.def(); // The impl item or the corresponding trait default.
            let item_span = self.def_span(item_def.rust_def_id());
            let item_def_id = item_def.rust_def_id();
            match item_def.kind() {
                hax::FullDefKind::AssocFn { .. } => {
                    let fun_id = self.register_fun_decl_id(item_span, item_def_id);
                    match &impl_item.value {
                        Provided { is_override, .. } => {
                            let fun_def = self.t_ctx.hax_def(item_def_id)?;
                            let fn_ref =
                                self.translate_binder_for_def(item_span, &fun_def, |bt_ctx| {
                                    // TODO: there's probably a cleaner way to write this
                                    assert_eq!(bt_ctx.binding_levels.len(), 2);
                                    let fun_generics = bt_ctx
                                        .outermost_binder()
                                        .params
                                        .identity_args_at_depth(DeBruijnId::one())
                                        .concat(
                                            &bt_ctx
                                                .innermost_binder()
                                                .params
                                                .identity_args_at_depth(DeBruijnId::zero()),
                                        );
                                    Ok(FunDeclRef {
                                        id: fun_id,
                                        generics: fun_generics,
                                    })
                                })?;
                            if *is_override {
                                provided_methods.push((name, fn_ref));
                            } else {
                                required_methods.push((name, fn_ref));
                            }
                        }
                        DefaultedFn { .. } => {
                            // TODO: handle defaulted methods
                        }
                        _ => unreachable!(),
                    }
                }
                hax::FullDefKind::AssocConst { .. } => {
                    let id = self.register_global_decl_id(item_span, item_def_id);
                    // The parameters of the constant are the same as those of the item that
                    // declares them.
                    let generics = match &impl_item.value {
                        Provided { .. } => self.the_only_binder().params.identity_args(),
                        _ => implemented_trait.generics.clone(),
                    };
                    let gref = GlobalDeclRef { id, generics };
                    consts.push((name, gref));
                }
                hax::FullDefKind::AssocTy { generics, .. } if !generics.params.is_empty() => {
                    // We don't support GATs; the error was already reported in the trait declaration.
                }
                hax::FullDefKind::AssocTy { value, .. } => {
                    let ty = match &impl_item.value {
                        Provided { .. } => value.as_ref().unwrap(),
                        DefaultedTy { ty, .. } => ty,
                        _ => unreachable!(),
                    };
                    let ty = self.translate_ty(item_span, &ty)?;
                    types.push((name.clone(), ty));

                    let trait_refs =
                        self.translate_trait_impl_exprs(item_span, &impl_item.required_impl_exprs)?;
                    type_clauses.push((name, trait_refs));
                }
                _ => panic!("Unexpected definition for trait item: {item_def:?}"),
            }
        }

        if item_meta.opacity.is_opaque() {
            let ctx = self.into_fmt();
            self.t_ctx.errors.display_error(
                &self.t_ctx.translated,
                item_meta.span,
                Level::Warning,
                format!(
                    "Trait implementations cannot be \"opaque\"; the impl `{}` will be translated as normal.",
                    item_meta.name.fmt_with_ctx(&ctx)
                ),
            )
        }

        Ok(ast::TraitImpl {
            def_id,
            item_meta,
            impl_trait: implemented_trait,
            generics: self.into_generics(),
            parent_trait_refs,
            type_clauses,
            consts,
            types,
            required_methods,
            provided_methods,
        })
    }
}
