#![allow(dead_code)]
use crate::gast::{GenericArgs, ImplTraitRef, TraitItemName};
use crate::names_utils;
use crate::translate_ctx::*;
use crate::types::{ETy, GlobalDeclId};
use crate::ullbc_ast as ast;
use hax_frontend_exporter::SInto;
use rustc_hir::def_id::DefId;
use std::collections::HashMap;

impl<'tcx, 'ctx, 'ctx1> BodyTransCtx<'tcx, 'ctx, 'ctx1> {
    /// Remark: this **doesn't** register the def id (on purpose)
    /// TODO: directly use the
    pub(crate) fn translate_trait_item_name(&mut self, rust_id: DefId) -> TraitItemName {
        self.t_ctx.translate_trait_item_name(rust_id)
    }

    fn translate_ty_from_trait_item(&mut self, item: &rustc_middle::ty::AssocItem) -> ETy {
        self.translate_ety(
            &self
                .t_ctx
                .tcx
                .type_of(item.def_id)
                .subst_identity()
                .sinto(&self.hax_state),
        )
        .unwrap()
    }
    fn translate_const_from_trait_item(
        &mut self,
        item: &rustc_middle::ty::AssocItem,
    ) -> (TraitItemName, (ETy, GlobalDeclId::Id)) {
        let ty = self.translate_ty_from_trait_item(item);
        let name = TraitItemName(item.name.to_string());
        let id = self.translate_global_decl_id(item.def_id);
        (name, (ty, id))
    }

    fn add_self_trait_clause(&mut self) {
        // The self trait clause is actually the first trait predicate given by
        // [TyCtxt::predicates_of].
        // **ATTENTION**: this doesn't return the same thing as [TyCtxt::predicates_defined_on],
        // which we use elsewhere.

        // Sanity check: we should add the self trait clause before we start
        // translating the clauses.
        assert!(self.trait_clauses.is_empty());

        let predicates = self
            .t_ctx
            .tcx
            .predicates_of(self.def_id)
            .sinto(&self.hax_state);
        trace!("predicates: {:?}", predicates);
        let clause = predicates
            .predicates
            .into_iter()
            .find_map(|(pred, span)| self.translate_predicate(pred, span))
            .unwrap();
        self.self_trait_clause = Some(clause);

        // Do not forget to reinitialize
        let _ = self.clear_predicates();
    }
}

impl<'tcx, 'ctx> TransCtx<'tcx, 'ctx> {
    /// Remark: this **doesn't** register the def id (on purpose)
    pub(crate) fn translate_trait_item_name(&mut self, rust_id: DefId) -> TraitItemName {
        // Translate the name
        let name = names_utils::item_def_id_to_name(self.tcx, rust_id);
        TraitItemName(name.name.last().unwrap().as_ident().clone())
    }

    pub(crate) fn translate_trait_decl(&mut self, rust_id: DefId) {
        let def_id = self.translate_trait_decl_id(rust_id);
        let tcx = self.tcx;
        let mut bt_ctx = BodyTransCtx::new(rust_id, self);

        let name = names_utils::extended_def_id_to_name(&rust_id.sinto(&bt_ctx.hax_state));

        // Translate the generic
        let _substs = bt_ctx.translate_generics(rust_id);

        // Add the self trait clause
        bt_ctx.add_self_trait_clause();

        // Translate the predicates.
        bt_ctx.translate_predicates_of(rust_id);
        // Retrieve the current trait clauses, which apply to the trait decl
        // itself (we will continue appending the ones from the associated items
        // in bt_ctx).
        let mut trait_clauses = bt_ctx.trait_clauses.clone();
        let mut trait_clauses_start_index = bt_ctx.trait_clauses.len();

        trace!("- trait id: {:?}\n- trait name: {:?}", rust_id, name);
        trace!("Trait predicates: {:?}", tcx.predicates_of(rust_id));

        // Explore the associated items
        // We do something subtle here: TODO
        let tcx = bt_ctx.t_ctx.tcx;
        let mut consts = Vec::new();
        let mut types = Vec::new();
        let mut required_methods = Vec::new();
        let mut provided_methods = Vec::new();
        for item in tcx.associated_items(rust_id).in_definition_order() {
            use rustc_middle::ty::AssocKind;

            let has_default_value = item.defaultness(tcx).has_value();
            // Skip the provided methods for the trait declarations, but still
            // remember their name.
            if item.kind == AssocKind::Fn && has_default_value {
                let name = bt_ctx.t_ctx.translate_trait_item_name(item.def_id);
                provided_methods.push(name);
                continue;
            }

            match &item.kind {
                AssocKind::Fn => {
                    let method_name = bt_ctx.t_ctx.translate_trait_item_name(item.def_id);
                    let fun_id = bt_ctx.translate_fun_decl_id(item.def_id);
                    required_methods.push((method_name, fun_id));
                }
                AssocKind::Const => {
                    // Check if the constant has a value (i.e., a body).
                    // We are handling a trait *declaration* so we need to
                    // check whether the constant has a default value.
                    trace!("id: {:?}\n- item: {:?}", rust_id, item);
                    let c = if has_default_value {
                        let (name, (ty, id)) = bt_ctx.translate_const_from_trait_item(item);
                        (name, (ty, Some(id)))
                    } else {
                        let ty = bt_ctx.translate_ty_from_trait_item(item);
                        let name = TraitItemName(item.name.to_string());
                        (name, (ty, None))
                    };
                    consts.push(c);
                }
                AssocKind::Type => {
                    let name = TraitItemName(item.name.to_string());

                    // Translating the predicates
                    // TODO: this is an ugly manip
                    let bounds = tcx.item_bounds(item.def_id).subst_identity();
                    use crate::rustc_middle::query::Key;
                    let span = bounds.default_span(tcx);
                    let bounds: Vec<_> = bounds.into_iter().map(|x| (x, span)).collect();
                    let bounds = bounds.sinto(&bt_ctx.hax_state);
                    bt_ctx.translate_predicates_vec(bounds);

                    // Retreive the trait clauses
                    let mut trait_clauses = Vec::new();
                    for i in trait_clauses_start_index..bt_ctx.trait_clauses.len() {
                        trait_clauses.push(bt_ctx.trait_clauses.vector.get(i).unwrap().clone());
                    }
                    trait_clauses_start_index = bt_ctx.trait_clauses.len();

                    let ty = if has_default_value {
                        Some(bt_ctx.translate_ty_from_trait_item(item))
                    } else {
                        None
                    };

                    types.push((name, (trait_clauses, ty)));
                }
            }
        }

        // We need to make a small manipulation: the generics stored in the bt_ctx contain
        // the trait clauses for the trait decl itself but also for its associated types.
        // We need to exchange those with the trait clauses we computed above.
        let mut generics = bt_ctx.get_generics();
        std::mem::swap(&mut generics.trait_clauses, &mut trait_clauses);

        // In case of a trait implementation, some values may not have been
        // provided, in case the declaration provided default values. We
        // check those, and lookup the relevant values.
        let trait_decl = ast::TraitDecl {
            def_id,
            name,
            generics,
            all_trait_clauses: trait_clauses,
            consts,
            types,
            required_methods,
            provided_methods,
        };
        self.trait_decls.insert(def_id, trait_decl)
    }

    pub(crate) fn translate_trait_impl(&mut self, rust_id: DefId) {
        let def_id = self.translate_trait_impl_id(rust_id);
        let tcx = self.tcx;
        let mut bt_ctx = BodyTransCtx::new(rust_id, self);

        let name = names_utils::extended_def_id_to_name(&rust_id.sinto(&bt_ctx.hax_state));

        // Translate the generics
        let _substs = bt_ctx.translate_generics(rust_id);

        // Translate the predicates
        bt_ctx.translate_predicates_of(rust_id);

        trace!("- trait id: {:?}\n- trait name: {:?}", rust_id, name);
        trace!("Trait predicates: {:?}", tcx.predicates_of(rust_id));

        // Retrieve the information about the implemented trait.
        let (impl_trait_rust_id, impl_trait) =
            if let rustc_hir::def::DefKind::Impl { .. } = tcx.def_kind(rust_id) {
                let trait_rust_id = tcx.trait_id_of_impl(rust_id).unwrap();
                let trait_id = bt_ctx.translate_trait_decl_id(trait_rust_id);
                let rustc_middle::ty::ImplSubject::Trait(trait_ref) =
                    tcx.impl_subject(rust_id).subst_identity() else { unreachable!() };
                let trait_ref = trait_ref.sinto(&bt_ctx.hax_state);
                let (regions, types, const_generics) = bt_ctx
                    .translate_substs(None, &trait_ref.generic_args)
                    .unwrap();
                let generics = GenericArgs {
                    regions,
                    types,
                    const_generics,
                    trait_refs: Vec::new(),
                };
                let trait_ref = ImplTraitRef { trait_id, generics };
                (trait_rust_id, trait_ref)
            } else {
                unreachable!()
            };

        // Explore the associated items
        // We do something subtle here: TODO
        let tcx = bt_ctx.t_ctx.tcx;
        let mut consts = HashMap::new();
        let mut types = HashMap::new();
        let mut required_methods = Vec::new();
        let mut provided_methods = Vec::new();

        use rustc_middle::ty::AssocKind;
        for item in tcx.associated_items(rust_id).in_definition_order() {
            let has_default_value = item.defaultness(tcx).has_value();
            match &item.kind {
                AssocKind::Fn => {
                    let method_name = bt_ctx.t_ctx.translate_trait_item_name(item.def_id);
                    let fun_id = bt_ctx.translate_fun_decl_id(item.def_id);

                    // Check if we implement a required method or reimplement
                    // a provided method
                    if has_default_value {
                        provided_methods.push((method_name, fun_id));
                    } else {
                        required_methods.push((method_name, fun_id));
                    }
                }
                AssocKind::Const => {
                    let (name, c) = bt_ctx.translate_const_from_trait_item(item);
                    consts.insert(name, c);
                }
                AssocKind::Type => {
                    let name = TraitItemName(item.name.to_string());
                    let ty = bt_ctx.translate_ty_from_trait_item(item);
                    types.insert(name, ty);
                }
            }
        }

        // In case of a trait implementation, some values may not have been
        // provided, in case the declaration provided default values. We
        // check those, and lookup the relevant values.
        let partial_consts = consts;
        let partial_types = types;
        let mut consts = Vec::new();
        let mut types = Vec::new();
        // TODO: types
        for item in tcx
            .associated_items(impl_trait_rust_id)
            .in_definition_order()
        {
            match &item.kind {
                AssocKind::Fn => (),
                AssocKind::Const => {
                    let name = TraitItemName(item.name.to_string());
                    let c = match partial_consts.get(&name) {
                        Some(c) => c.clone(),
                        None => {
                            // The item is not defined in the trait impl:
                            // the trait decl *must* define a default value.
                            bt_ctx.translate_const_from_trait_item(item).1
                        }
                    };
                    consts.push((name, c));
                }
                AssocKind::Type => {
                    let name = TraitItemName(item.name.to_string());
                    let ty = match partial_types.get(&name) {
                        Some(ty) => ty.clone(),
                        None => {
                            // The item is not defined in the trait impl:
                            // the trait decl *must* define a default value.
                            bt_ctx.translate_ty_from_trait_item(item)
                        }
                    };
                    types.push((name, ty));
                }
            }
        }

        let trait_impl = ast::TraitImpl {
            def_id,
            name,
            impl_trait,
            generics: bt_ctx.get_generics(),
            consts,
            types,
            required_methods,
            provided_methods,
        };
        self.trait_impls.insert(def_id, trait_impl)
    }
}
