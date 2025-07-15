use std::mem;
use std::ops::ControlFlow::Continue;

use crate::translate::translate_bodies::BodyTransCtx;
use crate::translate::translate_types;

use crate::translate::{translate_generics::BindingLevel, translate_predicates::PredicateLocation};

use super::translate_ctx::*;
use charon_lib::ast::*;
use hax_frontend_exporter as hax;
use petgraph::matrix_graph::Zero;

use super::translate_ctx::*;
use charon_lib::ast::*;
use charon_lib::formatter::IntoFormatter;
use charon_lib::ids::Vector;
use charon_lib::pretty::FmtWithCtx;
use charon_lib::ullbc_ast::*;
use itertools::Itertools;
use tracing::field;

/// Type: `*[mut] ()`
fn unit_raw_ptr(is_mut: bool) -> Ty {
    Ty::new(TyKind::RawPtr(Ty::mk_unit(), RefKind::mutable(is_mut)))
}

fn dummy_public_attr_info() -> AttrInfo {
    AttrInfo {
        public: true,
        ..Default::default()
    }
}

/// Field: `drop_func: *mut () -> ()`
fn drop_func_field() -> Field {
    Field {
        span: Span::dummy(),
        attr_info: dummy_public_attr_info(),
        name: Some("drop_func".into()),
        ty: Ty::new(TyKind::FnPtr(RegionBinder {
            regions: Vector::new(),
            skip_binder: (Vec::from([unit_raw_ptr(true)]), Ty::mk_unit()),
        })),
    }
}

/// Field: `self_ty_size: usize`
fn size_field() -> Field {
    Field {
        span: Span::dummy(),
        attr_info: dummy_public_attr_info(),
        name: Some("self_ty_size".into()),
        ty: Ty::new(TyKind::Literal(LiteralTy::Integer(IntegerTy::Usize))),
    }
}

/// Field: `self_ty_align: usize`
fn align_field() -> Field {
    Field {
        span: Span::dummy(),
        attr_info: dummy_public_attr_info(),
        name: Some("self_ty_align".into()),
        ty: Ty::new(TyKind::Literal(LiteralTy::Integer(IntegerTy::Usize))),
    }
}

fn common_vtable_entries() -> Vector<FieldId, Field> {
    let mut ret = Vector::new();
    ret.push(drop_func_field());
    ret.push(size_field());
    ret.push(align_field());
    ret
}

/// Remove the first `Self` type variable from the generic parameters.
fn remove_self_from_params(params: &mut GenericParams) {
    params.types.remove_and_shift_ids(TypeVarId::ZERO);
    params.types.iter_mut().for_each(|ty| {
        ty.index -= 1;
    });
}

impl ItemTransCtx<'_, '_> {
    /// Given the trait id, register the vtable of it and returns the vtable struct id
    pub fn translate_vtable_trait_id_as_type_id(
        &mut self,
        span: Span,
        trait_id: &hax::DefId,
    ) -> Result<TypeId, Error> {
        // The vtable type is a type decl, so we register it as such.
        let id = self.register_vtable_as_type_decl_id(span, trait_id);
        Ok(TypeId::Adt(id))
    }

    fn add_parent_trait_vtable_ptrs(
        &mut self,
        fields: &mut Vector<FieldId, Field>,
        parent_clauses: &Vector<TraitClauseId, (hax::TraitPredicate, TraitClause)>,
    ) -> Result<(), Error> {
        for (idx, (pred, clause)) in parent_clauses.iter_indexed_values() {
            let trait_ref = &clause.trait_.skip_binder;
            // FIXME: Why the generics here is WRONG?
            let mut generics = trait_ref.generics.clone();
            // remove the `Self` type argument from the generics
            generics.types.remove_and_shift_ids(TypeVarId::ZERO);
            let def_id = &pred.trait_ref.def_id;
            let id = self.translate_vtable_trait_id_as_type_id(Span::dummy(), def_id)?;
            let vtbl_struct = TypeDeclRef { id, generics };
            let field = Field {
                span: Span::dummy(),
                attr_info: dummy_public_attr_info(),
                name: Some(format!("super_trait_{idx}").into()),
                ty: Ty::new(TyKind::RawPtr(
                    Ty::new(TyKind::Adt(vtbl_struct)),
                    RefKind::Shared,
                )),
            };
            fields.push(field);
        }
        Ok(())
    }

    /// `fn func(&self, ...)` ==> `fn func(&dyn Trait, ...)`
    /// Given the `&self` receiver as the `in_ty`, we convert it to the shim type.
    ///
    /// Specifically, we should every occurence of `Self` in the type to the shim type:
    /// `dyn Trait<'a, ..., T, ..., const N, ..., AssocTy=?, ...>`.
    /// But the `AssocTy` should be yet-to-qualify, and we ignore them here.
    ///
    /// This is because the receiver can not only be `&self` but also `&mut self`, `Box<Self>`, etc.
    fn convert_to_shim_ty(&mut self, span: Span, trait_id: &hax::DefId, in_ty: &Ty) -> Ty {
        // Firstly, create the correct `dyn Trait<'a, ..., T, ..., const N = ?, ...>` type.
        // Add a new binding level for the existentially quantified type.
        self.binding_levels.push(BindingLevel::new(true));

        // Add the existentially quantified type.
        let ty_id = self
            .innermost_binder_mut()
            .params
            .types
            .push_with(|idx| TypeVar {
                index: idx,
                name: String::from("_"),
            });
        let ty = TyKind::TypeVar(DeBruijnVar::new_at_zero(ty_id)).into_ty();

        let mut params = self.binding_levels.pop().unwrap().params;

        // the trait decl ref: `Trait<'a, ..., T, ..., const N = ?, ...>`
        let trait_decl_ref = TraitDeclRef {
            id: self.register_trait_decl_id(span, trait_id),
            // the param should be the identity args of the `trait` decl itself
            generics: Box::new(self.outermost_binder().params.identity_args()),
        };
        // add constraint: `T : Trait<'a, ..., T, ..., const N = ?, ...>`
        params.trait_clauses.push_with(|idx| TraitClause {
            clause_id: idx,
            span: Some(span),
            origin: PredicateOrigin::Dyn,
            trait_: RegionBinder {
                regions: Vector::new(),
                skip_binder: trait_decl_ref,
            },
        });
        let binder = Binder {
            params: params,
            skip_binder: ty,
            kind: BinderKind::Dyn,
        };
        // target type: `dyn Trait<'a, ..., T, ..., const N = ?, ...>`
        // But no `AssocTy` is specified here
        let target_ty = Ty::new(TyKind::DynTrait(DynPredicate { binder }));

        // Then, replace every `Self` in the type with the target type
        #[derive(Clone)]
        struct SelfVisitor(Ty);
        impl VarsVisitor for SelfVisitor {
            fn visit_type_var(&mut self, v: TypeDbVar) -> Option<Ty> {
                let SelfVisitor(target_ty) = self.clone();
                // if the var refers to Bound(0), it refers to `Self`
                // Otherwise, when it is referring something else, it can be unchanged
                if let DeBruijnVar::Bound(DeBruijnId::ZERO, _) = v {
                    Some(target_ty)
                } else {
                    None
                }
            }
        }
        let mut ty = in_ty.clone();
        ty.visit_vars(&mut SelfVisitor(target_ty));
        // ty
        unit_raw_ptr(true)
    }

    fn add_vtable_methods_from_trait_items(
        &mut self,
        span: Span,
        trait_id: &hax::DefId,
        fields: &mut Vector<FieldId, Field>,
        items: &Vec<(hax::AssocItem, std::sync::Arc<hax::FullDef>)>,
    ) -> Result<(), Error> {
        let items: Vec<(TraitItemName, &hax::AssocItem, std::sync::Arc<hax::FullDef>)> = items
            .iter()
            .map(|(item, def)| {
                let name = self.t_ctx.translate_trait_item_name(def.def_id())?;
                Ok((name, item, def.clone()))
            })
            .try_collect()?;
        for (item_name, item, hax_def) in &items {
            match &hax_def.kind {
                hax::FullDefKind::AssocFn { sig, .. } => {
                    // see if this function should be added -- it should be `vtable-safe`
                    // prepare the inquiry context
                    use rustc_trait_selection::traits::is_vtable_safe_method;
                    let tcx = self.t_ctx.tcx;
                    let func_def_id = &item.def_id;
                    let item = tcx.associated_item(func_def_id.as_rust_def_id().unwrap());
                    if !is_vtable_safe_method(tcx, trait_id.as_rust_def_id().unwrap(), item) {
                        continue;
                    }

                    // else, it is `vtable-safe`, then we should translate it
                    // to prepare the shim type environment
                    let func_def = self.hax_def(func_def_id)?;
                    let trait_decl_id = self.register_trait_decl_id(span, trait_id);
                    let binder_kind = BinderKind::TraitMethod(trait_decl_id, item_name.clone());

                    // prepare the shim type
                    let shim_ty = self
                        .translate_binder_for_def(span, binder_kind, &func_def, |tcx| {
                            let sig = &sig.value;
                            let mut in_tys: Vec<Ty> = sig
                                .inputs
                                .iter()
                                .map(|ty| tcx.translate_ty(span, ty))
                                .try_collect()?;
                            // take out the first element of `in_tys` and modify it to the shim type
                            in_tys[0] = tcx.convert_to_shim_ty(span, trait_id, &in_tys[0]);
                            let out_ty = tcx.translate_ty(span, &sig.output)?;
                            // it is safe to take only the region binder here
                            // as Rustc guarantees that only generic Region is allowed
                            // by dyn-compatibility
                            let ty = Ty::new(TyKind::FnPtr(RegionBinder {
                                regions: tcx.innermost_binder().params.regions.clone(),
                                skip_binder: (in_tys, out_ty),
                            }));
                            Ok(ty)
                        })?
                        .skip_binder;

                    let field = Field {
                        span: Span::dummy(),
                        attr_info: dummy_public_attr_info(),
                        name: Some(item_name.to_string().into()),
                        ty: shim_ty,
                    };
                    fields.push(field);
                }
                _ => {}
            }
        }
        Ok(())
    }

    pub fn check_at_most_one_pred_has_methods(
        &mut self,
        span: Span,
        preds: &hax::GenericPredicates,
    ) -> Result<(), Error> {
        // Only the first clause is allowed to have methods.
        for (clause, _) in preds.predicates.iter().skip(1) {
            if let hax::ClauseKind::Trait(trait_predicate) = clause.kind.hax_skip_binder_ref() {
                let trait_def_id = &trait_predicate.trait_ref.def_id;
                let trait_def = self.hax_def(trait_def_id)?;
                let has_methods = match trait_def.kind() {
                    hax::FullDefKind::Trait { items, .. } => items
                        .iter()
                        .any(|(assoc, _)| matches!(assoc.kind, hax::AssocKind::Fn { .. })),
                    hax::FullDefKind::TraitAlias { .. } => false,
                    _ => unreachable!(),
                };
                if has_methods {
                    raise_error!(
                        self,
                        span,
                        "`dyn Trait` with multiple method-bearing predicates is not supported"
                    );
                }
            }
        }
        Ok(())
    }

    /// the true layout of the vtable:
    /// [ drop_func : *mut () -> (),
    ///   self_ty_size : usize,
    ///   self_ty_align : usize,
    ///   ...  -- the super trait vtables
    ///   ...  -- the method list ]
    pub(crate) fn translate_vtable_struct(
        mut self,
        typ_id: TypeDeclId,
        item_meta: ItemMeta,
        trait_full_def: &hax::FullDef,
    ) -> Result<TypeDecl, Error> {
        // start by getting the generic environment ready
        self.translate_def_generics(Span::dummy(), trait_full_def)?;
        // remove the `Self` type variable from the generic parameters
        remove_self_from_params(&mut self.the_only_binder_mut().params);
        let mut fields = common_vtable_entries();

        // translate the super pointers
        let parent_clauses = mem::take(&mut self.parent_trait_clauses);
        self.add_parent_trait_vtable_ptrs(&mut fields, &parent_clauses)?;

        // if it is a trait definition, we need to add the methods
        if let hax::FullDefKind::Trait { items, .. } = &trait_full_def.kind() {
            self.add_vtable_methods_from_trait_items(
                item_meta.span,
                trait_full_def.def_id(),
                &mut fields,
                items,
            )?;
        }
        // else, it should be a trait alias, which should not have any methods in its vtable

        // take out the required stuff before consuming `self`
        let ptr_size = self.t_ctx.translated.target_information.target_pointer_size;
        let trait_id = self.register_trait_decl_id(Span::dummy(), &trait_full_def.def_id);
        // consumes `self` to get the generics
        let generics = self.into_generics();
        let ptr_align = ptr_size;
        let layout = Layout {
            // everything is of the same size as a pointer
            size: Some((fields.iter().count() as u64) * ptr_size),
            align: Some(ptr_align as u64),
            discriminant_layout: None,
            uninhabited: false,
            variant_layouts: Vector::new(),
        };
        let trait_decl_ref = TraitDeclRef {
            id: trait_id,
            generics: Box::new(generics.identity_args()),
        };

        Ok(TypeDecl {
            def_id: typ_id,
            item_meta: item_meta,
            generics: generics,
            src: ItemKind::VTable {
                trait_decl_ref: trait_decl_ref,
            },
            kind: TypeDeclKind::Struct(fields),
            layout: Some(layout),
            // There is definitely no metadata associated with this type
            ptr_metadata: None,
        })
    }

    pub(crate) fn translate_vtable_instance(
        mut self,
        glob_id: GlobalDeclId,
        item_meta: ItemMeta,
        def: &hax::FullDef,
    ) -> Result<GlobalDecl, Error> {
        Err(Error { span: item_meta.span, msg: String::from("TODO") })
    }

    pub(crate) fn translate_vtable_instance_body(
        mut self,
        init_func_id: FunDeclId,
        item_meta: ItemMeta,
        def: &hax::FullDef,
    ) -> Result<FunDecl, Error> {
        Err(Error { span: item_meta.span, msg: String::from("TODO") })
    }

    pub fn translate_existential_predicates(
        &mut self,
        span: Span,
        self_ty: &hax::ParamTy,
        preds: &hax::GenericPredicates,
        region: &hax::Region,
    ) -> Result<DynPredicate, Error> {
        // This is a robustness check: the current version of Rustc
        // accepts at most one method-bearing predicate in a trait object.
        // But things may change in the future.
        self.check_at_most_one_pred_has_methods(span, preds)?;

        // Translate the region outside the binder.
        let region = self.translate_region(span, region)?;
        let region = region.move_under_binder();

        // Add a binder that contains the existentially quantified type.
        self.binding_levels.push(BindingLevel::new(true));

        // Add the existentially quantified type.
        let ty_id = self
            .innermost_binder_mut()
            .push_type_var(self_ty.index, self_ty.name.clone());
        let ty = TyKind::TypeVar(DeBruijnVar::new_at_zero(ty_id)).into_ty();

        self.innermost_binder_mut()
            .params
            .types_outlive
            .push(RegionBinder::empty(OutlivesPred(ty.clone(), region)));
        self.register_predicates(preds, PredicateOrigin::Dyn, &PredicateLocation::Base)?;

        let params = self.binding_levels.pop().unwrap().params;
        let binder = Binder {
            params: params,
            skip_binder: ty,
            kind: BinderKind::Dyn,
        };
        Ok(DynPredicate { binder })
    }
}
