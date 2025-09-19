use super::{
    translate_crate::TransItemSourceKind, translate_ctx::*, translate_generics::BindingLevel,
};

use charon_lib::formatter::IntoFormatter;
use charon_lib::ids::Vector;
use charon_lib::pretty::FmtWithCtx;
use charon_lib::ullbc_ast::*;
use itertools::Itertools;

fn dummy_public_attr_info() -> AttrInfo {
    AttrInfo {
        public: true,
        ..Default::default()
    }
}

fn usize_ty() -> Ty {
    Ty::new(TyKind::Literal(LiteralTy::UInt(UIntTy::Usize)))
}

/// Takes a `T` valid in the context of a trait ref and transforms it into a `T` valid in the
/// context of its vtable definition, i.e. no longer mentions the `Self` type or `Self` clause. If
/// `new_self` is `Some`, we replace any mention of the `Self` type with it; otherwise we panic if
/// `Self` is mentioned.
/// If `for_method` is true, we're handling a value coming from a `AssocFn`, which takes the `Self`
/// clause as its first clause parameter. Otherwise we're in trait scope, where the `Self` clause
/// is represented with `TraitRefKind::SelfId`.
fn dynify<T: TyVisitable>(mut x: T, new_self: Option<Ty>, for_method: bool) -> T {
    struct ReplaceSelfVisitor {
        new_self: Option<Ty>,
        for_method: bool,
    }
    impl VarsVisitor for ReplaceSelfVisitor {
        fn visit_type_var(&mut self, v: TypeDbVar) -> Option<Ty> {
            if let DeBruijnVar::Bound(DeBruijnId::ZERO, type_id) = v {
                // Replace type 0 and decrement the others.
                Some(if let Some(new_id) = type_id.index().checked_sub(1) {
                    TyKind::TypeVar(DeBruijnVar::Bound(DeBruijnId::ZERO, TypeVarId::new(new_id)))
                        .into_ty()
                } else {
                    self.new_self.clone().expect(
                        "Found unexpected `Self` 
                        type when constructing vtable",
                    )
                })
            } else {
                None
            }
        }

        fn visit_clause_var(&mut self, v: ClauseDbVar) -> Option<TraitRefKind> {
            if let DeBruijnVar::Bound(DeBruijnId::ZERO, clause_id) = v {
                if self.for_method && clause_id == TraitClauseId::ZERO {
                    // That's the `Self` clause.
                    Some(TraitRefKind::Dyn)
                } else {
                    panic!("Found unexpected clause var when constructing vtable: {v}")
                }
            } else {
                None
            }
        }

        fn visit_self_clause(&mut self) -> Option<TraitRefKind> {
            Some(TraitRefKind::Dyn)
        }
    }
    x.visit_vars(&mut ReplaceSelfVisitor {
        new_self,
        for_method,
    });
    x
}

//// Translate the `dyn Trait` type.
impl ItemTransCtx<'_, '_> {
    pub fn check_at_most_one_pred_has_methods(
        &mut self,
        span: Span,
        preds: &hax::GenericPredicates,
    ) -> Result<(), Error> {
        // Only the first clause is allowed to have methods.
        for (clause, _) in preds.predicates.iter().skip(1) {
            if let hax::ClauseKind::Trait(trait_predicate) = clause.kind.hax_skip_binder_ref() {
                let trait_def_id = &trait_predicate.trait_ref.def_id;
                let trait_def = self.poly_hax_def(trait_def_id)?;
                let has_methods = match trait_def.kind() {
                    hax::FullDefKind::Trait { items, .. } => items
                        .iter()
                        .any(|assoc| matches!(assoc.kind, hax::AssocKind::Fn { .. })),
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
        self.register_predicates(preds, PredicateOrigin::Dyn)?;

        let params = self.binding_levels.pop().unwrap().params;
        let binder = Binder {
            params: params,
            skip_binder: ty,
            kind: BinderKind::Dyn,
        };
        Ok(DynPredicate { binder })
    }
}

//// Generate the vtable struct.
impl ItemTransCtx<'_, '_> {
    /// Query whether a trait is dyn compatible.
    /// TODO(dyn): for now we return `false` if the trait has any associated types, as we don't
    /// handle associated types in vtables.
    pub fn trait_is_dyn_compatible(&mut self, def_id: &hax::DefId) -> Result<bool, Error> {
        let def = self.poly_hax_def(def_id)?;
        Ok(match def.kind() {
            hax::FullDefKind::Trait { dyn_self, .. }
            | hax::FullDefKind::TraitAlias { dyn_self, .. } => dyn_self.is_some(),
            _ => false,
        })
    }

    /// Check whether this trait ref is of the form `Self: Trait<...>`.
    fn pred_is_for_self(&self, tref: &hax::TraitRef) -> bool {
        let first_ty = tref
            .generic_args
            .iter()
            .filter_map(|arg| match arg {
                hax::GenericArg::Type(ty) => Some(ty),
                _ => None,
            })
            .next();
        match first_ty {
            None => false,
            Some(first_ty) => match first_ty.kind() {
                hax::TyKind::Param(param_ty) if param_ty.index == 0 => {
                    assert_eq!(param_ty.name, "Self");
                    true
                }
                _ => false,
            },
        }
    }

    /// Given a trait ref, return a reference to its vtable struct, if it is dyn compatible.
    pub fn translate_vtable_struct_ref(
        &mut self,
        span: Span,
        tref: &hax::TraitRef,
    ) -> Result<Option<TypeDeclRef>, Error> {
        if !self.trait_is_dyn_compatible(&tref.def_id)? {
            return Ok(None);
        }
        // Don't enqueue the vtable for translation by default. It will be enqueued if used in a
        // `dyn Trait`.
        let mut vtable_ref: TypeDeclRef =
            self.translate_item_no_enqueue(span, tref, TransItemSourceKind::VTable)?;
        // Remove the `Self` type variable from the generic parameters.
        vtable_ref
            .generics
            .types
            .remove_and_shift_ids(TypeVarId::ZERO);

        // The vtable type also takes associated types as parameters.
        let assoc_tys: Vec<_> = tref
            .trait_associated_types(&self.hax_state_with_id())
            .iter()
            .map(|ty| self.translate_ty(span, ty))
            .try_collect()?;
        vtable_ref.generics.types.extend(assoc_tys);

        Ok(Some(vtable_ref))
    }

    /// Add a `method_name: fn(...) -> ...` field for the method.
    fn add_method_to_vtable_def(
        &mut self,
        span: Span,
        trait_def: &hax::FullDef,
        mut mk_field: impl FnMut(String, Ty),
        item: &hax::AssocItem,
    ) -> Result<(), Error> {
        let item_def_id = &item.def_id;
        let item_def = self.hax_def(
            &trait_def
                .this()
                .with_def_id(&self.t_ctx.hax_state, item_def_id),
        )?;
        let hax::FullDefKind::AssocFn {
            sig,
            vtable_receiver: Some(_),
            ..
        } = item_def.kind()
        else {
            return Ok(());
        };

        let item_name = self.t_ctx.translate_trait_item_name(item_def_id)?;
        // It's ok to translate the method signature in the context of the trait because
        // `vtable_safe: true` ensures the method has no generics of its own.
        let sig = self.translate_fun_sig(span, sig)?;
        let ty = TyKind::FnPtr(sig).into_ty();

        mk_field(format!("method_{}", item_name.0), ty);
        Ok(())
    }

    /// Add `super_trait_n: &'static SuperTraitNVTable` fields.
    fn add_supertraits_to_vtable_def(
        &mut self,
        span: Span,
        mut mk_field: impl FnMut(String, Ty),
        implied_predicates: &hax::GenericPredicates,
    ) -> Result<(), Error> {
        let mut counter = (0..).into_iter();
        for (clause, _span) in &implied_predicates.predicates {
            if let hax::ClauseKind::Trait(pred) = clause.kind.hax_skip_binder_ref() {
                // If a clause looks like `Self: OtherTrait<...>`, we consider it a supertrait.
                if !self.pred_is_for_self(&pred.trait_ref) {
                    continue;
                }
                let vtbl_struct = self
                    .translate_region_binder(span, &clause.kind, |ctx, _| {
                        ctx.translate_vtable_struct_ref(span, &pred.trait_ref)
                    })?
                    .erase()
                    .expect("parent trait should be dyn compatible");
                let ty = Ty::new(TyKind::Ref(
                    Region::Static,
                    Ty::new(TyKind::Adt(vtbl_struct)),
                    RefKind::Shared,
                ));
                mk_field(format!("super_trait_{}", counter.next().unwrap()), ty);
            }
        }
        Ok(())
    }

    fn gen_vtable_struct_fields(
        &mut self,
        span: Span,
        trait_def: &hax::FullDef,
        implied_predicates: &hax::GenericPredicates,
    ) -> Result<Vector<FieldId, Field>, Error> {
        let mut fields = Vector::new();
        let mut mk_field = |name, ty| {
            fields.push(Field {
                span,
                attr_info: dummy_public_attr_info(),
                name: Some(name),
                ty,
            });
        };

        // Add the basic fields.
        // Field: `size: usize`
        mk_field("size".into(), usize_ty());
        // Field: `align: usize`
        mk_field("align".into(), usize_ty());
        // Field: `drop: fn(*mut Self)`
        mk_field("drop".into(), {
            let self_ty = TyKind::TypeVar(DeBruijnVar::new_at_zero(TypeVarId::ZERO)).into_ty();
            let self_ptr = TyKind::RawPtr(self_ty, RefKind::Mut).into_ty();
            Ty::new(TyKind::FnPtr(RegionBinder::empty((
                [self_ptr].into(),
                Ty::mk_unit(),
            ))))
        });

        // Add the method pointers (trait aliases don't have methods).
        if let hax::FullDefKind::Trait { items, .. } = trait_def.kind() {
            for item in items {
                self.add_method_to_vtable_def(span, trait_def, &mut mk_field, item)?;
            }
        }

        // Add the supertrait vtables.
        self.add_supertraits_to_vtable_def(span, &mut mk_field, implied_predicates)?;

        Ok(fields)
    }

    /// This is a temporary check until we support `dyn Trait` with `--monomorphize`.
    pub(crate) fn check_no_monomorphize(&self, span: Span) -> Result<(), Error> {
        if self.monomorphize() {
            raise_error!(
                self,
                span,
                "`dyn Trait` is not yet supported with `--monomorphize`; \
                use `--monomorphize-conservative` instead"
            )
        }
        Ok(())
    }

    /// Construct the type of the vtable for this trait.
    ///
    /// It's a struct that has for generics the generics of the trait + one parameter for each
    /// associated type of the trait and its parents.
    ///
    /// struct TraitVTable<TraitArgs.., AssocTys..> {
    ///   size: usize,
    ///   align: usize,
    ///   drop: fn(*mut dyn Trait<...>),
    ///   method_name: fn(&dyn Trait<...>, Args..) -> Output,
    ///   ... other methods
    ///   super_trait_0: &'static SuperTrait0VTable
    ///   ... other supertraits
    /// }
    pub(crate) fn translate_vtable_struct(
        mut self,
        type_id: TypeDeclId,
        item_meta: ItemMeta,
        trait_def: &hax::FullDef,
    ) -> Result<TypeDecl, Error> {
        let span = item_meta.span;
        if !self.trait_is_dyn_compatible(trait_def.def_id())? {
            raise_error!(
                self,
                span,
                "Trying to compute the vtable type \
                for a non-dyn-compatible trait"
            );
        }
        self.check_no_monomorphize(span)?;

        self.translate_def_generics(span, trait_def)?;

        let (hax::FullDefKind::Trait {
            dyn_self,
            implied_predicates,
            ..
        }
        | hax::FullDefKind::TraitAlias {
            dyn_self,
            implied_predicates,
            ..
        }) = trait_def.kind()
        else {
            panic!()
        };
        let Some(dyn_self) = dyn_self else {
            panic!("Trying to generate a vtable for a non-dyn-compatible trait")
        };

        // The `dyn Trait<Args..>` type for this trait.
        let mut dyn_self = {
            let dyn_self = self.translate_ty(span, dyn_self)?;
            let TyKind::DynTrait(mut dyn_pred) = dyn_self.kind().clone() else {
                panic!("incorrect `dyn_self`")
            };

            // Add one generic parameter for each associated type of this trait and its parents. We
            // then use that in `dyn_self`
            for (i, ty_constraint) in dyn_pred
                .binder
                .params
                .trait_type_constraints
                .iter_mut()
                .enumerate()
            {
                let name = format!("Ty{i}");
                let new_ty = self
                    .the_only_binder_mut()
                    .params
                    .types
                    .push_with(|index| TypeVar { index, name });
                // Moving that type under two levels of binders: the `DynPredicate` binder and the
                // type constraint binder.
                let new_ty =
                    TyKind::TypeVar(DeBruijnVar::bound(DeBruijnId::new(2), new_ty)).into_ty();
                ty_constraint.skip_binder.ty = new_ty;
            }
            TyKind::DynTrait(dyn_pred).into_ty()
        };

        // First construct fields that use the real method signatures (which may use the `Self`
        // type). We fixup the types and generics below.
        let fields = self.gen_vtable_struct_fields(span, trait_def, implied_predicates)?;
        let mut kind = TypeDeclKind::Struct(fields);
        let layout = self.generate_naive_layout(span, &kind)?;

        // Replace any use of `Self` with `dyn Trait<...>`, and remove the `Self` type variable
        // from the generic parameters.
        let mut generics = self.into_generics();
        {
            dyn_self = dynify(dyn_self, None, false);
            generics = dynify(generics, Some(dyn_self.clone()), false);
            kind = dynify(kind, Some(dyn_self.clone()), true);
            generics.types.remove_and_shift_ids(TypeVarId::ZERO);
            generics.types.iter_mut().for_each(|ty| {
                ty.index -= 1;
            });
        }

        let dyn_predicate = dyn_self
            .kind()
            .as_dyn_trait()
            .expect("incorrect `dyn_self`");
        Ok(TypeDecl {
            def_id: type_id,
            item_meta: item_meta,
            generics: generics,
            src: ItemKind::VTableTy {
                dyn_predicate: dyn_predicate.clone(),
            },
            kind,
            layout: Some(layout),
            ptr_metadata: None,
        })
    }
}

//// Generate a vtable value.
impl ItemTransCtx<'_, '_> {
    pub fn translate_vtable_instance_ref(
        &mut self,
        span: Span,
        trait_ref: &hax::TraitRef,
        impl_ref: &hax::ItemRef,
    ) -> Result<Option<GlobalDeclRef>, Error> {
        if !self.trait_is_dyn_compatible(&trait_ref.def_id)? {
            return Ok(None);
        }
        // Don't enqueue the vtable for translation by default. It will be enqueued if used in a
        // `dyn Trait` coercion.
        // TODO(dyn): To do this properly we'd need to know for each clause whether it ultimately
        // ends up used in a vtable cast.
        let vtable_ref: GlobalDeclRef = self.translate_item_no_enqueue(
            span,
            impl_ref,
            TransItemSourceKind::VTableInstance(TraitImplSource::Normal),
        )?;
        Ok(Some(vtable_ref))
    }

    /// Local helper function to get the vtable struct reference and trait declaration reference
    fn get_vtable_instance_info<'a>(
        &mut self,
        span: Span,
        impl_def: &'a hax::FullDef,
        impl_kind: &TraitImplSource,
    ) -> Result<(TraitImplRef, TraitDeclRef, TypeDeclRef), Error> {
        let implemented_trait = match impl_def.kind() {
            hax::FullDefKind::TraitImpl { trait_pred, .. } => &trait_pred.trait_ref,
            _ => unreachable!(),
        };
        let vtable_struct_ref = self
            .translate_vtable_struct_ref(span, implemented_trait)?
            .expect("trait should be dyn-compatible");
        let implemented_trait = self.translate_trait_decl_ref(span, implemented_trait)?;
        let impl_ref = self.translate_item(
            span,
            impl_def.this(),
            TransItemSourceKind::TraitImpl(*impl_kind),
        )?;
        Ok((impl_ref, implemented_trait, vtable_struct_ref))
    }

    /// E.g.,
    /// global {impl Trait for Foo}::vtable<Args..>: Trait::{vtable}<TraitArgs.., AssocTys..> {
    ///     size: size_of(Foo),
    ///     align: align_of(Foo),
    ///     drop: <Foo as Drop>::drop,
    ///     method_0: <Foo as Trait>::method_0::{shim},
    ///     method_1: <Foo as Trait>::method_1::{shim},
    ///     ...
    ///     super_trait_0: SuperImpl0<..>::{vtable_instance}::<..>,
    ///     super_trait_1: SuperImpl1<..>::{vtable_instance}::<..>,
    ///     ...
    /// }
    pub(crate) fn translate_vtable_instance(
        mut self,
        global_id: GlobalDeclId,
        item_meta: ItemMeta,
        impl_def: &hax::FullDef,
        impl_kind: &TraitImplSource,
    ) -> Result<GlobalDecl, Error> {
        let span = item_meta.span;
        self.translate_def_generics(span, impl_def)?;
        self.check_no_monomorphize(span)?;

        let (impl_ref, _, vtable_struct_ref) =
            self.get_vtable_instance_info(span, impl_def, impl_kind)?;
        // Initializer function for this global.
        let init = self.register_item(
            span,
            impl_def.this(),
            TransItemSourceKind::VTableInstanceInitializer(*impl_kind),
        );

        Ok(GlobalDecl {
            def_id: global_id,
            item_meta,
            generics: self.into_generics(),
            kind: ItemKind::VTableInstance { impl_ref },
            // it should be static to have its own address
            global_kind: GlobalKind::Static,
            ty: Ty::new(TyKind::Adt(vtable_struct_ref)),
            init,
        })
    }

    fn add_method_to_vtable_value(
        &mut self,
        span: Span,
        impl_def: &hax::FullDef,
        item: &hax::ImplAssocItem,
        mut mk_field: impl FnMut(ConstantExprKind),
    ) -> Result<(), Error> {
        // Exit if the item isn't a vtable safe method.
        match self.poly_hax_def(&item.decl_def_id)?.kind() {
            hax::FullDefKind::AssocFn {
                vtable_receiver: Some(_),
                ..
            } => {}
            _ => return Ok(()),
        }

        let const_kind = match &item.value {
            hax::ImplAssocItemValue::Provided {
                def_id: item_def_id,
                ..
            } => {
                // The method is vtable safe so it has no generics, hence we can reuse the impl
                // generics.
                let item_ref = impl_def.this().with_def_id(self.hax_state(), item_def_id);
                let shim_ref = self
                    .translate_fn_ptr(span, &item_ref, TransItemSourceKind::VTableMethod)?
                    .erase();
                ConstantExprKind::FnPtr(shim_ref)
            }
            hax::ImplAssocItemValue::DefaultedFn { .. } => ConstantExprKind::Opaque(
                "shim for default methods \
                    aren't yet supported"
                    .to_string(),
            ),
            _ => return Ok(()),
        };

        mk_field(const_kind);

        Ok(())
    }

    fn add_supertraits_to_vtable_value(
        &mut self,
        span: Span,
        trait_def: &hax::FullDef,
        impl_def: &hax::FullDef,
        mut mk_field: impl FnMut(ConstantExprKind),
    ) -> Result<(), Error> {
        let hax::FullDefKind::TraitImpl {
            implied_impl_exprs, ..
        } = impl_def.kind()
        else {
            unreachable!()
        };
        let hax::FullDefKind::Trait {
            implied_predicates, ..
        } = trait_def.kind()
        else {
            unreachable!()
        };
        for ((clause, _), impl_expr) in implied_predicates.predicates.iter().zip(implied_impl_exprs)
        {
            let hax::ClauseKind::Trait(pred) = clause.kind.hax_skip_binder_ref() else {
                continue;
            };
            // If a clause looks like `Self: OtherTrait<...>`, we consider it a supertrait.
            if !self.pred_is_for_self(&pred.trait_ref) {
                continue;
            }

            let vtable_def_ref = self
                .translate_region_binder(span, &impl_expr.r#trait, |ctx, tref| {
                    ctx.translate_vtable_struct_ref(span, tref)
                })?
                .erase()
                .expect("parent trait should be dyn compatible");
            let fn_ptr_ty = TyKind::Adt(vtable_def_ref).into_ty();
            let kind = match &impl_expr.r#impl {
                hax::ImplExprAtom::Concrete(impl_item) => {
                    let vtable_instance_ref = self
                        .translate_region_binder(span, &impl_expr.r#trait, |ctx, tref| {
                            ctx.translate_vtable_instance_ref(span, tref, impl_item)
                        })?
                        .erase()
                        .expect("parent trait should be dyn compatible");
                    let global = Box::new(ConstantExpr {
                        value: ConstantExprKind::Global(vtable_instance_ref),
                        ty: fn_ptr_ty,
                    });
                    ConstantExprKind::Ref(global)
                }
                // TODO(dyn): builtin impls
                _ => ConstantExprKind::Opaque("missing supertrait vtable".into()),
            };
            mk_field(kind);
        }
        Ok(())
    }

    /// Generate the body of the vtable instance function.
    /// This is for `impl Trait for T` implementation, it does NOT handle builtin impls.
    /// ```ignore
    /// let ret@0 : VTable;
    /// ret@0 = VTable { ... };
    /// return;
    /// ```
    fn gen_vtable_instance_init_body(
        &mut self,
        span: Span,
        impl_def: &hax::FullDef,
        vtable_struct_ref: TypeDeclRef,
    ) -> Result<Body, Error> {
        let mut locals = Locals {
            arg_count: 0,
            locals: Vector::new(),
        };
        let ret_ty = Ty::new(TyKind::Adt(vtable_struct_ref.clone()));
        let ret_place = locals.new_var(Some("ret".into()), ret_ty.clone());

        let hax::FullDefKind::TraitImpl {
            trait_pred, items, ..
        } = impl_def.kind()
        else {
            unreachable!()
        };
        let trait_def = self.hax_def(&trait_pred.trait_ref)?;

        // Retreive the expected field types from the struct definition. This avoids complicated
        // substitutions.
        let field_tys = {
            let vtable_decl_id = vtable_struct_ref.id.as_adt().unwrap().clone();
            let AnyTransItem::Type(vtable_def) =
                self.t_ctx.get_or_translate(vtable_decl_id.into())?
            else {
                unreachable!()
            };
            let TypeDeclKind::Struct(fields) = &vtable_def.kind else {
                unreachable!()
            };
            fields
                .iter()
                .map(|f| &f.ty)
                .cloned()
                .map(|ty| ty.substitute(&vtable_struct_ref.generics))
                .collect_vec()
        };

        let mut statements = vec![];
        let mut aggregate_fields = vec![];
        // For each vtable field, assign the desired value to a new local.
        let mut field_ty_iter = field_tys.into_iter();
        let mut mk_field = |kind| {
            aggregate_fields.push(Operand::Const(Box::new(ConstantExpr {
                value: kind,
                ty: field_ty_iter.next().unwrap(),
            })));
        };

        // TODO(dyn): provide values
        mk_field(ConstantExprKind::Opaque("unknown size".to_string()));
        mk_field(ConstantExprKind::Opaque("unknown align".to_string()));
        mk_field(ConstantExprKind::Opaque("unknown drop".to_string()));

        for item in items {
            self.add_method_to_vtable_value(span, impl_def, item, &mut mk_field)?;
        }

        self.add_supertraits_to_vtable_value(span, &trait_def, impl_def, &mut mk_field)?;

        if field_ty_iter.next().is_some() {
            raise_error!(
                self,
                span,
                "Missed some fields in vtable value construction"
            )
        }

        // Construct the final struct.
        statements.push(Statement::new(
            span,
            StatementKind::Assign(
                ret_place,
                Rvalue::Aggregate(
                    AggregateKind::Adt(vtable_struct_ref.clone(), None, None),
                    aggregate_fields,
                ),
            ),
        ));

        let block = BlockData {
            statements,
            terminator: Terminator::new(span, TerminatorKind::Return),
        };

        Ok(Body::Unstructured(GExprBody {
            span,
            locals,
            comments: Vec::new(),
            body: [block].into(),
        }))
    }

    fn generate_concretization(
        &mut self,
        span: Span,
        statements: &mut Vec<Statement>,
        shim_self: &Place,
        target_self: &Place,
    ) -> Result<(), Error> {
        let rval = Rvalue::UnaryOp(
            UnOp::Cast(CastKind::Concretize(
                shim_self.ty().clone(),
                target_self.ty().clone(),
            )),
            Operand::Move(shim_self.clone()),
        );
        let stmt = StatementKind::Assign(target_self.clone(), rval);
        statements.push(Statement::new(span, stmt));

        Ok(())
    }

    pub(crate) fn translate_vtable_instance_init(
        mut self,
        init_func_id: FunDeclId,
        item_meta: ItemMeta,
        impl_def: &hax::FullDef,
        impl_kind: &TraitImplSource,
    ) -> Result<FunDecl, Error> {
        let span = item_meta.span;
        self.translate_def_generics(span, impl_def)?;
        self.check_no_monomorphize(span)?;

        let (impl_ref, _, vtable_struct_ref) =
            self.get_vtable_instance_info(span, impl_def, impl_kind)?;
        let init_for = self.register_item(
            span,
            impl_def.this(),
            TransItemSourceKind::VTableInstance(*impl_kind),
        );

        // Signature: `() -> VTable`.
        let sig = FunSig {
            is_unsafe: false,
            generics: self.the_only_binder().params.clone(),
            inputs: vec![],
            output: Ty::new(TyKind::Adt(vtable_struct_ref.clone())),
        };

        let body = match impl_kind {
            TraitImplSource::Normal => {
                let body = self.gen_vtable_instance_init_body(span, impl_def, vtable_struct_ref)?;
                Ok(body)
            }
            _ => {
                raise_error!(
                    self,
                    span,
                    "Don't know how to generate a vtable for a virtual impl {impl_kind:?}"
                );
            }
        };

        Ok(FunDecl {
            def_id: init_func_id,
            item_meta: item_meta,
            signature: sig,
            kind: ItemKind::VTableInstance { impl_ref },
            is_global_initializer: Some(init_for),
            body,
        })
    }

    /// The target vtable shim body looks like:
    /// ```ignore
    /// local ret@0 : ReturnTy;
    /// // the shim receiver of this shim function
    /// local shim_self@1 : ShimReceiverTy;
    /// // the arguments of the impl function
    /// local arg1@2 : Arg1Ty;
    /// ...
    /// local argN@N : ArgNTy;
    /// // the target receiver of the impl function
    /// local target_self@(N+1) : TargetReceiverTy;
    /// // perform some conversion to cast / re-box the shim receiver to the target receiver
    /// ...
    /// target_self@(N+1) := concretize_cast<ShimReceiverTy, TargetReceiverTy>(shim_self@1);
    /// // call the impl function and assign the result to ret@0
    /// ret@0 := impl_func(target_self@(N+1), arg1@2, ..., argN@N);
    /// ```
    fn translate_vtable_shim_body(
        &mut self,
        span: Span,
        target_receiver: &Ty,
        shim_signature: &FunSig,
        impl_func_def: &hax::FullDef,
    ) -> Result<Body, Error> {
        let mut locals = Locals {
            arg_count: shim_signature.inputs.len(),
            locals: Vector::new(),
        };
        let mut statements = vec![];
        let mut new_var = |name, ty| {
            let ret = locals.new_var(name, ty);
            statements.push(Statement::new(
                span,
                StatementKind::StorageLive(ret.as_local().unwrap()),
            ));
            ret
        };

        let ret_place = new_var(None, shim_signature.output.clone());
        let shim_self = new_var(None, shim_signature.inputs[0].clone());
        let args = shim_signature.inputs[1..]
            .iter()
            .map(|ty| new_var(None, ty.clone()))
            .collect::<Vec<_>>();
        let target_self = new_var(None, target_receiver.clone());

        // Perform the core concretization cast, need to unpack & re-pack the structure
        // for cases like `Rc`, `Arc`, `Pin` and (when --raw-boxes is on) `Box`
        self.generate_concretization(span, &mut statements, &shim_self, &target_self)?;

        let call = {
            let fun_id = self.register_item(span, &impl_func_def.this(), TransItemSourceKind::Fun);
            let generics = Box::new(self.outermost_binder().params.identity_args());
            Call {
                func: FnOperand::Regular(FnPtr {
                    func: Box::new(FunIdOrTraitMethodRef::Fun(fun_id)),
                    generics,
                }),
                args: [target_self]
                    .into_iter()
                    .chain(args)
                    .map(|arg| Operand::Move(arg))
                    .collect(),
                dest: ret_place,
            }
        };

        // Create blocks
        let mut blocks = Vector::new();

        let ret_block = BlockData {
            statements: vec![],
            terminator: Terminator::new(span, TerminatorKind::Return),
        };

        let unwind_block = BlockData {
            statements: vec![],
            terminator: Terminator::new(span, TerminatorKind::UnwindResume),
        };

        let call_block = BlockData {
            statements,
            terminator: Terminator::new(
                span,
                TerminatorKind::Call {
                    call,
                    target: BlockId::new(1),    // ret_block
                    on_unwind: BlockId::new(2), // unwind_block
                },
            ),
        };

        blocks.push(call_block); // BlockId(0) -- START_BLOCK_ID
        blocks.push(ret_block); // BlockId(1)
        blocks.push(unwind_block); // BlockId(2)

        Ok(Body::Unstructured(GExprBody {
            span,
            locals,
            comments: Vec::new(),
            body: blocks,
        }))
    }

    pub(crate) fn translate_vtable_shim(
        mut self,
        fun_id: FunDeclId,
        item_meta: ItemMeta,
        impl_func_def: &hax::FullDef,
    ) -> Result<FunDecl, Error> {
        let span = item_meta.span;
        self.check_no_monomorphize(span)?;

        let hax::FullDefKind::AssocFn {
            vtable_receiver: Some(vtable_receiver),
            ..
        } = impl_func_def.kind()
        else {
            raise_error!(
                self,
                span,
                "Trying to generate a vtable shim for a non-vtable-safe method"
            );
        };

        // compute the correct signature for the shim
        let mut signature = self.translate_function_signature(impl_func_def, &item_meta)?;

        let target_receiver = signature.inputs[0].clone();

        // Use the vtable_receiver as the shim receiver type, but substitute generics
        // with concrete types from the impl context
        let dyn_receiver = self.translate_ty(span, vtable_receiver)?;
        signature.inputs[0] = dyn_receiver;

        trace!(
            "[VtableShim] Obtained dyn receiver type: {}",
            signature.inputs[0].with_ctx(&self.into_fmt())
        );

        let body =
            self.translate_vtable_shim_body(span, &target_receiver, &signature, impl_func_def)?;

        Ok(FunDecl {
            def_id: fun_id,
            item_meta,
            signature,
            kind: ItemKind::VTableMethodShim,
            is_global_initializer: None,
            body: Ok(body),
        })
    }
}
