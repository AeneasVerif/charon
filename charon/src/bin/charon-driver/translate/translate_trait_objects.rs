use charon_lib::ast::ullbc_ast_utils::BodyBuilder;
use hax::TraitPredicate;
use itertools::Itertools;
use rustc_span::kw;
use std::mem;

use super::{
    translate_crate::TransItemSourceKind, translate_ctx::*, translate_generics::BindingLevel,
};
use charon_lib::formatter::IntoFormatter;
use charon_lib::ids::{IndexMap, IndexVec};
use charon_lib::pretty::FmtWithCtx;
use charon_lib::ullbc_ast::*;

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

    pub fn translate_dyn_binder<T, U>(
        &mut self,
        span: Span,
        binder: &hax::DynBinder<T>,
        f: impl FnOnce(&mut Self, Ty, &T) -> Result<U, Error>,
    ) -> Result<Binder<U>, Error> {
        // This is a robustness check: the current version of Rustc
        // accepts at most one method-bearing predicate in a trait object.
        // But things may change in the future.
        self.check_at_most_one_pred_has_methods(span, &binder.predicates)?;

        // Add a binder that contains the existentially quantified type.
        self.binding_levels.push(BindingLevel::new(true));

        // Add the existentially quantified type.
        let ty_id = self
            .innermost_binder_mut()
            .push_type_var(binder.existential_ty.index, binder.existential_ty.name);
        let ty = TyKind::TypeVar(DeBruijnVar::new_at_zero(ty_id)).into_ty();
        let val = f(self, ty, &binder.val)?;

        self.register_predicates(&binder.predicates, PredicateOrigin::Dyn)?;

        let params = self.binding_levels.pop().unwrap().params;
        Ok(Binder {
            params: params,
            skip_binder: val,
            kind: BinderKind::Dyn,
        })
    }
}

/// Vtable field info used for translation (same deal as `charon_lib::VTableField` but with
/// different data).
pub enum TrVTableField {
    Size,
    Align,
    Drop,
    Method(TraitItemName, hax::Binder<hax::TyFnSig>),
    SuperTrait(TraitClauseId, hax::Clause),
}

pub struct VTableData {
    pub fields: IndexVec<FieldId, TrVTableField>,
    pub supertrait_map: IndexMap<TraitClauseId, Option<FieldId>>,
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
                    assert_eq!(param_ty.name, kw::SelfUpper);
                    true
                }
                _ => false,
            },
        }
    }

    pub fn translate_vtable_struct_ref(
        &mut self,
        span: Span,
        tref: &hax::TraitRef,
    ) -> Result<Option<TypeDeclRef>, Error> {
        self.translate_vtable_struct_ref_maybe_enqueue(true, span, tref)
    }

    pub fn translate_vtable_struct_ref_no_enqueue(
        &mut self,
        span: Span,
        tref: &hax::TraitRef,
    ) -> Result<Option<TypeDeclRef>, Error> {
        self.translate_vtable_struct_ref_maybe_enqueue(false, span, tref)
    }

    /// Given a trait ref, return a reference to its vtable struct, if it is dyn compatible.
    pub fn translate_vtable_struct_ref_maybe_enqueue(
        &mut self,
        enqueue: bool,
        span: Span,
        tref: &hax::TraitRef,
    ) -> Result<Option<TypeDeclRef>, Error> {
        if !self.trait_is_dyn_compatible(&tref.def_id)? {
            return Ok(None);
        }
        // Don't enqueue the vtable for translation by default. It will be enqueued if used in a
        // `dyn Trait`.
        let mut vtable_ref: TypeDeclRef =
            self.translate_item_maybe_enqueue(span, enqueue, tref, TransItemSourceKind::VTable)?;
        // Remove the `Self` type variable from the generic parameters.
        vtable_ref
            .generics
            .types
            .remove_and_shift_ids(TypeVarId::ZERO);

        // The vtable type also takes associated types as parameters.
        let assoc_tys: Vec<_> = tref
            .trait_associated_types(self.hax_state_with_id())
            .iter()
            .map(|ty| self.translate_ty(span, ty))
            .try_collect()?;
        vtable_ref.generics.types.extend(assoc_tys);

        Ok(Some(vtable_ref))
    }

    fn prepare_vtable_fields(
        &mut self,
        trait_def: &hax::FullDef,
        implied_predicates: &hax::GenericPredicates,
    ) -> Result<VTableData, Error> {
        let mut supertrait_map: IndexMap<TraitClauseId, _> =
            (0..implied_predicates.predicates.len())
                .map(|_| None)
                .collect();
        let mut fields = IndexVec::new();

        // Basic fields.
        fields.push(TrVTableField::Size);
        fields.push(TrVTableField::Align);
        fields.push(TrVTableField::Drop);

        // Method fields.
        if let hax::FullDefKind::Trait { items, .. } = trait_def.kind() {
            for item in items {
                let item_def_id = &item.def_id;
                // This is ok because dyn-compatible methods don't have generics.
                let item_def =
                    self.hax_def(&trait_def.this().with_def_id(self.hax_state(), item_def_id))?;
                if let hax::FullDefKind::AssocFn {
                    sig,
                    vtable_sig: Some(_),
                    ..
                } = item_def.kind()
                {
                    let name = self.translate_trait_item_name(&item_def_id)?;
                    fields.push(TrVTableField::Method(name, sig.clone()));
                }
            }
        }

        // Supertrait fields.
        for (i, (clause, _span)) in implied_predicates.predicates.iter().enumerate() {
            // If a clause looks like `Self: OtherTrait<...>`, we consider it a supertrait.
            if let hax::ClauseKind::Trait(pred) = clause.kind.hax_skip_binder_ref()
                && self.pred_is_for_self(&pred.trait_ref)
            {
                let trait_clause_id = TraitClauseId::from_raw(i);
                supertrait_map[trait_clause_id] = Some(fields.next_idx());
                fields.push(TrVTableField::SuperTrait(trait_clause_id, clause.clone()));
            }
        }

        Ok(VTableData {
            fields,
            supertrait_map,
        })
    }

    /// The Charon+Hax machinery will add Destruct super-traits to trait bounds,
    /// however for `dyn Trait` the Destruct super-trait is unexepcted, as it is not
    /// dyn-compatible.
    /// We use this function to ensure that any non dyn-compatible super-trait is
    /// Destruct and can be safely ignored.
    fn assert_is_destruct(&self, tref: &hax::TraitRef) {
        assert!(
            tref.def_id
                .as_rust_def_id()
                .is_some_and(|id| self.tcx.is_lang_item(id, rustc_hir::LangItem::Destruct)),
            "unexpected non-dyn compatible supertrait: {:?}",
            tref.def_id
        );
    }

    fn gen_vtable_struct_fields(
        &mut self,
        span: Span,
        vtable_data: &VTableData,
    ) -> Result<IndexVec<FieldId, Field>, Error> {
        let mut fields = IndexVec::new();
        let mut supertrait_counter = (0..).into_iter();
        for field in &vtable_data.fields {
            let (name, ty) = match field {
                TrVTableField::Size => ("size".into(), usize_ty()),
                TrVTableField::Align => ("align".into(), usize_ty()),
                TrVTableField::Drop => {
                    let self_ty =
                        TyKind::TypeVar(DeBruijnVar::new_at_zero(TypeVarId::ZERO)).into_ty();
                    let self_ptr = TyKind::RawPtr(self_ty, RefKind::Mut).into_ty();
                    let drop_ty = Ty::new(TyKind::FnPtr(RegionBinder::empty(FunSig {
                        is_unsafe: true,
                        inputs: [self_ptr].into(),
                        output: Ty::mk_unit(),
                    })));
                    ("drop".into(), drop_ty)
                }
                TrVTableField::Method(item_name, sig) => {
                    // It's ok to translate the method signature in the context of the trait because
                    // `vtable_sig: Some(_)` ensures the method has no generics of its own.
                    let sig = self.translate_poly_fun_sig(span, &sig)?;
                    let ty = TyKind::FnPtr(sig).into_ty();
                    let field_name = format!("method_{}", item_name.0);
                    (field_name, ty)
                }
                TrVTableField::SuperTrait(_, clause) => {
                    let vtbl_struct =
                        self.translate_region_binder(span, &clause.kind, |ctx, kind| {
                            let hax::ClauseKind::Trait(pred) = kind else {
                                unreachable!()
                            };
                            let tyref = ctx.translate_vtable_struct_ref(span, &pred.trait_ref)?;
                            if tyref.is_none() {
                                ctx.assert_is_destruct(&pred.trait_ref);
                            }
                            Ok(tyref)
                        })?;
                    // We already checked above that it's ok for this to be none.
                    let Some(vtbl_struct) = self.erase_region_binder(vtbl_struct) else {
                        continue;
                    };
                    let ty = Ty::new(TyKind::Ref(
                        Region::Static,
                        Ty::new(TyKind::Adt(vtbl_struct)),
                        RefKind::Shared,
                    ));
                    let name = format!("super_trait_{}", supertrait_counter.next().unwrap());
                    (name, ty)
                }
            };
            fields.push(Field {
                span,
                attr_info: AttrInfo::dummy_public(),
                name: Some(name),
                ty,
            });
        }
        Ok(fields)
    }

    /// This is a temporary check until we support `dyn Trait` with `--monomorphize`.
    pub(crate) fn check_no_monomorphize(&self, span: Span) -> Result<(), Error> {
        if self.monomorphize() {
            raise_error!(
                self,
                span,
                "`dyn Trait` is not yet supported with `--monomorphize`"
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
                    .push_with(|index| TypeParam { index, name });
                // Moving that type under two levels of binders: the `DynPredicate` binder and the
                // type constraint binder.
                let new_ty =
                    TyKind::TypeVar(DeBruijnVar::bound(DeBruijnId::new(2), new_ty)).into_ty();
                ty_constraint.skip_binder.ty = new_ty;
            }
            TyKind::DynTrait(dyn_pred).into_ty()
        };

        let mut field_map = IndexVec::new();
        let mut supertrait_map: IndexMap<TraitClauseId, _> =
            (0..implied_predicates.predicates.len())
                .map(|_| None)
                .collect();
        let (mut kind, layout) = if item_meta.opacity.with_private_contents().is_opaque() {
            (TypeDeclKind::Opaque, None)
        } else {
            // First construct fields that use the real method signatures (which may use the `Self`
            // type). We fixup the types and generics below.
            let vtable_data = self.prepare_vtable_fields(trait_def, implied_predicates)?;
            let fields = self.gen_vtable_struct_fields(span, &vtable_data)?;
            let kind = TypeDeclKind::Struct(fields);
            let layout = self.generate_naive_layout(span, &kind)?;
            supertrait_map = vtable_data.supertrait_map;
            field_map = vtable_data.fields.map_ref(|tr_field| match *tr_field {
                TrVTableField::Size => VTableField::Size,
                TrVTableField::Align => VTableField::Align,
                TrVTableField::Drop => VTableField::Drop,
                TrVTableField::Method(name, ..) => VTableField::Method(name),
                TrVTableField::SuperTrait(clause_id, ..) => VTableField::SuperTrait(clause_id),
            });
            (kind, Some(layout))
        };

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
            src: ItemSource::VTableTy {
                dyn_predicate: dyn_predicate.clone(),
                field_map,
                supertrait_map,
            },
            kind,
            layout,
            // A vtable struct is always sized
            ptr_metadata: PtrMetadata::None,
            repr: None,
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
        self.translate_vtable_instance_ref_maybe_enqueue(true, span, trait_ref, impl_ref)
    }

    pub fn translate_vtable_instance_ref_no_enqueue(
        &mut self,
        span: Span,
        trait_ref: &hax::TraitRef,
        impl_ref: &hax::ItemRef,
    ) -> Result<Option<GlobalDeclRef>, Error> {
        self.translate_vtable_instance_ref_maybe_enqueue(false, span, trait_ref, impl_ref)
    }

    pub fn translate_vtable_instance_ref_maybe_enqueue(
        &mut self,
        enqueue: bool,
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
        let vtable_ref: GlobalDeclRef = self.translate_item_maybe_enqueue(
            span,
            enqueue,
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
    ) -> Result<(TraitImplRef, TypeDeclRef), Error> {
        let implemented_trait = match impl_def.kind() {
            hax::FullDefKind::TraitImpl { trait_pred, .. } => &trait_pred.trait_ref,
            _ => unreachable!(),
        };
        let vtable_struct_ref = self
            .translate_vtable_struct_ref(span, implemented_trait)?
            .expect("trait should be dyn-compatible");
        let impl_ref = self.translate_item(
            span,
            impl_def.this(),
            TransItemSourceKind::TraitImpl(*impl_kind),
        )?;
        Ok((impl_ref, vtable_struct_ref))
    }

    /// E.g.,
    /// ```
    /// global {impl Trait for Foo}::vtable<Args..>: Trait::{vtable}<TraitArgs.., AssocTys..> {
    ///     size: size_of(Foo),
    ///     align: align_of(Foo),
    ///     drop: <Foo as Destruct>::drop_in_place,
    ///     method_0: <Foo as Trait>::method_0::{shim},
    ///     method_1: <Foo as Trait>::method_1::{shim},
    ///     ...
    ///     super_trait_0: SuperImpl0<..>::{vtable_instance}::<..>,
    ///     super_trait_1: SuperImpl1<..>::{vtable_instance}::<..>,
    ///     ...
    /// }
    /// ```
    pub(crate) fn translate_vtable_instance(
        mut self,
        global_id: GlobalDeclId,
        item_meta: ItemMeta,
        impl_def: &hax::FullDef,
        impl_kind: &TraitImplSource,
    ) -> Result<GlobalDecl, Error> {
        let span = item_meta.span;
        self.check_no_monomorphize(span)?;

        let (impl_ref, vtable_struct_ref) =
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
            src: ItemSource::VTableInstance { impl_ref },
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
                vtable_sig: Some(_),
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
                // generics -- the lifetime binder will be added as `Erased` in `translate_fn_ptr`.
                let item_ref = impl_def.this().with_def_id(self.hax_state(), item_def_id);
                let shim_ref =
                    self.translate_fn_ptr(span, &item_ref, TransItemSourceKind::VTableMethod)?;
                ConstantExprKind::FnDef(shim_ref)
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

            let bound_tyref =
                self.translate_region_binder(span, &impl_expr.r#trait, |ctx, tref| {
                    let tyref = ctx.translate_vtable_struct_ref(span, tref)?;
                    if tyref.is_none() {
                        ctx.assert_is_destruct(tref);
                    }
                    Ok(tyref)
                })?;
            let Some(vtable_def_ref) = self.erase_region_binder(bound_tyref) else {
                continue;
            };
            let fn_ptr_ty = TyKind::Adt(vtable_def_ref).into_ty();
            let kind = match &impl_expr.r#impl {
                hax::ImplExprAtom::Concrete(impl_item) => {
                    let bound_gref: RegionBinder<Option<GlobalDeclRef>> = self
                        .translate_region_binder(span, &impl_expr.r#trait, |ctx, tref| {
                            let gref = ctx.translate_vtable_instance_ref(span, tref, impl_item)?;
                            if gref.is_none() {
                                ctx.assert_is_destruct(tref);
                            };
                            Ok(gref)
                        })?;
                    let Some(vtable_instance_ref) = self.erase_region_binder(bound_gref) else {
                        continue;
                    };
                    let global = Box::new(ConstantExpr {
                        kind: ConstantExprKind::Global(vtable_instance_ref),
                        ty: fn_ptr_ty,
                    });
                    ConstantExprKind::Ref(global, None)
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
        let hax::FullDefKind::TraitImpl {
            trait_pred, items, ..
        } = impl_def.kind()
        else {
            unreachable!()
        };
        let trait_def = self.hax_def(&trait_pred.trait_ref)?;
        let implemented_trait = self.translate_trait_decl_ref(span, &trait_pred.trait_ref)?;
        // The type this impl is for.
        let self_ty = &implemented_trait.generics.types[0];

        let mut builder = BodyBuilder::new(span, 0);
        let ret_ty = Ty::new(TyKind::Adt(vtable_struct_ref.clone()));
        let ret_place = builder.new_var(Some("ret".into()), ret_ty.clone());

        // Retreive the expected field types from the struct definition. This avoids complicated
        // substitutions.
        let field_tys = {
            let vtable_decl_id = vtable_struct_ref.id.as_adt().unwrap().clone();
            let ItemRef::Type(vtable_def) = self.t_ctx.get_or_translate(vtable_decl_id.into())?
            else {
                unreachable!()
            };
            let fields = match &vtable_def.kind {
                TypeDeclKind::Struct(fields) => fields,
                TypeDeclKind::Opaque => return Ok(Body::Opaque),
                TypeDeclKind::Error(error) => return Err(Error::new(span, error.clone())),
                _ => unreachable!(),
            };
            fields
                .iter()
                .map(|f| &f.ty)
                .cloned()
                .map(|ty| ty.substitute(&vtable_struct_ref.generics))
                .collect_vec()
        };

        let mut aggregate_fields = vec![];
        // For each vtable field, assign the desired value to a new local.
        let mut field_ty_iter = field_tys.into_iter();

        let size_ty = field_ty_iter.next().unwrap();
        let size_local = builder.new_var(Some("size".to_string()), size_ty);
        builder.push_statement(StatementKind::Assign(
            size_local.clone(),
            Rvalue::NullaryOp(NullOp::SizeOf, self_ty.clone()),
        ));
        aggregate_fields.push(Operand::Move(size_local));

        let align_ty = field_ty_iter.next().unwrap();
        let align_local = builder.new_var(Some("align".to_string()), align_ty);
        builder.push_statement(StatementKind::Assign(
            align_local.clone(),
            Rvalue::NullaryOp(NullOp::AlignOf, self_ty.clone()),
        ));
        aggregate_fields.push(Operand::Move(align_local));

        // Helper to fill in the remaining fields with constant values.
        let mut mk_field = |kind| {
            let ty = field_ty_iter.next().unwrap();
            aggregate_fields.push(Operand::Const(Box::new(ConstantExpr { kind, ty })));
        };

        let drop_shim =
            self.translate_item(span, impl_def.this(), TransItemSourceKind::VTableDropShim)?;

        mk_field(ConstantExprKind::FnDef(drop_shim));

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
        builder.push_statement(StatementKind::Assign(
            ret_place,
            Rvalue::Aggregate(
                AggregateKind::Adt(vtable_struct_ref.clone(), None, None),
                aggregate_fields,
            ),
        ));

        Ok(Body::Unstructured(builder.build()))
    }

    pub(crate) fn translate_vtable_instance_init(
        mut self,
        init_func_id: FunDeclId,
        item_meta: ItemMeta,
        impl_def: &hax::FullDef,
        impl_kind: &TraitImplSource,
    ) -> Result<FunDecl, Error> {
        let span = item_meta.span;
        self.check_no_monomorphize(span)?;

        let (impl_ref, vtable_struct_ref) =
            self.get_vtable_instance_info(span, impl_def, impl_kind)?;
        let init_for = self.register_item(
            span,
            impl_def.this(),
            TransItemSourceKind::VTableInstance(*impl_kind),
        );

        // Signature: `() -> VTable`.
        let sig = FunSig {
            is_unsafe: false,
            inputs: vec![],
            output: Ty::new(TyKind::Adt(vtable_struct_ref.clone())),
        };

        let body = match impl_kind {
            _ if item_meta.opacity.with_private_contents().is_opaque() => Body::Opaque,
            TraitImplSource::Normal => {
                self.gen_vtable_instance_init_body(span, impl_def, vtable_struct_ref)?
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
            generics: self.into_generics(),
            signature: sig,
            src: ItemSource::VTableInstance { impl_ref },
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
        let mut builder = BodyBuilder::new(span, shim_signature.inputs.len());

        let ret_place = builder.new_var(None, shim_signature.output.clone());
        let mut method_args = shim_signature
            .inputs
            .iter()
            .map(|ty| builder.new_var(None, ty.clone()))
            .collect_vec();
        let target_self = builder.new_var(None, target_receiver.clone());

        // Replace the `dyn Trait` receiver with the concrete one.
        let shim_self = mem::replace(&mut method_args[0], target_self.clone());

        // Perform the core concretization cast.
        // FIXME: need to unpack & re-pack the structure for cases like `Rc`, `Arc`, `Pin` and
        // (when --raw-boxes is on) `Box`
        let rval = Rvalue::UnaryOp(
            UnOp::Cast(CastKind::Concretize(
                shim_self.ty().clone(),
                target_self.ty().clone(),
            )),
            Operand::Move(shim_self.clone()),
        );
        builder.push_statement(StatementKind::Assign(target_self.clone(), rval));

        let fun_id = self.register_item(span, &impl_func_def.this(), TransItemSourceKind::Fun);
        let generics = self.outermost_binder().params.identity_args();
        builder.call(Call {
            func: FnOperand::Regular(FnPtr::new(FnPtrKind::Fun(fun_id), generics)),
            args: method_args
                .into_iter()
                .map(|arg| Operand::Move(arg))
                .collect(),
            dest: ret_place,
        });

        Ok(Body::Unstructured(builder.build()))
    }

    /// The target vtable drop_shim body looks like:
    /// ```ignore
    /// local ret@0 : ();
    /// // the shim receiver of this drop_shim function
    /// local shim_self@1 : ShimReceiverTy;
    /// // the target receiver of the drop_shim
    /// local target_self@2 : TargetReceiverTy;
    /// // perform some conversion to cast / re-box the drop_shim receiver to the target receiver
    /// target_self@2 := concretize_cast<ShimReceiverTy, TargetReceiverTy>(shim_self@1);
    /// Drop(*target_self@2);
    /// ```
    fn translate_vtable_drop_shim_body(
        &mut self,
        span: Span,
        shim_receiver: &Ty,
        target_receiver: &Ty,
        trait_pred: &TraitPredicate,
    ) -> Result<Body, Error> {
        let mut builder = BodyBuilder::new(span, 1);

        builder.new_var(Some("ret".into()), Ty::mk_unit());
        let dyn_self = builder.new_var(Some("dyn_self".into()), shim_receiver.clone());
        let target_self = builder.new_var(Some("target_self".into()), target_receiver.clone());

        // Perform the core concretization cast.
        let rval = Rvalue::UnaryOp(
            UnOp::Cast(CastKind::Concretize(
                dyn_self.ty().clone(),
                target_self.ty().clone(),
            )),
            Operand::Move(dyn_self.clone()),
        );
        builder.push_statement(StatementKind::Assign(target_self.clone(), rval));

        // Build a reference to `impl Destruct for T`. Given the
        // target_receiver type `T`, use Hax to solve `T: Destruct`
        // and translate the resolved result to `TraitRef` of the
        // `drop_in_place`
        let destruct_trait = self.tcx.lang_items().destruct_trait().unwrap();
        let impl_expr: hax::ImplExpr = {
            let s = self.hax_state_with_id();
            let rustc_trait_args = trait_pred.trait_ref.rustc_args(s);
            let generics = self.tcx.mk_args(&rustc_trait_args[..1]); // keep only the `Self` type
            let tref =
                rustc_middle::ty::TraitRef::new_from_args(self.tcx, destruct_trait, generics);
            hax::solve_trait(s, rustc_middle::ty::Binder::dummy(tref))
        };
        let tref = self.translate_trait_impl_expr(span, &impl_expr)?;

        // Drop(*target_self)
        let drop_arg = target_self.clone().deref();
        builder.insert_drop(drop_arg, tref);

        Ok(Body::Unstructured(builder.build()))
    }

    pub(crate) fn translate_vtable_drop_shim(
        mut self,
        fun_id: FunDeclId,
        item_meta: ItemMeta,
        impl_def: &hax::FullDef,
    ) -> Result<FunDecl, Error> {
        let span = item_meta.span;

        let hax::FullDefKind::TraitImpl {
            dyn_self: Some(dyn_self),
            trait_pred,
            ..
        } = impl_def.kind()
        else {
            raise_error!(
                self,
                span,
                "Trying to generate a vtable drop shim for a non-trait impl"
            );
        };

        // `*mut dyn Trait`
        let ref_dyn_self =
            TyKind::RawPtr(self.translate_ty(span, dyn_self)?, RefKind::Mut).into_ty();
        // `*mut T` for `impl Trait for T`
        let ref_target_self = {
            let impl_trait = self.translate_trait_ref(span, &trait_pred.trait_ref)?;
            TyKind::RawPtr(impl_trait.generics.types[0].clone(), RefKind::Mut).into_ty()
        };

        // `*mut dyn Trait -> ()`
        let signature = FunSig {
            is_unsafe: true,
            inputs: vec![ref_dyn_self.clone()],
            output: Ty::mk_unit(),
        };

        let body: Body = self.translate_vtable_drop_shim_body(
            span,
            &ref_dyn_self,
            &ref_target_self,
            trait_pred,
        )?;

        Ok(FunDecl {
            def_id: fun_id,
            item_meta,
            generics: self.into_generics(),
            signature,
            src: ItemSource::VTableMethodShim,
            is_global_initializer: None,
            body,
        })
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
            vtable_sig: Some(vtable_sig),
            sig: target_signature,
            ..
        } = impl_func_def.kind()
        else {
            raise_error!(
                self,
                span,
                "Trying to generate a vtable shim for a non-vtable-safe method"
            );
        };

        // The signature of the shim function.
        let signature = self.translate_fun_sig(span, &vtable_sig.value)?;
        // The concrete receiver we will cast to.
        let target_receiver = self.translate_ty(span, &target_signature.value.inputs[0])?;

        trace!(
            "[VtableShim] Obtained dyn signature with receiver type: {}",
            signature.inputs[0].with_ctx(&self.into_fmt())
        );

        let body = if item_meta.opacity.with_private_contents().is_opaque() {
            Body::Opaque
        } else {
            self.translate_vtable_shim_body(span, &target_receiver, &signature, impl_func_def)?
        };

        Ok(FunDecl {
            def_id: fun_id,
            item_meta,
            generics: self.into_generics(),
            signature,
            src: ItemSource::VTableMethodShim,
            is_global_initializer: None,
            body,
        })
    }
}
