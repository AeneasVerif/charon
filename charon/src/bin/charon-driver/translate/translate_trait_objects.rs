use std::mem;
use std::ops::ControlFlow::Continue;

use crate::translate::translate_bodies::BodyTransCtx;
use crate::translate::translate_crate::RustcItem;
use crate::translate::translate_types;

use crate::translate::{translate_generics::BindingLevel, translate_predicates::PredicateLocation};

use super::translate_ctx::*;
use charon_lib::ast::*;
use charon_lib::llbc_ast::Block;
use hax_frontend_exporter::{self as hax};
use petgraph::matrix_graph::Zero;

use super::translate_ctx::*;
use charon_lib::ast::*;
use charon_lib::formatter::IntoFormatter;
use charon_lib::ids::Vector;
use charon_lib::pretty::FmtWithCtx;
use charon_lib::ullbc_ast::*;
use itertools::Itertools;
use tracing::field;
use super::{
    translate_crate::TransItemSourceKind, translate_ctx::*
};

use charon_lib::ullbc_ast::*;

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

fn usize_ty() -> Ty {
    Ty::new(TyKind::Literal(LiteralTy::UInt(UIntTy::Usize)))
}

/// Field: `self_ty_size: usize`
fn size_field() -> Field {
    Field {
        span: Span::dummy(),
        attr_info: dummy_public_attr_info(),
        name: Some("self_ty_size".into()),
        ty: usize_ty(),
    }
}

/// Shift the bounded type variables in the given type by the specified distance.
/// It can be positive or negative, for both the DB level & id at the same level
///
/// Note: it only shifts those bounded outside, the internally bounded variables are left intact
fn shift_bounded_ty_vars(ty: &mut Ty, db_distance: isize, distance: isize) {
    struct SelfVisitor(isize, isize);
    impl VarsVisitor for SelfVisitor {
        fn visit_type_var(&mut self, v: TypeDbVar) -> Option<Ty> {
            let SelfVisitor(db_shift, shift) = self;
            if let DeBruijnVar::Bound(db_id, idx) = v {
                let DeBruijnId { index: id } = db_id;
                let db_id = DeBruijnId {
                    index: if *db_shift < 0 {
                        assert!(db_shift.abs() as usize <= id);
                        id - (-*db_shift as usize)
                    } else {
                        id + (*db_shift as usize)
                    },
                };
                let idx = if *shift < 0 {
                    assert!(shift.abs() as usize <= idx);
                    idx - TypeVarId::from_raw(-*shift as usize)
                } else {
                    idx + TypeVarId::from_raw(*shift as usize)
                };
                Some(Ty::new(TyKind::TypeVar(DeBruijnVar::Bound(db_id, idx))))
            } else {
                None
            }
        }
    }
    ty.visit_vars(&mut SelfVisitor(db_distance, distance));
}

fn shift_db_vars<T: TyVisitable, F: Fn(usize) -> usize>(ty: &mut T, f: F) {
    let _ = ty.visit_db_id(|db_id| {
        *db_id = DeBruijnId {
            index: f(db_id.index),
        };
        Continue::<()>(())
    });
}

/// Field: `self_ty_align: usize`
fn align_field() -> Field {
    Field {
        span: Span::dummy(),
        attr_info: dummy_public_attr_info(),
        name: Some("self_ty_align".into()),
        ty: usize_ty(),
    }
}

/// Remove the first `Self` type variable from the generic parameters.
fn remove_self_from_params(params: &mut GenericParams) {
    params.types.remove_and_shift_ids(TypeVarId::ZERO);
    params.types.iter_mut().for_each(|ty| {
        ty.index -= 1;
    });
}

// fn dummy_public_attr_info() -> AttrInfo {
//     AttrInfo {
//         public: true,
//         ..Default::default()
//     }
// }

// fn usize_ty() -> Ty {
//     Ty::new(TyKind::Literal(LiteralTy::UInt(UIntTy::Usize)))
// }

/// Takes a `T` valid in the context of a trait ref and transforms it into a `T` valid in the
/// context of its vtable definition, i.e. no longer mentions `Self`. If `new_self` is `Some`, we
/// replace any mention of `Self` with it; otherwise we panic if `Self` is mentioned.
fn dynify<T: TyVisitable>(mut x: T, new_self: Option<Ty>) -> T {
    struct ReplaceSelfVisitor(Option<Ty>);
    impl VarsVisitor for ReplaceSelfVisitor {
        fn visit_type_var(&mut self, v: TypeDbVar) -> Option<Ty> {
            if let DeBruijnVar::Bound(DeBruijnId::ZERO, type_id) = v {
                // Replace type 0 and decrement the others.
                Some(if let Some(new_id) = type_id.index().checked_sub(1) {
                    TyKind::TypeVar(DeBruijnVar::Bound(DeBruijnId::ZERO, TypeVarId::new(new_id)))
                        .into_ty()
                } else {
                    self.0.clone().expect(
                        "Found unexpected `Self` 
                        type when constructing vtable",
                    )
                })
            } else {
                None
            }
        }
    }
    x.visit_vars(&mut ReplaceSelfVisitor(new_self));
    x
}

//// Translate the `dyn Trait` type.
impl ItemTransCtx<'_, '_> {
    fn is_for_self(&self, poly_trait_ref: &RegionBinder<TraitDeclRef>) -> bool {
        // If the trait reference is not pointing to `Self`, it is not a super trait
        let types = &poly_trait_ref.skip_binder.generics.types;
        if types.is_empty() {
            return false;
        }
        // The outermost type variable should be where `Self` is
        // The level should be binding_levels.len() - 1, but there is one more level
        // of the `RegionBinder`, so we need to increase it by 1.
        let out_most_level = self.binding_levels.len();
        match types[0].kind() {
            TyKind::TypeVar(DeBruijnVar::Bound(lv, TypeVarId::ZERO)) => lv.index == out_most_level,
            TyKind::TypeVar(DeBruijnVar::Free(TypeVarId::ZERO)) => true,
            // If it is a type variable, it should be bound to `Self`
            TyKind::TypeVar(DeBruijnVar::Bound(_, _)) => false,
            _ => false,
        }
    }

    /// Field: `drop_func: *mut dyn Trait<'a, ..., T, ...> -> ()`
    fn drop_func_field(&mut self, tref: TraitDeclRef) -> Field {
        // *mut Self
        let ptr_self = Ty::new(TyKind::RawPtr(
            Ty::new(TyKind::TypeVar(DeBruijnVar::Bound(
                DeBruijnId {
                    index: self.binding_levels.len() - 1,
                },
                TypeVarId::ZERO,
            ))),
            RefKind::Mut,
        ));
        // *mut dyn Trait<'a, ..., T, ...>
        let mut shim_ty = self.receiver_ty_to_shim_ty(Span::dummy(), tref, &ptr_self);
        // to shift the bounds --- remove `Self` & shift DB for `RegionBinder`
        shift_db_vars(&mut shim_ty, |v| v + 1);
        self.ty_shift_for_removed_self(&mut shim_ty);
        Field {
            span: Span::dummy(),
            attr_info: dummy_public_attr_info(),
            name: Some("drop_func".into()),
            ty: Ty::new(TyKind::FnPtr(RegionBinder {
                regions: Vector::new(),
                skip_binder: (Vec::from([shim_ty]), Ty::mk_unit()),
            })),
        }
    }

    fn common_vtable_entries(&mut self, tref: TraitDeclRef) -> Vector<FieldId, Field> {
        let mut ret = Vector::new();
        ret.push(self.drop_func_field(tref));
        ret.push(size_field());
        ret.push(align_field());
        ret
    }

    fn add_parent_trait_vtable_ptrs(
        &mut self,
        fields: &mut Vector<FieldId, Field>,
        parent_clauses: &Vector<TraitClauseId, (hax::TraitPredicate, TraitClause)>,
    ) -> Result<(), Error> {
        trace!(
            "Adding parent trait vtable pointers for: {}",
            parent_clauses
                .iter()
                .map(|(_, c)| c.with_ctx(&self.into_fmt()).to_string())
                .join(", ")
        );
        for (idx, (pred, clause)) in parent_clauses.iter_indexed_values() {
            let poly_trait_ref = &clause.trait_;
            // The trait reference is pointing to `Self` iff it is a super trait
            // If it is not a super trait, skip it
            if !self.is_for_self(poly_trait_ref) {
                trace!(
                    "Skipping non-self trait reference: {}",
                    poly_trait_ref.with_ctx(&self.into_fmt())
                );
                continue;
            }
            // FIXME: is it correct to use `skip_binder`? -- it might lose the newly binded regions
            let mut generics = poly_trait_ref.skip_binder.generics.clone();
            // So that generics correspond to the `skip_binder`
            shift_db_vars(&mut generics, |v| v - 1);
            // remove the `Self` type argument from the generics
            generics.types.remove_and_shift_ids(TypeVarId::ZERO);
            // Also skip the poly binder
            // It is guanranteed by Rustc that the reference to `Self` can only appear in the first position
            generics
                .types
                .iter_mut()
                .for_each(|ty| self.ty_shift_for_removed_self(ty));
            let def_id = &pred.trait_ref.def_id;
            let id = self.register_and_enqueue(Span::dummy(), TransItemSource { item: RustcItem::Poly(def_id.clone()), kind: TransItemSourceKind::VTable });
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
    ///
    /// NOTE: the converted shim type will continue to keep the current generic environment
    /// To remove `Self`, note to call `self.ty_shift_for_removed_self`
    fn receiver_ty_to_shim_ty(&mut self, span: Span, tref: TraitDeclRef, in_ty: &Ty) -> Ty {
        trace!(
            "Converting into shim type for: `{}`",
            in_ty.with_ctx(&self.into_fmt())
        );
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
                name: String::from("_dyn"),
            });
        let ty = TyKind::TypeVar(DeBruijnVar::new_at_zero(ty_id)).into_ty();

        let mut params = self.binding_levels.pop().unwrap().params;

        // the trait decl ref: `Trait<'a, ..., T, ..., const N = ?, ...>`
        let mut args = tref.generics;
        // The DB shifting level should be: binding_levels.len() - 1 to refer to the top here
        // But as the reference is behind a `RegionBinder`, we need to shift it by `+ 1`
        // Also, the predicate itself is within a level, hence, it is shifted by `+ 1` as well.
        // So, the final shift is `binding_levels.len() + 1` = `binding_levels.len() - 1 + 1 + 1`
        let levels = self.binding_levels.len() + 1;
        // the args should refer to the top level binder, with the sole exception that
        // the `Self` type variable should refer to the `_dyn` above
        shift_db_vars(&mut args, |id| id + levels);
        let trait_decl_ref = TraitDeclRef {
            id: tref.id,
            generics: args,
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
        trace!(
            "Target shim type: `{}`",
            target_ty.with_ctx(&self.into_fmt())
        );

        let self_level = self.binding_levels.len() - 1;
        // Then, replace every `Self` in the type with the target type
        #[derive(Clone)]
        struct SelfVisitor(usize, Ty);
        impl VarsVisitor for SelfVisitor {
            fn visit_type_var(&mut self, v: TypeDbVar) -> Option<Ty> {
                let SelfVisitor(self_level, target_ty) = self.clone();
                if let DeBruijnVar::Bound(lv, TypeVarId::ZERO) = v
                    && lv.index == self_level
                {
                    Some(target_ty)
                } else {
                    None
                }
            }
        }
        let mut ty = in_ty.clone();
        ty.visit_vars(&mut SelfVisitor(self_level, target_ty));
        trace!("Converted shim type: `{}`", ty.with_ctx(&self.into_fmt()));
        ty
    }

    /// When the `Self` type variable is removed, we need to shift the other bounded type variables.
    /// Namely, for types with sub-part `TBound(outmost, i)`, we need to shift `i` by `-1` as now `Self` is gone.
    fn ty_shift_for_removed_self(&self, ty: &mut Ty) {
        let outmost_level = self.binding_levels.len() - 1;
        struct SelfVisitor(usize);
        impl VarsVisitor for SelfVisitor {
            fn visit_type_var(&mut self, v: TypeDbVar) -> Option<Ty> {
                let SelfVisitor(outmost_level) = self;
                if let DeBruijnVar::Bound(lv, i) = v
                    && lv.index == *outmost_level
                {
                    assert!(i > 0);
                    Some(Ty::new(TyKind::TypeVar(DeBruijnVar::Bound(lv, i - 1))))
                } else {
                    None
                }
            }
        }
        ty.visit_vars(&mut SelfVisitor(outmost_level));
    }

    /// The hax function signature to its vtable shim type.
    fn sig_to_shim_ty(
        &mut self,
        span: Span,
        tref: TraitDeclRef,
        sig: &hax::TyFnSig,
    ) -> Result<Ty, Error> {
        let mut in_tys: Vec<Ty> = sig
            .inputs
            .iter()
            .map(|ty| self.translate_ty(span, ty))
            .try_collect()?;
        // take out the first element of `in_tys` and modify it to the shim type
        in_tys[0] = self.receiver_ty_to_shim_ty(span, tref, &in_tys[0]);
        trace!(
            "Obtained shim type: {}",
            in_tys[0].with_ctx(&self.into_fmt())
        );
        in_tys.iter_mut().for_each(|ty| {
            trace!(
                "To shift for removed self for fun sig in-type: {}\nIts original type is: {:?}",
                ty.with_ctx(&self.into_fmt()),
                ty
            );
            self.ty_shift_for_removed_self(ty)
        });
        let mut out_ty = self.translate_ty(span, &sig.output)?;
        self.ty_shift_for_removed_self(&mut out_ty);
        // it is safe to take only the region binder here
        // as Rustc guarantees that only generic Region is allowed
        // by dyn-compatibility
        let ty = Ty::new(TyKind::FnPtr(RegionBinder {
            regions: self.innermost_binder().params.regions.clone(),
            skip_binder: (in_tys, out_ty),
        }));
        Ok(ty)
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
                    let func_def = self.poly_hax_def(func_def_id)?;
                    let trait_decl_id = self.register_and_enqueue(span,
                        TransItemSource {
                            item: RustcItem::Poly(trait_id.clone()),
                            kind: TransItemSourceKind::VTable,
                        });
                    let binder_kind = BinderKind::TraitMethod(trait_decl_id, item_name.clone());

                    // prepare the shim type
                    let shim_ty = self
                        .translate_binder_for_def(span, binder_kind, &func_def, |tcx| {
                            let sig = &sig.value;
                            let args = tcx.outermost_binder().params.identity_args();
                            let tref = TraitDeclRef {
                                id: trait_decl_id,
                                generics: Box::new(args),
                            };
                            tcx.sig_to_shim_ty(span, tref, sig)
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

    // fn gen_vtable_struct_fields(
    //     &mut self,
    //     span: Span,
    //     trait_full_def: &hax::FullDef,
    // ) -> Result<Vector<FieldId, Field>, Error> {
    //     let trait_def_id = trait_full_def.def_id();
    //     let trait_args = self.outermost_binder().params.identity_args();
    //     let tref = TraitDeclRef {
    //         id: self.register_trait_decl_id(span, &trait_def_id),
    //         generics: Box::new(trait_args),
    //     };
    //     let mut fields = self.common_vtable_entries(tref);

    //     // translate the super pointers
    //     let parent_clauses = mem::take(&mut self.parent_trait_clauses);
    //     self.add_parent_trait_vtable_ptrs(&mut fields, &parent_clauses)?;

    //     // if it is a trait definition, we need to add the methods
    //     if let hax::FullDefKind::Trait { items, .. } = &trait_full_def.kind() {
    //         self.add_vtable_methods_from_trait_items(span, trait_def_id, &mut fields, items)?;
    //     } else {
    //         // else, it should be a trait alias, which should not have any methods in its vtable
    //         // assert here for robustness
    //         assert!(matches!(
    //             trait_full_def.kind(),
    //             hax::FullDefKind::TraitAlias { .. }
    //         ));
    //     }

    //     Ok(fields)
    // }

    // /// the true layout of the vtable:
    // /// [ drop_func : *mut () -> (),
    // ///   self_ty_size : usize,
    // ///   self_ty_align : usize,
    // ///   ...  -- the super trait vtables
    // ///   ...  -- the method list ]
    // pub(crate) fn translate_vtable_struct(
    //     mut self,
    //     typ_id: TypeDeclId,
    //     item_meta: ItemMeta,
    //     trait_full_def: &hax::FullDef,
    // ) -> Result<TypeDecl, Error> {
    //     // start by getting the generic environment ready
    //     self.translate_def_generics(Span::dummy(), trait_full_def)?;
    //     let fields = self.gen_vtable_struct_fields(item_meta.span, trait_full_def)?;

    //     // take out the required stuff before consuming `self`
    //     let ptr_size = self.t_ctx.translated.target_information.target_pointer_size;
    //     let trait_id = self.register_trait_decl_id(Span::dummy(), &trait_full_def.def_id);
    //     // consumes `self` to get the generics
    //     let mut generics = self.into_generics();
    //     // remove the `Self` type variable from the generic parameters
    //     remove_self_from_params(&mut generics);
    //     let ptr_align = ptr_size;
    //     let layout = Layout {
    //         // everything is of the same size as a pointer
    //         size: Some((fields.iter().count() as u64) * ptr_size),
    //         align: Some(ptr_align as u64),
    //         discriminant_layout: None,
    //         uninhabited: false,
    //         variant_layouts: Vector::new(),
    //     };
    //     let trait_decl_ref = TraitDeclRef {
    //         id: trait_id,
    //         generics: Box::new(generics.identity_args()),
    //     };

    //     Ok(TypeDecl {
    //         def_id: typ_id,
    //         item_meta: item_meta,
    //         generics: generics,
    //         src: ItemKind::VTable {
    //             trait_decl_ref: trait_decl_ref,
    //         },
    //         kind: TypeDeclKind::Struct(fields),
    //         layout: Some(layout),
    //         // There is definitely no metadata associated with this type
    //         ptr_metadata: None,
    //     })
    // }

    // /// E.g.,
    // /// global <T..., VT...>
    // ///     trait::{vtable_instance}::<ImplTy<T...>> :
    // ///         trait::{vtable}<VT...> = trait::{vtable}<VT...> {
    // ///     drop_func: &ignore / &<ImplTy<T...> as Drop>::drop,
    // ///     size: size_of(<ImplTy<T...>>),
    // ///     align: align_of(<ImplTy<T...>>),
    // ///     super_trait_0: &SuperTrait0<VT...>::{vtable_instance}::<ImplTy<T...>>,
    // ///     super_trait_1: &SuperTrait1<VT...>::{vtable_instance}::<ImplTy<T...>>,
    // ///     ...
    // ///     method_0: &<ImplTy<T...> as Trait>::method_0::{shim},
    // ///     method_1: &<ImplTy<T...> as Trait>::method_1::{shim},
    // ///     ...
    // /// }
    // pub(crate) fn translate_vtable_instance(
    //     mut self,
    //     glob_id: GlobalDeclId,
    //     item_meta: ItemMeta,
    //     trait_impl_def: &hax::FullDef,
    //     maybe_target_kind: Option<ClosureKind>,
    // ) -> Result<GlobalDecl, Error> {
    //     // prepare the generic environment
    //     self.translate_def_generics(item_meta.span, trait_impl_def)?;
    //     let init = self.register_vtable_instance_body_as_fun_decl_id(
    //         item_meta.span,
    //         &trait_impl_def.def_id,
    //         maybe_target_kind,
    //     );

    //     let (vtable_struct_ref, trait_decl_ref) =
    //         self.get_vtable_instance_info(item_meta.span, trait_impl_def, maybe_target_kind)?;

    //     Ok(GlobalDecl {
    //         def_id: glob_id,
    //         item_meta,
    //         generics: self.into_generics(),
    //         kind: ItemKind::VTable { trait_decl_ref },
    //         // it should be static to have its own address
    //         global_kind: GlobalKind::Static,
    //         ty: Ty::new(TyKind::Adt(vtable_struct_ref)),
    //         init,
    //     })
    // }

    // /// Local helper function to get the vtable struct reference and trait declaration reference
    // /// Should be called after the generic environment is set up
    // fn get_vtable_instance_info<'a>(
    //     &mut self,
    //     span: Span,
    //     trait_impl_def: &'a hax::FullDef,
    //     maybe_target_kind: Option<ClosureKind>,
    // ) -> Result<(TypeDeclRef, TraitDeclRef), Error> {
    //     let implemented_trait = match trait_impl_def.kind() {
    //         hax::FullDefKind::TraitImpl { trait_pred, .. } => &trait_pred.trait_ref,
    //         hax::FullDefKind::Closure {
    //             fn_once_impl,
    //             fn_mut_impl,
    //             fn_impl,
    //             ..
    //         } => {
    //             // It is guaranteed that the `maybe_target_kind` is `Some` here
    //             let vimpl = match maybe_target_kind.unwrap() {
    //                 ClosureKind::FnOnce => fn_once_impl,
    //                 ClosureKind::FnMut => fn_mut_impl.as_ref().unwrap(),
    //                 ClosureKind::Fn => fn_impl.as_ref().unwrap(),
    //             };
    //             &vimpl.trait_pred.trait_ref
    //         }
    //         _ => unreachable!(),
    //     };
    //     let vtable_id = self.register_vtable_as_type_decl_id(span, &implemented_trait.def_id);
    //     let tref = self.translate_trait_ref(span, implemented_trait)?;
    //     let mut generics = tref.generics.clone();
    //     // remove the `Self` type argument from the generics
    //     generics.types.remove_and_shift_ids(TypeVarId::ZERO);
    //     let vtable_struct_ref = TypeDeclRef {
    //         id: TypeId::Adt(vtable_id),
    //         generics,
    //     };
    //     Ok((vtable_struct_ref, tref))
    // }

    fn add_parent_ptr_to_vtable_instance_func_body(
        &mut self,
        // The trait predicate for the trait implementation, i.e., the current implemented trait.
        _trait_pred: &hax::TraitPredicate,
        // The implied impl expressions for the trait implementation.
        implied_impl_exprs: &Vec<hax::ImplExpr>,
        locals: &mut Vector<LocalId, Local>,
        statements: &mut Vec<llbc_ast::Statement>,
    ) -> Result<(), Error> {
        for impl_expr in implied_impl_exprs {
            match &impl_expr.r#impl {
                hax::ImplExprAtom::Concrete(item) => {
                    let poly_trait_ref =
                        self.translate_poly_trait_ref(Span::dummy(), &impl_expr.r#trait)?;
                    // It is not for `Self`, so it is not a parent trait impl expression.
                    if !self.is_for_self(&poly_trait_ref) {
                        continue;
                    }

                    // add a pointer to the parent vtable instance, the reference to the item
                    // get the instance
                    let parent_vtable_instance_id =
                        self.register_and_enqueue(Span::dummy(), TransItemSource {
                            item: RustcItem::Poly(item.def_id.clone()),
                            kind: TransItemSourceKind::VTableInstance(
                                TraitImplSource::Normal,
                            ),
                        });
                    let impl_ref = self.translate_trait_impl_ref(Span::dummy(), item, TraitImplSource::Normal)?;
                    let mut generics = impl_ref.generics.clone();
                    // remove the `Self` type argument from the generics
                    generics.types.remove_and_shift_ids(TypeVarId::ZERO);
                    let vtable_instance_ref = GlobalDeclRef {
                        id: parent_vtable_instance_id,
                        generics,
                    };

                    // get the struct type
                    let vtable_struct_id = self.register_and_enqueue(Span::dummy(), TransItemSource {
                        item: RustcItem::Poly(impl_expr.r#trait.value.def_id.clone()),
                        kind: TransItemSourceKind::VTable,
                    });
                    // otherwise, we are losing the newly binded regions
                    assert!(poly_trait_ref.regions.is_empty());
                    let mut generics = poly_trait_ref.skip_binder.generics.clone();
                    generics.types.remove_and_shift_ids(TypeVarId::ZERO);
                    // shift to correspond to `skip_binder`
                    let _ = generics.visit_db_id(|db_id| {
                        *db_id = DeBruijnId {
                            index: db_id.index - 1,
                        };
                        Continue::<()>(())
                    });
                    let vtable_struct_ref = TypeDeclRef {
                        id: TypeId::Adt(vtable_struct_id),
                        generics,
                    };

                    // push new locals
                    let local = locals.push_with(|idx| Local {
                        index: idx,
                        name: Some(format!("parent_vtable_instance_{}", idx)),
                        ty: Ty::new(TyKind::RawPtr(
                            Ty::new(TyKind::Adt(vtable_struct_ref.clone())),
                            RefKind::Shared,
                        )),
                    });
                    // add the assignment statement
                    let assn: llbc_ast::Statement = llbc_ast::Statement::new(
                        Span::dummy(),
                        llbc_ast::RawStatement::Assign(
                            Place {
                                kind: PlaceKind::Local(local),
                                ty: Ty::new(TyKind::RawPtr(
                                    Ty::new(TyKind::Adt(vtable_struct_ref)),
                                    RefKind::Shared,
                                )),
                            },
                            Rvalue::GlobalRef(vtable_instance_ref, RefKind::Shared),
                        ),
                    );
                    statements.push(assn);
                }
                _ => { /* Do nothing, as they are not parent trait impl expressions. */ }
            }
        }
        Ok(())
    }

    /// This function combines each level of Generic parameters' identity arguments
    /// into a single `GenericArgs` object, the order is from the outermost to the innermost.
    pub fn combined_identity_args(&self) -> GenericArgs {
        let mut args = GenericArgs::empty();
        for (level, binding) in self.binding_levels.iter_enumerated().rev() {
            args = args.concat(&binding.params.identity_args_at_depth(level));
        }
        args
    }

    fn add_vtable_methods_to_vtable_instance_func_body(
        &mut self,
        tref: &TraitDeclRef,
        items: &Vec<hax::ImplAssocItem>,
        locals: &mut Vector<LocalId, Local>,
        statements: &mut Vec<llbc_ast::Statement>,
    ) -> Result<(), Error> {
        for item in items {
            let def = self.poly_hax_def(item.def_id())?;
            let item_span = self.def_span(def.def_id());
            match def.kind() {
                hax::FullDefKind::AssocFn { sig, .. } => {
                    // get the shim type, Rustc guarantees that the latest level of binder can only be `RegionBinder`
                    let func_shim_ty = self
                        .translate_region_binder(item_span, sig, |bt_ctx, sig| {
                            bt_ctx.sig_to_shim_ty(item_span, tref.clone(), sig)
                        })?
                        .skip_binder;

                    // get the shim ref
                    let func_shim_ref = FunDeclRef {
                        id: self.register_and_enqueue(item_span, TransItemSource { item: RustcItem::Poly(def.def_id().clone()), kind: TransItemSourceKind::VTable }),
                        generics: Box::new(self.combined_identity_args()),
                    };

                    // create a local for the shim
                    let method_name = self.t_ctx.translate_trait_item_name(def.def_id())?;
                    let local = locals.push_with(|idx| Local {
                        index: idx,
                        name: Some(method_name.to_string()),
                        ty: func_shim_ty.clone(),
                    });
                    // add the assignment statement:
                    //   local := &func_shim_ref
                    statements.push(llbc_ast::Statement::new(
                        item_span,
                        llbc_ast::RawStatement::Assign(
                            Place {
                                kind: PlaceKind::Local(local),
                                ty: func_shim_ty.clone(),
                            },
                            Rvalue::Use(Operand::Const(Box::new(ConstantExpr {
                                value: RawConstantExpr::FnPtr(FnPtr {
                                    func: Box::new(FunIdOrTraitMethodRef::Fun(FunId::Regular(
                                        func_shim_ref.id,
                                    ))),
                                    generics: func_shim_ref.generics,
                                }),
                                ty: func_shim_ty,
                            }))),
                        ),
                    ));
                }
                _ => { /* Only Assoc-Funcs are required for vtable */ }
            }
        }
        Ok(())
    }

    /// Generate the body of the vtable instance function.
    /// This is for `impl Trait for T` implementation, it does NOT handle closures.
    /// ```no_run
    /// let ret@0 : VTable;
    /// ret@0 = VTable { ... };
    /// return;
    /// ```
    fn gen_vtable_instance_func_body(
        &mut self,
        vtable_struct_ref: TypeDeclRef,
        trait_impl_def: &hax::FullDef,
    ) -> Result<Body, Error> {
        let mut locals = Vector::new();
        let local_ty = Ty::new(TyKind::Adt(vtable_struct_ref.clone()));
        let ret_local = locals.push_with(|idx| Local {
            index: idx,
            name: Some("ret".into()),
            ty: local_ty.clone(),
        });
        // there are mainly two parts of statements:
        // the prepration of fields initialisation of ret
        // the assignment of ret
        let mut statements = Vec::new();

        let hax::FullDefKind::TraitImpl {
            trait_pred,
            implied_impl_exprs,
            items,
            ..
        } = trait_impl_def.kind()
        else {
            unreachable!()
        };

        self.add_parent_ptr_to_vtable_instance_func_body(
            trait_pred,
            implied_impl_exprs,
            &mut locals,
            &mut statements,
        )?;

        let impl_span = self.def_span(&trait_impl_def.def_id());
        let implemented_tref = self.translate_trait_ref(impl_span, &trait_pred.trait_ref)?;
        trace!(
            "For vtable instance, implemented trait: {}",
            implemented_tref.with_ctx(&self.into_fmt())
        );
        self.add_vtable_methods_to_vtable_instance_func_body(
            &implemented_tref,
            items,
            &mut locals,
            &mut statements,
        )?;

        // assignment to ret
        let assn: llbc_ast::Statement = {
            let operands = locals
                .iter()
                .filter_map(|local| {
                    // the return should not be mapped
                    if local.index.is_zero() {
                        None
                    } else {
                        Some(Operand::Move(Place {
                            kind: PlaceKind::Local(local.index),
                            ty: local_ty.clone(),
                        }))
                    }
                })
                .collect();
            llbc_ast::Statement::new(
                Span::dummy(),
                llbc_ast::RawStatement::Assign(
                    Place {
                        kind: PlaceKind::Local(ret_local),
                        ty: local_ty.clone(),
                    },
                    Rvalue::Aggregate(
                        AggregateKind::Adt(vtable_struct_ref.clone(), None, None),
                        operands,
                    ),
                ),
            )
        };
        statements.push(assn);
        statements.push(llbc_ast::Statement::new(
            Span::dummy(),
            llbc_ast::RawStatement::Return,
        ));

        let body = Block {
            span: Span::dummy(),
            statements,
        };

        // Generate the body of the vtable instance function.
        Ok(Body::Structured(GExprBody {
            span: Span::dummy(),
            locals: Locals {
                arg_count: 0,
                locals: locals,
            },
            comments: Vec::new(),
            body: body,
        }))
    }

    // pub(crate) fn translate_vtable_instance_body(
    //     mut self,
    //     init_func_id: FunDeclId,
    //     item_meta: ItemMeta,
    //     // This can be either a trait impl or a closure definition.
    //     def: &hax::FullDef,
    //     maybe_target_kind: Option<ClosureKind>,
    // ) -> Result<FunDecl, Error> {
    //     // prepare the generic environment
    //     self.translate_def_generics(item_meta.span, def)?;

    //     let def_span = self.def_span(def.def_id());

    //     let (vtable_struct_ref, trait_decl_ref) =
    //         self.get_vtable_instance_info(def_span, def, maybe_target_kind)?;
    //     let glob_def_id = self.register_vtable_instance_as_global_decl_id(
    //         item_meta.span,
    //         &def.def_id,
    //         maybe_target_kind,
    //     );

    //     // signature: `() -> VTable`
    //     let sig = FunSig {
    //         is_unsafe: true,
    //         generics: self.the_only_binder().params.clone(),
    //         inputs: vec![Ty::mk_unit()],
    //         output: Ty::new(TyKind::Adt(vtable_struct_ref.clone())),
    //     };

    //     let body = match def.kind() {
    //         hax::FullDefKind::TraitImpl { .. } => {
    //             let body = self.gen_vtable_instance_func_body(vtable_struct_ref, def)?;
    //             Ok(body)
    //         }
    //         hax::FullDefKind::Closure { .. } => {
    //             todo!("Handle closure vtable instance translation");
    //         }
    //         _ => {
    //             panic!("Unexpected trait impl definition kind: {:?}", def.kind());
    //         }
    //     };

    //     Ok(FunDecl {
    //         def_id: init_func_id,
    //         item_meta: item_meta,
    //         signature: sig,
    //         kind: ItemKind::VTable { trait_decl_ref },
    //         is_global_initializer: Some(glob_def_id),
    //         body,
    //     })
    // }

    pub(crate) fn translate_vtable_shim(
        mut self,
        fun_id: FunDeclId,
        item_meta: ItemMeta,
        impl_func_def: &hax::FullDef,
    ) -> Result<FunDecl, Error> {
        Err(Error {
            span: item_meta.span,
            msg: String::from("TODO"),
        })
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

//// Generate the vtable struct.
impl ItemTransCtx<'_, '_> {
    /// Query whether a trait is dyn compatible.
    /// TODO(dyn): for now we return `false` if the trait has any associated types, as we don't
    /// handle associated types in vtables.
    pub fn trait_is_dyn_compatible(&mut self, def_id: &hax::DefId) -> Result<bool, Error> {
        let def = self.poly_hax_def(def_id)?;
        Ok(match def.kind() {
            hax::FullDefKind::Trait {
                dyn_self: Some(dyn_self),
                ..
            }
            | hax::FullDefKind::TraitAlias {
                dyn_self: Some(dyn_self),
                ..
            } => {
                match dyn_self.kind() {
                    // `dyn_self` looks like `dyn Trait<Args.., Ty0 = .., Ty1 = ..>`. The first
                    // predicate is `_: Trait<Args..>`, the rest are type constraints. Hence the
                    // trait recursively has no assoc types iff `preds.len() == 1`.
                    hax::TyKind::Dynamic(_, preds, _) => preds.predicates.len() == 1,
                    _ => panic!("unexpected `dyn_self`: {dyn_self:?}"),
                }
            }
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
            vtable_safe: true,
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

    /// Construct the type of the vtable for this trait.
    ///
    /// It's a struct that has for generics the generics of the trait + one parameter for each
    /// associated type of the trait and its parents.
    /// TODO(dyn): add the associated types.
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

        self.translate_def_generics(span, trait_def)?;
        // TODO(dyn): add the associated types.

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
        let mut dyn_self = self.translate_ty(span, dyn_self)?;
        // First construct fields that use the real method signatures (which may use the `Self`
        // type). We fixup the types and generics below.
        let fields = self.gen_vtable_struct_fields(span, trait_def, implied_predicates)?;
        let mut kind = TypeDeclKind::Struct(fields);
        let layout = self.generate_naive_layout(span, &kind)?;

        // Replace any use of `Self` with `dyn Trait<...>`, and remove the `Self` type variable
        // from the generic parameters.
        let mut generics = self.into_generics();
        {
            dyn_self = dynify(dyn_self, None);
            generics = dynify(generics, Some(dyn_self.clone()));
            kind = dynify(kind, Some(dyn_self.clone()));
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
    /// global <T..., VT...>
    ///     trait::{vtable_instance}::<ImplTy<T...>> :
    ///         trait::{vtable}<VT...> = trait::{vtable}<VT...> {
    ///     drop: &ignore / &<ImplTy<T...> as Drop>::drop,
    ///     size: size_of(<ImplTy<T...>>),
    ///     align: align_of(<ImplTy<T...>>),
    ///     method_0: &<ImplTy<T...> as Trait>::method_0::{shim},
    ///     method_1: &<ImplTy<T...> as Trait>::method_1::{shim},
    ///     ...
    ///     super_trait_0: &SuperTrait0<VT...>::{vtable_instance}::<ImplTy<T...>>,
    ///     super_trait_1: &SuperTrait1<VT...>::{vtable_instance}::<ImplTy<T...>>,
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
        mut mk_field: impl FnMut(RawConstantExpr),
    ) -> Result<(), Error> {
        // Exit if the item isn't a vtable safe method.
        match self.poly_hax_def(&item.decl_def_id)?.kind() {
            hax::FullDefKind::AssocFn {
                vtable_safe: true, ..
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
                let shim_ref =
                    self.translate_item(span, &item_ref, TransItemSourceKind::VTableMethod)?;
                RawConstantExpr::FnPtr(shim_ref)
            }
            hax::ImplAssocItemValue::DefaultedFn { .. } => RawConstantExpr::Opaque(
                "shim for provided methods \
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
        mut mk_field: impl FnMut(RawConstantExpr),
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
            if let hax::ClauseKind::Trait(pred) = clause.kind.hax_skip_binder_ref() {
                // If a clause looks like `Self: OtherTrait<...>`, we consider it a supertrait.
                if !self.pred_is_for_self(&pred.trait_ref) {
                    continue;
                }
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
                        value: RawConstantExpr::Global(vtable_instance_ref),
                        ty: fn_ptr_ty,
                    });
                    RawConstantExpr::Ref(global)
                }
                // TODO(dyn): builtin impls
                _ => RawConstantExpr::Opaque("missing supertrait vtable".into()),
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
            let ty = field_ty_iter.next().unwrap();
            aggregate_fields.push(Operand::Const(Box::new(ConstantExpr { value: kind, ty })));
        };

        // TODO(dyn): provide values
        mk_field(RawConstantExpr::Opaque("unknown size".to_string()));
        mk_field(RawConstantExpr::Opaque("unknown align".to_string()));
        mk_field(RawConstantExpr::Opaque("unknown drop".to_string()));

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
            RawStatement::Assign(
                ret_place,
                Rvalue::Aggregate(
                    AggregateKind::Adt(vtable_struct_ref.clone(), None, None),
                    aggregate_fields,
                ),
            ),
        ));

        let block = BlockData {
            statements,
            terminator: Terminator::new(span, RawTerminator::Return),
        };

        Ok(Body::Unstructured(GExprBody {
            span,
            locals,
            comments: Vec::new(),
            body: [block].into(),
        }))
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

    // pub(crate) fn translate_vtable_shim(
    //     self,
    //     _fun_id: FunDeclId,
    //     item_meta: ItemMeta,
    //     _impl_func_def: &hax::FullDef,
    // ) -> Result<FunDecl, Error> {
    //     let span = item_meta.span;
    //     raise_error!(self, span, "unimplemented")
    // }
}
