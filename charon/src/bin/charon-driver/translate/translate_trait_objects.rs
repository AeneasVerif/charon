use std::mem;
use std::ops::ControlFlow::Continue;

use crate::translate::translate_bodies::BodyTransCtx;
use crate::translate::translate_types;

use crate::translate::{translate_generics::BindingLevel, translate_predicates::PredicateLocation};

use super::translate_ctx::*;
use charon_lib::ast::*;
use hax_frontend_exporter as hax;

use super::translate_ctx::*;
use charon_lib::ast::*;
use charon_lib::formatter::IntoFormatter;
use charon_lib::ids::Vector;
use charon_lib::pretty::FmtWithCtx;
use charon_lib::ullbc_ast::*;
use hax_frontend_exporter as hax;
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

impl ItemTransCtx<'_, '_> {
    pub(crate) fn translate_existential_predicate_trait(
        &mut self,
        span: Span,
        tref: &hax::ExistentialTraitRef,
    ) -> Result<ExistentialTraitRef, Error> {
        // Here, we need to trigger the enqueue of the vtable struct
        let _ = self.register_vtable_as_type_decl_id(span, &tref.def_id);
        Ok(ExistentialTraitRef(
            self.translate_trait_decl_ref_from_ex_trait_ref(span, &tref.def_id, &tref.args)?,
        ))
    }

    fn translate_ex_generics(
        &mut self,
        span: Span,
        args: &[hax::GenericArg],
    ) -> Result<Box<GenericArgs>, Error> {
        let mut generics = Box::new(self.translate_generic_args(span, args, &[])?);
        generics.types.insert_and_shift_ids(
            TypeVarId::from_usize(0),
            Ty::new(TyKind::ExistentialPlaceholder),
        );
        Ok(generics)
    }

    /// An existential trait reference is represented separately as an `DefId`` with its args
    fn translate_trait_decl_ref_from_ex_trait_ref(
        &mut self,
        span: Span,
        def_id: &hax::DefId,
        args: &[hax::GenericArg],
    ) -> Result<TraitDeclRef, Error> {
        Ok(TraitDeclRef {
            id: self.register_trait_decl_id(span, def_id),
            generics: self.translate_ex_generics(span, args)?,
        })
    }

    pub(crate) fn translate_existential_predicate_projection(
        &mut self,
        span: Span,
        proj: &hax::ExistentialProjection,
    ) -> Result<ExistentialProjection, Error> {
        let args = self.translate_ex_generics(span, &proj.args)?;
        let name = self.t_ctx.translate_trait_item_name(&proj.def_id)?;
        let term = match &proj.term {
            hax_frontend_exporter::Term::Ty(ty) => TyTerm::Ty(self.translate_ty(span, ty)?),
            hax_frontend_exporter::Term::Const(decorated) => {
                TyTerm::Const(self.translate_constant_expr_to_constant_expr(span, decorated)?)
            }
        };
        Ok(ExistentialProjection {
            trait_item: name,
            generics: args,
            term,
        })
    }

    /// Simply gets the trait decl id for the DefId of the auto trait.
    pub(crate) fn translate_existential_predicate_auto_trait(
        &mut self,
        span: Span,
        def_id: &hax::DefId,
    ) -> Result<TraitDeclId, Error> {
        Ok(self.register_trait_decl_id(span, def_id))
    }

    pub(crate) fn translate_existential_predicate(
        &mut self,
        span: Span,
        pred: &hax::ExistentialPredicate,
    ) -> Result<ExistentialPredicate, Error> {
        Ok(match pred {
            hax::ExistentialPredicate::Trait(tref) => {
                ExistentialPredicate::Trait(self.translate_existential_predicate_trait(span, tref)?)
            }
            hax::ExistentialPredicate::Projection(proj) => ExistentialPredicate::Projection(
                self.translate_existential_predicate_projection(span, proj)?,
            ),
            hax::ExistentialPredicate::AutoTrait(def_id) => ExistentialPredicate::AutoTrait(
                self.translate_existential_predicate_auto_trait(span, def_id)?,
            ),
        })
    }

    // /// Returns the list of methods in the vtable for the given trait.
    // /// Just the methods! Ignoring `Vacant` and `TraitVPtr`.
    // /// Also, the types of the methods are already for the Shim functions,
    // /// i.e. the receiver of the functions are turned to the corresponding erased version:
    // /// - `&self` becomes `*()`
    // /// - `&mut self` becomes `*mut ()`
    // /// - `self : Box<Self>` becomes `Box<()>`
    // /// - `self : Arc<Self>` becomes `Arc<()>`
    // /// - `self : Rc<Self>` becomes `Rc<()>`
    // /// - `self : Pin<P>` becomes `Pin<P'>` where `P'` is recursively translated for the erased type.
    // /// See, e.g.,
    // ///     https://doc.rust-lang.org/reference/items/traits.html#dyn-compatibility
    // /// for more details
    // fn lookup_vtable_method_list(&self, trait_def_id: &hax::DefId) -> Vec<(String, Ty)> {
    //     // perform a DFS ourselves to find the methods in the vtable
    //     // as we only have the `hax::DefId` of the trait, but no `TraitRef` to call Rustc
    //     let mut vec = Vec::new();
    //     let call_back = |trait_ref: &rustc_middle::ty::TraitRef| {
    //         vec.append(&mut self.lookup_vtable_methods_of_one_trait_segment(trait_ref));
    //     };
    //     self.prepare_trait_segments(trait_def_id, call_back);
    //     vec
    // }

    // /// Call `rustc_trait_selection::traits::vtable::prepare_vtable_segments`
    // /// to get the correct order of the trait segments
    // /// The `TraitRef` to be supplied to the `call_back` is from the dummy object
    // /// the generic args might need to be substituted by the bounded generics
    // fn prepare_trait_segments(
    //     &self,
    //     trait_def_id: &hax::DefId,
    //     mut call_back: impl FnMut(&rustc_middle::ty::TraitRef),
    // ) {
    //     let tcx = self.t_ctx.tcx;
    //     let rid = trait_def_id.as_rust_def_id().unwrap();
    //     let dummy = rustc_middle::ty::TraitRef::identity(tcx, rid);
    //     use rustc_trait_selection::traits::vtable::*;
    //     prepare_vtable_segments(tcx, dummy, |segment| -> std::ops::ControlFlow<()> {
    //         match segment {
    //             VtblSegment::MetadataDSA => Continue(()),
    //             VtblSegment::TraitOwnEntries { trait_ref, .. } => {
    //                 call_back(&trait_ref);
    //                 Continue(())
    //             }
    //         }
    //     });
    // }

    fn add_parent_trait_vtable_ptrs(
        &mut self,
        fields: &mut Vector<FieldId, Field>,
        parent_clauses: &Vector<TraitClauseId, (hax::TraitPredicate, TraitClause)>,
    ) -> Result<(), Error> {
        for (idx, (pred, clause)) in parent_clauses.iter_indexed_values() {
            let trait_ref = &clause.trait_.skip_binder;
            let generics = trait_ref.generics.clone();
            let def_id = &pred.trait_ref.def_id;
            let id = self.translate_type_id(Span::dummy(), def_id)?;
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

    /// Get the shim type for the given method.
    /// The shim type is the type of the function that is used in the vtable.
    /// FIXME: add required parameters and implement
    fn get_shim_ty(&self) -> Result<Ty, Error> {
        // the shim type is always a raw pointer to unit
        todo!()
    }

    fn add_vtable_methods_from_trait_items(
        &mut self,
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
        for (item_name, _, hax_def) in &items {
            match &hax_def.kind {
                hax::FullDefKind::AssocFn { sig, .. } => {
                    let shim_ty = self.get_shim_ty()?;
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


    pub(crate) fn translate_vtale_struct(
        mut self,
        typ_id: TypeDeclId,
        item_meta: ItemMeta,
        trait_full_def: &hax::FullDef,
    ) -> Result<TypeDecl, Error> {
        // start by getting the generic environment ready
        self.translate_def_generics(Span::dummy(), trait_full_def)?;
        let mut fields = common_vtable_entries();
        // translate the super pointers
        let parent_clauses = mem::take(&mut self.parent_trait_clauses);
        self.add_parent_trait_vtable_ptrs(&mut fields, &parent_clauses)?;
        // if it is a trait definition, we need to add the methods
        if let hax::FullDefKind::Trait { items, .. } = &trait_full_def.kind() {
            self.add_vtable_methods_from_trait_items(&mut fields, items)?;
        }
        // else, it should be a trait alias, which should not have any methods in its vtable

        // take out the required stuff before consuming `self`
        let ptr_size = self.t_ctx.translated.target_information.target_pointer_size;
        let trait_id = self.register_trait_decl_id(Span::dummy(), &trait_full_def.def_id);
        let generics = self.into_generics();
        // the true layout of the vtable:
        // [ drop_func : *mut () -> (),
        //   self_ty_size : usize,
        //   self_ty_align : usize,
        //   ...  -- the super trait vtables
        //   ...  -- the method list ]
        // We IGNORE the vacant placeholder & upcast-ptr here!
        let ptr_align = ptr_size;
        let layout = Layout {
            // everything is of the same size as a pointer
            size: Some((fields.iter().count() as u64) * ptr_size),
            align: Some(ptr_align as u64),
            discriminant_layout: None,
            uninhabited: false,
            variant_layouts: Vector::new(),
        };
        // for (method_name, method_ty) in method_list {
        //     let field = Field {
        //         span: Span::dummy(),
        //         attr_info: dummy_public_attr_info(),
        //         name: Some(method_name),
        //         ty: method_ty,
        //     };
        //     fields.push(field);
        // }
        // let generics = self.into_generics();
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
        todo!()
    }

    pub(crate) fn translate_vtable_instance_body(
        mut self,
        init_func_id: FunDeclId,
        item_meta: ItemMeta,
        def: &hax::FullDef,
    ) -> Result<FunDecl, Error> {
        todo!()

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
