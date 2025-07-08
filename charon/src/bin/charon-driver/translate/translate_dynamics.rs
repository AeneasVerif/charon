use std::mem;

use crate::translate::translate_bodies::BodyTransCtx;

use super::translate_ctx::*;
use charon_lib::ast::*;
use charon_lib::ids::Vector;
use charon_lib::ullbc_ast::*;
use hax_frontend_exporter as hax;
use itertools::Itertools;
use tracing::field;

/// Type: `()`
fn unit_ty() -> Ty {
    Ty::new(TyKind::Adt(TypeDeclRef {
        id: TypeId::Tuple,
        generics: Box::new(GenericArgs::empty()),
    }))
}

/// Type: `*[mut] ()`
fn unit_raw_ptr(is_mut: bool) -> Ty {
    Ty::new(TyKind::RawPtr(
        unit_ty(),
        if is_mut {
            RefKind::Mut
        } else {
            RefKind::Shared
        },
    ))
}

fn dummy_public_attr_info() -> AttrInfo {
    AttrInfo {
        attributes: Vec::new(),
        inline: None,
        rename: None,
        public: true,
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
            skip_binder: (Vec::from([unit_raw_ptr(true)]), unit_ty()),
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
        let trait_decl_ref =
            self.translate_trait_decl_ref_from_ex_trait_ref(span, &tref.def_id, &tref.args)?;
        let id = self.register_type_decl_id(span, &tref.def_id);
        Ok(ExistentialTraitRef {
            trait_ref: trait_decl_ref,
            vtable_typ_id: id,
        })
    }

    fn translate_trait_decl_ref_from_ex_trait_ref(
        &mut self,
        span: Span,
        def_id: &hax::DefId,
        args: &[hax::GenericArg],
    ) -> Result<TraitDeclRef, Error> {
        Ok(TraitDeclRef {
            id: self.register_trait_decl_id(span, def_id),
            generics: Box::new(self.translate_generic_args(span, args, &[])?),
        })
    }

    pub(crate) fn translate_existential_predicate_projection(
        &mut self,
        span: Span,
        proj: &hax::ExistentialProjection,
    ) -> Result<ExistentialProjection, Error> {
        let trait_decl_ref =
            self.translate_trait_decl_ref_from_ex_trait_ref(span, &proj.def_id, &proj.args)?;
        // self.translate_trait_decl_ref(span, item);
        let term = match &proj.term {
            hax_frontend_exporter::Term::Ty(ty) => TyTerm::Ty(self.translate_ty(span, ty)?),
            hax_frontend_exporter::Term::Const(decorated) => {
                TyTerm::Const(self.translate_constant_expr_to_constant_expr(span, decorated)?)
            }
        };
        Ok(ExistentialProjection {
            trait_ref: trait_decl_ref,
            term: term,
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

    /// Returns the list of methods in the vtable for the given trait.
    /// Just the methods! Ignoring `Vacant` and `TraitVPtr`.
    /// Also, the types of the methods are already for the Shim functions,
    /// i.e. the receiver of the functions are turned to the corresponding erased version:
    /// - `&self` becomes `*()`
    /// - `&mut self` becomes `*mut ()`
    /// - `self : Box<Self>` becomes `Box<()>`
    /// - `self : Arc<Self>` becomes `Arc<()>`
    /// - `self : Rc<Self>` becomes `Rc<()>`
    /// - `self : Pin<P>` becomes `Pin<P'>` where `P'` is recursively translated for the erased type.
    fn lookup_vtable_method_list(&self, trait_def_id: &hax::DefId) -> Vec<(String, Ty)> {
        todo!()
    }

    pub(crate) fn translate_vtable_struct(
        mut self,
        typ_id: TypeDeclId,
        item_meta: ItemMeta,
        trait_def_id: &hax::DefId,
        trait_full_def: &hax::FullDef,
    ) -> Result<TypeDecl, Error> {
        let trait_id = self.register_trait_decl_id(Span::dummy(), trait_def_id);
        // the list of the form [(name, type)]
        let method_list = self.lookup_vtable_method_list(trait_def_id);
        // the true layout of the vtable:
        // [ drop_func : *mut () -> (),
        //   self_ty_size : usize,
        //   self_ty_align : usize,
        //   ...  -- the method list ]
        // We IGNORE the vacant placeholder & upcast-ptr here!
        let ptr_size = IntegerTy::size(&IntegerTy::Isize);
        let ptr_align = ptr_size;
        let layout = Layout {
            size: Some(((3 + method_list.len()) * ptr_size) as u64),
            align: Some(ptr_align as u64),
            discriminant_layout: None,
            uninhabited: false,
            variant_layouts: Vector::new(),
        };
        let mut fields = common_vtable_entries();
        for (method_name, method_ty) in method_list {
            let field = Field {
                span: Span::dummy(),
                attr_info: dummy_public_attr_info(),
                name: Some(method_name),
                ty: method_ty,
            };
            fields.push(field);
        }
        Ok(TypeDecl {
            def_id: typ_id,
            item_meta: item_meta,
            generics: self.into_generics(),
            src: ItemKind::VTable { trait_id: trait_id },
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
        tref: &hax::TraitRef,
    ) -> Result<GlobalDecl, Error> {
        todo!()
    }

    pub(crate) fn translate_vtable_instance_body(
        mut self,
        init_func_id: FunDeclId,
        item_meta: ItemMeta,
        tref: &hax::TraitRef,
    ) -> Result<FunDecl, Error> {
        todo!()
    }
}
