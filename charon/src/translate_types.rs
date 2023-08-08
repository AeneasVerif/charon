use crate::assumed;
use crate::common::*;
use crate::generics;
use crate::names::type_def_id_to_name;
use crate::regions_hierarchy::RegionGroups;
use crate::translate_ctx::*;
use crate::types as ty;
use crate::types::ConstGeneric;
use core::convert::*;
use rustc_hir::def_id::DefId;
use rustc_middle::mir::Mutability;
use rustc_middle::ty::{Ty, TyKind};

pub fn translate_region_name(region: &rustc_middle::ty::RegionKind<'_>) -> Option<String> {
    // Compute the region name
    let s = match region {
        rustc_middle::ty::RegionKind::ReEarlyBound(r) => Some(r.name.to_ident_string()),
        rustc_middle::ty::RegionKind::ReLateBound(_, br) => match br.kind {
            rustc_middle::ty::BoundRegionKind::BrAnon(_, _) => None,
            rustc_middle::ty::BoundRegionKind::BrNamed(_, symbol) => Some(symbol.to_ident_string()),
            rustc_middle::ty::BoundRegionKind::BrEnv => Some("@env".to_owned()),
        },
        rustc_middle::ty::RegionKind::ReFree(r) => match r.bound_region {
            rustc_middle::ty::BoundRegionKind::BrAnon(_, _) => None,
            rustc_middle::ty::BoundRegionKind::BrNamed(_, symbol) => Some(symbol.to_ident_string()),
            rustc_middle::ty::BoundRegionKind::BrEnv => Some("@env".to_owned()),
        },
        _ => {
            unreachable!();
        }
    };

    // We ignore the name when it is equal to "'_"
    if s.is_some() && s.as_ref().unwrap() == "'_" {
        None
    } else {
        s
    }
}

pub fn translate_non_erased_region<'tcx>(
    region_params: &im::OrdMap<rustc_middle::ty::RegionKind<'tcx>, ty::RegionVarId::Id>,
    region: rustc_middle::ty::RegionKind<'tcx>,
) -> ty::Region<ty::RegionVarId::Id> {
    match region {
        rustc_middle::ty::RegionKind::ReErased => unreachable!(),
        rustc_middle::ty::RegionKind::ReStatic => ty::Region::Static,
        _ => {
            let rid = region_params.get(&region).unwrap();
            ty::Region::Var(*rid)
        }
    }
}

/// Translate a region which is expected to be erased.
///
/// The regions are expected to be erased inside the function bodies (i.e.:
/// we believe MIR uses regions only in the function signatures).
pub fn translate_erased_region(region: rustc_middle::ty::RegionKind<'_>) -> ty::ErasedRegion {
    match region {
        rustc_middle::ty::RegionKind::ReErased => ty::ErasedRegion::Erased,
        _ => {
            unreachable!();
        }
    }
}

impl<'tcx, 'ctx, 'ctx1> BodyTransCtx<'tcx, 'ctx, 'ctx1> {
    /// Translate a Ty.
    ///
    /// Typically used in this module to translate the fields of a structure/
    /// enumeration definition, or later to translate the type of a variable.
    ///
    /// Note that we take as parameter a function to translate regions, because
    /// regions can be translated in several manners (non-erased region or erased
    /// regions), in which case the return type is different.
    pub(crate) fn translate_ty<R>(
        &mut self,
        region_translator: &dyn Fn(&rustc_middle::ty::RegionKind<'tcx>) -> R,
        ty: &Ty<'tcx>,
    ) -> Result<ty::Ty<R>>
    where
        R: Clone + Eq,
    {
        self.translate_ty_kind(region_translator, ty.kind())
    }

    /// Translate a [TyKind].
    ///
    /// See the comments for [translate_ty] (the two functions do the same thing,
    /// they simply don't take the same input parameters).
    pub(crate) fn translate_ty_kind<R>(
        &mut self,
        region_translator: &dyn Fn(&rustc_middle::ty::RegionKind<'tcx>) -> R,
        ty_kind: &TyKind<'tcx>,
    ) -> Result<ty::Ty<R>>
    where
        R: Clone + Eq,
    {
        trace!("{:?}", ty_kind);
        match ty_kind {
            TyKind::Bool => Ok(ty::Ty::Literal(ty::LiteralTy::Bool)),
            TyKind::Char => Ok(ty::Ty::Literal(ty::LiteralTy::Char)),
            TyKind::Int(int_ty) => Ok(ty::Ty::Literal(ty::LiteralTy::Integer(
                ty::IntegerTy::rust_int_ty_to_integer_ty(*int_ty),
            ))),
            TyKind::Uint(int_ty) => Ok(ty::Ty::Literal(ty::LiteralTy::Integer(
                ty::IntegerTy::rust_uint_ty_to_integer_ty(*int_ty),
            ))),
            TyKind::Float(_) => {
                trace!("Float");
                // This case should have been filtered during the registration phase
                unreachable!();
            }
            TyKind::Never => Ok(ty::Ty::Never),

            TyKind::Alias(_, _) => {
                unimplemented!();
            }

            TyKind::Adt(adt, substs) => {
                let adt_did = adt.did();
                trace!("Adt: {:?}", adt_did);

                // Retrieve the list of used arguments
                let used_params = if adt_did.is_local() {
                    Option::None
                } else {
                    let name = type_def_id_to_name(self.t_ctx.tcx, adt_did);
                    assumed::type_to_used_params(&name)
                };

                // Translate the type parameters instantiation
                let (regions, params, cgs) =
                    self.translate_substs(region_translator, used_params, substs)?;

                // Retrieve the ADT identifier
                let def_id = self.translate_type_id(adt_did);

                // Return the instantiated ADT
                Ok(ty::Ty::Adt(def_id, regions, params, cgs))
            }
            TyKind::Str => {
                trace!("Str");

                let id = ty::TypeId::Assumed(ty::AssumedTy::Str);
                Ok(ty::Ty::Adt(id, Vec::new(), Vec::new(), Vec::new()))
            }
            TyKind::Array(ty, const_param) => {
                trace!("Array");

                let c = self.translate_const_kind_as_const_generic(*const_param);
                let tys = vec![self.translate_ty(region_translator, ty)?];
                let cgs = vec![c];
                let id = ty::TypeId::Assumed(ty::AssumedTy::Array);
                Ok(ty::Ty::Adt(id, Vec::new(), tys, cgs))
            }
            TyKind::Slice(ty) => {
                trace!("Slice");

                let tys = vec![self.translate_ty(region_translator, ty)?];
                let id = ty::TypeId::Assumed(ty::AssumedTy::Slice);
                Ok(ty::Ty::Adt(id, Vec::new(), tys, Vec::new()))
            }
            TyKind::Ref(region, ty, mutability) => {
                trace!("Ref");

                let region = region_translator(region);
                let ty = self.translate_ty(region_translator, ty)?;
                let kind = match *mutability {
                    Mutability::Not => ty::RefKind::Shared,
                    Mutability::Mut => ty::RefKind::Mut,
                };
                Ok(ty::Ty::Ref(region, Box::new(ty), kind))
            }
            TyKind::RawPtr(ty_and_mut) => {
                trace!("RawPtr: {:?}", ty_and_mut);
                let ty = self.translate_ty(region_translator, &ty_and_mut.ty)?;
                let kind = match ty_and_mut.mutbl {
                    Mutability::Not => ty::RefKind::Shared,
                    Mutability::Mut => ty::RefKind::Mut,
                };
                Ok(ty::Ty::RawPtr(Box::new(ty), kind))
            }
            TyKind::Tuple(substs) => {
                trace!("Tuple");

                let mut params = vec![];
                for param in substs.iter() {
                    let param_ty = self.translate_ty(region_translator, &param)?;
                    params.push(param_ty);
                }

                Ok(ty::Ty::Adt(
                    ty::TypeId::Tuple,
                    Vec::new(),
                    params,
                    Vec::new(),
                ))
            }

            TyKind::FnPtr(_) => {
                trace!("FnPtr");
                unimplemented!();
            }
            TyKind::Param(param) => {
                // A type parameter, for example `T` in `fn f<T>(x : T) {}`.
                // Note that this type parameter may actually have been
                // instantiated (in our environment, we may map it to another
                // type): we just have to look it up.
                // Note that if we are using this function to translate a field
                // type in a type definition, it should actually map to a type
                // parameter.
                trace!("Param");

                // Retrieve the translation of the substituted type:
                let ty = self.type_vars_map.get(&param.index).unwrap();
                let ty = ty::Ty::TypeVar(*ty);

                Ok(ty)
            }

            // Below: those types should be unreachable: if such types are used in
            // the MIR, we should have found them and failed during the registration
            // phase.
            TyKind::Foreign(_) => {
                trace!("Foreign");
                unreachable!();
            }
            TyKind::Infer(_) => {
                trace!("Infer");
                unreachable!();
            }

            TyKind::FnDef(_, _) => {
                trace!("FnDef");
                unreachable!();
            }

            TyKind::Dynamic(_, _, _) => {
                trace!("Dynamic");
                unreachable!();
            }
            TyKind::Closure(_, _) => {
                trace!("Closure");
                unreachable!();
            }

            TyKind::Generator(_, _, _) | TyKind::GeneratorWitness(_) => {
                trace!("Generator");
                unreachable!();
            }

            TyKind::Error(_) => {
                trace!("Error");
                unreachable!();
            }
            TyKind::Bound(_, _) => {
                trace!("Bound");
                unreachable!();
            }
            TyKind::Placeholder(_) => {
                trace!("PlaceHolder");
                unreachable!();
            }
        }
    }

    /// Translate a signature type, where the regions are not erased and use region
    /// variable ids.
    /// Simply calls [`translate_ty`](translate_ty)
    pub(crate) fn translate_sig_ty(&mut self, ty: &Ty<'tcx>) -> Result<ty::RTy> {
        self.translate_ty(
            &|r| translate_non_erased_region(&self.region_vars_map, *r),
            ty,
        )
    }

    /// Translate a type where the regions are erased
    /// Simply calls [translate_ty]
    pub(crate) fn translate_ety(&mut self, ty: &Ty<'tcx>) -> Result<ty::ETy> {
        self.translate_ty(&|r| translate_erased_region(*r), ty)
    }

    fn translate_substs<R>(
        &mut self,
        region_translator: &dyn Fn(&rustc_middle::ty::RegionKind<'tcx>) -> R,
        used_params: Option<Vec<bool>>,
        substs: &rustc_middle::ty::subst::SubstsRef<'tcx>,
    ) -> Result<(Vec<R>, Vec<ty::Ty<R>>, Vec<ConstGeneric>)>
    where
        R: Clone + Eq,
    {
        // Filter the parameters
        let mut param_i = 0;
        let substs: Vec<(rustc_middle::ty::subst::GenericArg<'_>, u32)> = match used_params {
            Option::None => substs
                .iter()
                .map(|p| {
                    let i = param_i;
                    param_i += 1;
                    (p, i)
                })
                .collect(),
            Option::Some(used_params) => substs
                .iter()
                .zip(used_params.into_iter())
                .filter_map(|(param, used)| {
                    let i = param_i;
                    param_i += 1;
                    if used {
                        Some((param, i))
                    } else {
                        None
                    }
                })
                .collect(),
        };

        let mut regions: Vec<R> = vec![];
        let mut params = vec![];
        let cgs = vec![];
        for (param, param_i) in substs.iter() {
            trace!("Adt: param {}: {:?}", param_i, param);
            match param.unpack() {
                rustc_middle::ty::subst::GenericArgKind::Type(param_ty) => {
                    let param_ty = self.translate_ty(region_translator, &param_ty)?;
                    params.push(param_ty);
                }
                rustc_middle::ty::subst::GenericArgKind::Lifetime(region) => {
                    regions.push(region_translator(&region));
                }
                rustc_middle::ty::subst::GenericArgKind::Const(_) => {
                    unimplemented!();
                }
            }
        }

        Result::Ok((regions, params, cgs))
    }

    /// Translate a type def id
    pub(crate) fn translate_type_id(&mut self, def_id: DefId) -> ty::TypeId {
        trace!("{:?}", def_id);

        if def_id.is_local() {
            ty::TypeId::Adt(self.translate_type_decl_id(def_id))
        } else {
            // Non-local: check if the type has primitive support

            // Retrieve the type name
            let name = type_def_id_to_name(self.t_ctx.tcx, def_id);

            match assumed::get_type_id_from_name(&name) {
                Option::Some(id) => {
                    // The type has primitive support
                    ty::TypeId::Assumed(id)
                }
                Option::None => {
                    // The type is external
                    ty::TypeId::Adt(self.translate_type_decl_id(def_id))
                }
            }
        }
    }

    /// Translate one local type definition which has not been flagged as opaque.
    fn translate_transparent_type(
        &mut self,
        trans_id: ty::TypeDeclId::Id,
        substs: &rustc_middle::ty::subst::SubstsRef<'tcx>,
    ) -> ty::TypeDeclKind {
        trace!("{}", trans_id);

        // Retrieve the definition
        trace!("{:?}", self.def_id);
        let adt = self.t_ctx.tcx.adt_def(self.def_id);

        // Explore the variants
        let mut var_id = ty::VariantId::Id::new(0); // Variant index
        let mut variants: Vec<ty::Variant> = vec![];
        for var_def in adt.variants().iter() {
            trace!("variant {}: {:?}", var_id, var_def);

            let mut fields: Vec<ty::Field> = vec![];
            let mut field_id = ty::FieldId::Id::new(0);
            /* This is for sanity: check that either all the fields have names, or
             * none of them has */
            let mut have_names: Option<bool> = Option::None;
            for field_def in var_def.fields.iter() {
                trace!("variant {}: field {}: {:?}", var_id, field_id, field_def);

                let ty = field_def.ty(self.t_ctx.tcx, substs);

                // Translate the field type
                let ty = self.translate_sig_ty(&ty).unwrap();

                // Retrieve the field name.
                // Note that the only way to check if the user wrote the name or
                // if it is just an integer generated by rustc is by checking if
                // if is just made of numerals...
                let field_name = field_def.ident(self.t_ctx.tcx).name.to_ident_string();
                let field_name = {
                    let field_id: std::result::Result<usize, std::num::ParseIntError> =
                        field_name.parse();
                    match field_id {
                        std::result::Result::Ok(_) => None,
                        std::result::Result::Err(_) => Some(field_name),
                    }
                };
                match &have_names {
                    Option::None => {
                        have_names = match &field_name {
                            Option::None => Some(false),
                            Option::Some(_) => Some(true),
                        }
                    }
                    Option::Some(b) => {
                        assert!(*b == field_name.is_some());
                    }
                };

                // Translate the span information
                let meta = self.get_meta_from_rid(field_def.did);

                // Store the field
                let field = ty::Field {
                    meta,
                    name: field_name.clone(),
                    ty,
                };
                fields.push(field);

                field_id.incr();
            }

            let meta = self.get_meta_from_rid(var_def.def_id);
            let variant_name = var_def.ident(self.t_ctx.tcx).name.to_ident_string();
            variants.push(ty::Variant {
                meta,
                name: variant_name,
                fields: ty::FieldId::Vector::from(fields),
            });

            var_id.incr();
        }

        // Register the type
        let type_def_kind: ty::TypeDeclKind = match adt.adt_kind() {
            rustc_middle::ty::AdtKind::Struct => {
                ty::TypeDeclKind::Struct(variants[0].fields.clone())
            }
            rustc_middle::ty::AdtKind::Enum => {
                ty::TypeDeclKind::Enum(ty::VariantId::Vector::from(variants))
            }
            rustc_middle::ty::AdtKind::Union => {
                // Should have been filtered during the registration phase
                unreachable!();
            }
        };

        type_def_kind
    }
}

impl<'tcx, 'ctx> TransCtx<'tcx, 'ctx> {
    /// Auxiliary helper.
    ///
    /// Translate the generics of a type definition.
    /// Returns the translation, together with an instantiated MIR substitution,
    /// which represents the generics on the MIR side (and is useful to translate
    /// the body of the type...).
    ///
    /// Rem.: this seems simpler in [crate::translate_functions_to_ullbc].
    /// TODO: compare and simplify/factorize?
    fn translate_type_generics<'ctx1>(
        &'ctx1 mut self,
        def_id: DefId,
    ) -> (
        BodyTransCtx<'tcx, 'ctx1, 'ctx>,
        rustc_middle::ty::subst::SubstsRef<'tcx>,
    ) {
        // Check the generics
        generics::check_type_generics(self.tcx, def_id);

        // Use a dummy substitution to instantiate the type parameters
        let substs = rustc_middle::ty::subst::InternalSubsts::identity_for_item(self.tcx, def_id);

        // Initialize the body translation context
        let mut bt_ctx = BodyTransCtx::new(def_id, self);

        for p in substs.iter() {
            match p.unpack() {
                rustc_middle::ty::subst::GenericArgKind::Type(param_ty) => {
                    // The type should be a Param:
                    match param_ty.kind() {
                        rustc_middle::ty::TyKind::Param(param_ty) => {
                            let _ = bt_ctx
                                .push_type_var(param_ty.index, param_ty.name.to_ident_string());
                        }
                        _ => {
                            panic!("Inconsistent state");
                        }
                    }
                }
                rustc_middle::ty::subst::GenericArgKind::Lifetime(region) => {
                    let name = translate_region_name(&region);
                    let _ = bt_ctx.push_region(*region, name);
                }
                rustc_middle::ty::subst::GenericArgKind::Const(c) => {
                    // The type should be primitive, meaning it shouldn't contain variables,
                    // non-primitive adts, etc. As a result, we can use an empty context.
                    let ty = bt_ctx.translate_ety(&c.ty()).unwrap();
                    let ty = ty.to_literal();
                    match c.kind() {
                        rustc_middle::ty::ConstKind::Param(cp) => {
                            let _ = bt_ctx.push_const_generic_var(
                                cp.index,
                                ty,
                                cp.name.to_ident_string(),
                            );
                        }
                        _ => unreachable!(),
                    }
                }
            }
        }

        // Sanity check: region names are pairwise distinct (this caused trouble
        // when generating names for the backward functinos in Aeneas): at some
        // point, Rustc introduced names equal to `Some("'_")` for the anonymous
        // regions, instead of using `None` (we now check in [translate_region_name]
        // and ignore names equal to "'_").
        {
            let mut s = std::collections::HashSet::new();
            for r in &bt_ctx.region_vars {
                let name = &r.name;
                if name.is_some() {
                    let name = name.as_ref().unwrap();
                    assert!(s.contains(name));
                    s.insert(name.clone());
                }
            }
        }

        (bt_ctx, substs)
    }

    /// Translate a type definition.
    ///
    /// Note that we translate the types one by one: we don't need to take into
    /// account the fact that some types are mutually recursive at this point
    /// (we will need to take that into account when generating the code in a file).
    pub(crate) fn translate_type(&mut self, id: DefId) {
        let trans_id = self.translate_type_decl_id(id);

        // Check and translate the generics
        // TODO: use the body trans context as input, and don't return anything.
        let (mut bt_ctx, substs) = self.translate_type_generics(id);

        // Check if the type is opaque or external, and delegate the translation
        // of the "body" to the proper function
        let is_transparent = self.id_is_transparent(id);
        let kind = if !id.is_local() || !is_transparent {
            // Opaque types are:
            // - external types
            // - local types flagged as opaque
            ty::TypeDeclKind::Opaque
        } else {
            bt_ctx.translate_transparent_type(trans_id, &substs)
        };

        // Register the type
        let name = type_def_id_to_name(self.tcx, id);
        let region_params = bt_ctx.region_vars.clone();
        let type_params = bt_ctx.type_vars.clone();
        let const_generic_params = bt_ctx.const_generic_vars.clone();

        // Translate the span information
        let meta = bt_ctx.get_meta_from_rid(id);

        let type_def = ty::TypeDecl {
            def_id: trans_id,
            meta,
            name,
            region_params,
            type_params,
            const_generic_params,
            kind,
            regions_hierarchy: RegionGroups::new(),
        };

        trace!("{} -> {}", trans_id.to_string(), type_def.to_string());

        self.type_defs.insert(trans_id, type_def);
    }
}
