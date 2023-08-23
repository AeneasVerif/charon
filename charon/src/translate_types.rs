use crate::assumed;
use crate::common::*;
use crate::names_utils::{def_id_to_name, extended_def_id_to_name};
use crate::regions_hierarchy::RegionGroups;
use crate::translate_ctx::*;
use crate::types as ty;
use crate::types::ConstGeneric;
use core::convert::*;
use hax_frontend_exporter as hax;
use hax_frontend_exporter::SInto;
use rustc_hir::def_id::DefId;

/// Small helper: we ignore region names when they are equal to "'_"
fn check_region_name(s: Option<String>) -> Option<String> {
    if s.is_some() && s.as_ref().unwrap() == "'_" {
        None
    } else {
        s
    }
}

pub fn translate_bound_region_kind_name(kind: &hax::BoundRegionKind) -> Option<String> {
    use hax::BoundRegionKind::*;
    let s = match kind {
        BrAnon(..) => None,
        BrNamed(_, symbol) => Some(symbol.clone()),
        BrEnv => Some("@env".to_owned()),
    };
    check_region_name(s)
}

pub fn translate_region_name(region: &hax::Region) -> Option<String> {
    // Compute the region name
    use hax::{BoundRegionKind::*, RegionKind::*};
    let s = match &region.kind {
        ReEarlyBound(r) => Some(r.name.clone()),
        ReLateBound(_, br) => translate_bound_region_kind_name(&br.kind),
        ReFree(r) => match &r.bound_region {
            BrAnon(..) => None,
            BrNamed(_, symbol) => Some(symbol.clone()),
            BrEnv => Some("@env".to_owned()),
        },
        _ => {
            unreachable!();
        }
    };

    // We check twice in the case of late bound regions, but it is ok...
    check_region_name(s)
}

pub fn translate_non_erased_region(
    region_params: &ty::RegionVarId::MapGenerator<hax::Region>,
    bound_regions: &im::Vector<im::Vector<ty::RegionVarId::Id>>,
    region: &hax::Region,
) -> ty::Region<ty::RegionVarId::Id> {
    match &region.kind {
        hax::RegionKind::ReErased => unreachable!(),
        hax::RegionKind::ReStatic => ty::Region::Static,
        hax::RegionKind::ReLateBound(id, br) => {
            // See the comments in [BodyTransCtx.bound_vars]:
            // - the De Bruijn index identifies the group of variables
            // - the var id identifies the variable inside the group
            let rid = bound_regions.get(*id).unwrap().get(br.var).unwrap();
            ty::Region::Var(*rid)
        }
        _ => {
            // For the other regions, we use the regions map
            let rid = region_params.get(region).unwrap();
            ty::Region::Var(rid)
        }
    }
}

/// Translate a region which is expected to be erased.
///
/// The regions are expected to be erased inside the function bodies (i.e.:
/// we believe MIR uses regions only in the function signatures).
pub fn translate_erased_region(region: &hax::Region) -> ty::ErasedRegion {
    match region.kind {
        hax::RegionKind::ReErased => ty::ErasedRegion::Erased,
        _ => {
            // Actually, not all regions are erased. My understanding is that the early
            // bound regions are erased, but when a region appears in a type it is
            // not. We need to update that.
            unreachable!()
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
        region_translator: &dyn Fn(&hax::Region) -> R,
        ty: &hax::Ty,
    ) -> Result<ty::Ty<R>>
    where
        R: Clone + Eq,
    {
        trace!("{:?}", ty);
        use hax::Ty;
        match ty {
            Ty::Bool => Ok(ty::Ty::Literal(ty::LiteralTy::Bool)),
            Ty::Char => Ok(ty::Ty::Literal(ty::LiteralTy::Char)),
            Ty::Int(int_ty) => Ok(ty::Ty::Literal(ty::LiteralTy::Integer(
                ty::IntegerTy::rust_int_ty_to_integer_ty(*int_ty),
            ))),
            Ty::Uint(int_ty) => Ok(ty::Ty::Literal(ty::LiteralTy::Integer(
                ty::IntegerTy::rust_uint_ty_to_integer_ty(*int_ty),
            ))),
            Ty::Float(_) => {
                trace!("Float");
                unimplemented!();
            }
            Ty::Never => Ok(ty::Ty::Never),

            Ty::Alias(_, _) => {
                unimplemented!();
            }

            Ty::Adt {
                generic_args: substs,
                def_id,
            } => {
                let adt_did = def_id.rust_def_id.unwrap();
                trace!("Adt: {:?}", adt_did);

                // Retrieve the list of used arguments
                let used_params = if adt_did.is_local() {
                    Option::None
                } else {
                    let name = def_id_to_name(self.t_ctx.tcx, def_id);
                    assumed::type_to_used_params(&name)
                };

                // Translate the type parameters instantiation
                let (regions, params, cgs) =
                    self.translate_substs(region_translator, used_params, substs)?;

                // Retrieve the ADT identifier
                let def_id = self.translate_type_id(def_id);

                // Return the instantiated ADT
                Ok(ty::Ty::Adt(def_id, regions, params, cgs))
            }
            Ty::Str => {
                trace!("Str");

                let id = ty::TypeId::Assumed(ty::AssumedTy::Str);
                Ok(ty::Ty::Adt(id, Vec::new(), Vec::new(), Vec::new()))
            }
            Ty::Array(ty, const_param) => {
                trace!("Array");

                let c = self.translate_constant_expr_to_const_generic(const_param);
                let tys = vec![self.translate_ty(region_translator, ty)?];
                let cgs = vec![c];
                let id = ty::TypeId::Assumed(ty::AssumedTy::Array);
                Ok(ty::Ty::Adt(id, Vec::new(), tys, cgs))
            }
            Ty::Slice(ty) => {
                trace!("Slice");

                let tys = vec![self.translate_ty(region_translator, ty)?];
                let id = ty::TypeId::Assumed(ty::AssumedTy::Slice);
                Ok(ty::Ty::Adt(id, Vec::new(), tys, Vec::new()))
            }
            Ty::Ref(region, ty, mutability) => {
                trace!("Ref");

                let region = region_translator(region);
                let ty = self.translate_ty(region_translator, ty)?;
                let kind = if *mutability {
                    ty::RefKind::Mut
                } else {
                    ty::RefKind::Shared
                };
                Ok(ty::Ty::Ref(region, Box::new(ty), kind))
            }
            Ty::RawPtr(ty_and_mut) => {
                trace!("RawPtr: {:?}", ty_and_mut);
                let ty = self.translate_ty(region_translator, &ty_and_mut.ty)?;
                let kind = if ty_and_mut.mutbl {
                    ty::RefKind::Mut
                } else {
                    ty::RefKind::Shared
                };
                Ok(ty::Ty::RawPtr(Box::new(ty), kind))
            }
            Ty::Tuple(substs) => {
                trace!("Tuple");

                let mut params = vec![];
                for param in substs.iter() {
                    let param_ty = self.translate_ty(region_translator, param)?;
                    params.push(param_ty);
                }

                Ok(ty::Ty::Adt(
                    ty::TypeId::Tuple,
                    Vec::new(),
                    params,
                    Vec::new(),
                ))
            }

            Ty::Param(param) => {
                // A type parameter, for example `T` in `fn f<T>(x : T) {}`.
                // Note that this type parameter may actually have been
                // instantiated (in our environment, we may map it to another
                // type): we just have to look it up.
                // Note that if we are using this function to translate a field
                // type in a type definition, it should actually map to a type
                // parameter.
                trace!("Param");

                // Retrieve the translation of the substituted type:
                let var_id = self.type_vars_map.get(&param.index).unwrap();
                let ty = ty::Ty::TypeVar(var_id);

                Ok(ty)
            }

            Ty::Foreign(_) => {
                trace!("Foreign");
                unimplemented!();
            }
            Ty::Infer(_) => {
                trace!("Infer");
                unimplemented!();
            }

            Ty::Dynamic(_, _, _) => {
                trace!("Dynamic");
                unimplemented!();
            }

            Ty::Generator(_, _, _) => {
                trace!("Generator");
                unimplemented!();
            }

            Ty::Bound(_, _) => {
                trace!("Bound");
                unimplemented!();
            }
            Ty::Placeholder(_) => {
                trace!("PlaceHolder");
                unimplemented!();
            }
            Ty::Arrow { .. } => {
                trace!("Arrow");
                unimplemented!();
            }
            Ty::Error => {
                trace!("Error");
                unimplemented!();
            }
            Ty::Todo(s) => {
                trace!("Todo: {s}");
                unimplemented!();
            }
        }
    }

    /// Translate a signature type, where the regions are not erased and use region
    /// variable ids.
    /// Simply calls [`translate_ty`](translate_ty)
    pub(crate) fn translate_sig_ty(&mut self, ty: &hax::Ty) -> Result<ty::RTy> {
        // Borrowing issues: we have to clone some values.
        // This shouldn't cost us too much. In case of performance issues,
        // we can turn the map into an im::map
        let region_vars_map = &self.region_vars_map.clone();
        let bound_vars = &self.bound_vars.clone();
        self.translate_ty(
            &|r| translate_non_erased_region(region_vars_map, bound_vars, r),
            ty,
        )
    }

    /// Translate a type where the regions are erased
    /// Simply calls [translate_ty]
    pub(crate) fn translate_ety(&mut self, ty: &hax::Ty) -> Result<ty::ETy> {
        self.translate_ty(&|r| translate_erased_region(r), ty)
    }

    fn translate_substs<R>(
        &mut self,
        region_translator: &dyn Fn(&hax::Region) -> R,
        used_params: Option<Vec<bool>>,
        substs: &Vec<hax::GenericArg>,
    ) -> Result<(Vec<R>, Vec<ty::Ty<R>>, Vec<ConstGeneric>)>
    where
        R: Clone + Eq,
    {
        // Filter the parameters
        let mut param_i = 0;
        let substs: Vec<(hax::GenericArg, u32)> = match used_params {
            Option::None => substs
                .into_iter()
                .cloned()
                .map(|p| {
                    let i = param_i;
                    param_i += 1;
                    (p, i)
                })
                .collect(),
            Option::Some(used_params) => substs
                .into_iter()
                .cloned()
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
        let mut cgs = vec![];
        for (param, param_i) in substs.iter() {
            trace!("Adt: param {}: {:?}", param_i, param);
            match param {
                hax::GenericArg::Type(param_ty) => {
                    let param_ty = self.translate_ty(region_translator, &param_ty)?;
                    params.push(param_ty);
                }
                hax::GenericArg::Lifetime(region) => {
                    regions.push(region_translator(&region));
                }
                hax::GenericArg::Const(c) => {
                    cgs.push(self.translate_constant_expr_to_const_generic(c));
                }
            }
        }

        Result::Ok((regions, params, cgs))
    }

    /// Translate a type def id
    pub(crate) fn translate_type_id(&mut self, def_id: &hax::DefId) -> ty::TypeId {
        trace!("{:?}", def_id);

        let rust_id = def_id.rust_def_id.unwrap();
        if rust_id.is_local() {
            ty::TypeId::Adt(self.translate_type_decl_id(rust_id))
        } else {
            // Non-local: check if the type has primitive support

            // Retrieve the type name
            let name = def_id_to_name(self.t_ctx.tcx, def_id);

            match assumed::get_type_id_from_name(&name) {
                Option::Some(id) => {
                    // The type has primitive support
                    ty::TypeId::Assumed(id)
                }
                Option::None => {
                    // The type is external
                    ty::TypeId::Adt(self.translate_type_decl_id(rust_id))
                }
            }
        }
    }

    /// Translate one local type definition which has not been flagged as opaque.
    fn translate_transparent_type(
        &mut self,
        trans_id: ty::TypeDeclId::Id,
        adt: hax::AdtDef,
    ) -> ty::TypeDeclKind {
        trace!("{}", trans_id);

        // Explore the variants
        let mut var_id = ty::VariantId::Id::new(0); // Variant index
        let mut variants: Vec<ty::Variant> = vec![];
        for var_def in adt.variants.raw {
            trace!("variant {}: {:?}", var_id, var_def);

            let mut fields: Vec<ty::Field> = vec![];
            let mut field_id = ty::FieldId::Id::new(0);
            /* This is for sanity: check that either all the fields have names, or
             * none of them has */
            let mut have_names: Option<bool> = Option::None;
            for field_def in var_def.fields.into_iter() {
                trace!("variant {}: field {}: {:?}", var_id, field_id, field_def);

                // Translate the field type
                let ty = self.translate_sig_ty(&field_def.ty).unwrap();

                // Retrieve the field name.
                let field_name = field_def.name;
                // Sanity check
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
                let meta = self.translate_meta_from_rspan(field_def.span);

                // Store the field
                let field = ty::Field {
                    meta,
                    name: field_name.clone(),
                    ty,
                };
                fields.push(field);

                field_id.incr();
            }

            let meta = self.translate_meta_from_rspan(var_def.span);
            let variant_name = var_def.name;
            variants.push(ty::Variant {
                meta,
                name: variant_name,
                fields: ty::FieldId::Vector::from(fields),
            });

            var_id.incr();
        }

        // Register the type
        use hax::AdtKind;
        let type_def_kind: ty::TypeDeclKind = match adt.adt_kind {
            AdtKind::Struct => ty::TypeDeclKind::Struct(variants[0].fields.clone()),
            AdtKind::Enum => ty::TypeDeclKind::Enum(ty::VariantId::Vector::from(variants)),
            AdtKind::Union => {
                unimplemented!();
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
    pub(crate) fn translate_generics<'ctx1>(
        &'ctx1 mut self,
        def_id: DefId,
    ) -> (BodyTransCtx<'tcx, 'ctx1, 'ctx>, Vec<hax::GenericArg>) {
        let tcx = self.tcx;

        // Initialize the body translation context
        let mut bt_ctx = BodyTransCtx::new(def_id, self);

        // We could use: TyCtxt::generics_of(DefId)
        // But using the identity substitution is simpler. For instance, we can
        // easily retrieve the type for the const parameters.
        let substs = rustc_middle::ty::subst::InternalSubsts::identity_for_item(tcx, def_id)
            .sinto(&bt_ctx.t_ctx.hax_state);

        for p in &substs {
            use hax::GenericArg::*;
            match p {
                Type(p) => {
                    // The type should be a Param
                    if let hax::Ty::Param(p) = p {
                        let _ = bt_ctx.push_type_var(p.index, p.name.clone());
                    } else {
                        unreachable!("unexpected");
                    }
                }
                Lifetime(region) => {
                    let name = translate_region_name(&region);
                    let _ = bt_ctx.push_region(region.clone(), name);
                }
                Const(c) => {
                    // The type should be primitive, meaning it shouldn't contain variables,
                    // non-primitive adts, etc. As a result, we can use an empty context.
                    let ty = bt_ctx.translate_ety(&c.ty).unwrap();
                    let ty = ty.to_literal();
                    if let hax::ConstantExprKind::ConstRef { id: cp } = &*c.contents {
                        let _ = bt_ctx.push_const_generic_var(cp.index, ty, cp.name.clone());
                    } else {
                        unreachable!();
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
    pub(crate) fn translate_type(&mut self, rust_id: DefId) {
        let trans_id = self.translate_type_decl_id(rust_id);
        let is_transparent = self.id_is_transparent(rust_id);

        // Check and translate the generics
        // TODO: use the body trans context as input, and don't return anything.
        let (mut bt_ctx, _substs) = self.translate_generics(rust_id);

        // Translate the predicates
        bt_ctx.translate_predicates_of(rust_id);

        // Check if the type is opaque or external, and delegate the translation
        // of the "body" to the proper function
        let kind = if !rust_id.is_local() || !is_transparent {
            // Opaque types are:
            // - external types
            // - local types flagged as opaque
            ty::TypeDeclKind::Opaque
        } else {
            let adt = bt_ctx
                .t_ctx
                .tcx
                .adt_def(rust_id)
                .sinto(&bt_ctx.t_ctx.hax_state);
            bt_ctx.translate_transparent_type(trans_id, adt)
        };

        // Register the type
        let name = extended_def_id_to_name(&rust_id.sinto(&bt_ctx.t_ctx.hax_state));
        let region_params = bt_ctx.region_vars.clone();
        let type_params = bt_ctx.type_vars.clone();
        let const_generic_params = bt_ctx.const_generic_vars.clone();

        // Translate the span information
        let meta = bt_ctx.translate_meta_from_rid(rust_id);

        let type_def = ty::TypeDecl {
            def_id: trans_id,
            meta,
            name,
            region_params,
            type_params,
            const_generic_params,
            trait_clauses: bt_ctx.trait_clauses.clone(),
            kind,
            // Dummy value for now: we compute this later
            regions_hierarchy: RegionGroups::new(),
        };

        trace!("{} -> {}", trans_id.to_string(), type_def.to_string());

        self.type_defs.insert(trans_id, type_def);
    }
}
