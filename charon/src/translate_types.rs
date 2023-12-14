use crate::assumed;
use crate::common::*;
use crate::formatter::IntoFormatter;
use crate::gast::*;
use crate::translate_ctx::*;
use crate::types::*;
use core::convert::*;
use hax_frontend_exporter as hax;
use hax_frontend_exporter::SInto;
use rustc_hir::def_id::DefId;

/// Small helper: we ignore some region names (when they are equal to "'_")
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

impl<'tcx, 'ctx, 'ctx1> BodyTransCtx<'tcx, 'ctx, 'ctx1> {
    // Translate a region
    pub(crate) fn translate_region(
        &mut self,
        span: rustc_span::Span,
        erase_regions: bool,
        region: &hax::Region,
    ) -> Result<Region, Error> {
        if erase_regions {
            Ok(Region::Erased)
        } else {
            match &region.kind {
                hax::RegionKind::ReErased => Ok(Region::Erased),
                hax::RegionKind::ReStatic => Ok(Region::Static),
                hax::RegionKind::ReLateBound(id, br) => {
                    // See the comments in [BodyTransCtx.bound_vars]:
                    // - the De Bruijn index identifies the group of variables
                    // - the var id identifies the variable inside the group
                    let rid = self
                        .bound_region_vars
                        .get(*id)
                        .unwrap()
                        .get(br.var)
                        .unwrap();
                    let br_id = DeBruijnId::new(*id);
                    Ok(Region::BVar(br_id, *rid))
                }
                hax::RegionKind::ReVar(re_var) => {
                    // TODO: I'm really not sure how to handle those, here.
                    // They sometimes appear and seem to refer to the early bound
                    // regions. But on the other hand, whenever I investigated, I
                    // only encountered those in *trait references* in trait
                    // implementations.
                    //
                    // For instance, here is a minimal example which triggers
                    // this case:
                    // ```
                    // pub trait From<T> {
                    //     type Error;
                    //   fn from(v: T) -> Result<Self, Self::Error>
                    // //                                ^^^^^^^^^^
                    // //                    This associated type is important
                    //     where
                    //         Self: std::marker::Sized;
                    //
                    // impl From<&bool> for bool {
                    // //        ^^^^^
                    // // This reference is important
                    //     type Error = ();
                    //
                    //     fn from(v: &bool) -> Result<Self, Self::Error> {
                    //         Ok(*v)
                    //     }
                    // }
                    // ```
                    //
                    // If we extract this to LLBC, wet get (focusing on the implementation
                    //  of `from`):
                    // ```
                    // ... // omitted
                    //
                    // fn crate::{bool}::from<@R0, @R1>(@1: &@R1 (bool)) ->
                    //   core::result::Result<bool, crate::{bool}<@R0>::Error> {
                    //   //                                       ^^^
                    //   //                             The problematic region
                    //   ... // omitted
                    // }
                    // ```
                    error_assert!(self, span, self.free_region_vars.get(region).is_none());

                    for (rk, rid) in self.free_region_vars.iter() {
                        if let hax::RegionKind::ReEarlyBound(eb) = &rk.kind {
                            if eb.index == re_var.index {
                                // Note that the DeBruijn index depends
                                // on the current stack of bound region groups.
                                let db_id = self.region_vars.len() - 1;
                                return Ok(Region::BVar(DeBruijnId::new(db_id), *rid));
                            }
                        }
                    }
                    let err = format!(
                        "Could not find region: {:?}\n\nRegion vars map:\n{:?}\n\nBound region vars:\n{:?}",
                        region, self.free_region_vars, self.bound_region_vars
                    );
                    error_or_panic!(self, span, err)
                }
                _ => {
                    // For the other regions, we use the regions map, which
                    // contains the early-bound (free) regions.
                    match self.free_region_vars.get(region) {
                        Some(rid) => {
                            // Note that the DeBruijn index depends
                            // on the current stack of bound region groups.
                            let db_id = self.region_vars.len() - 1;
                            Ok(Region::BVar(DeBruijnId::new(db_id), *rid))
                        }
                        None => {
                            let err = format!(
                                "Could not find region: {:?}\n\nRegion vars map:\n{:?}\n\nBound region vars:\n{:?}",
                                region, self.free_region_vars, self.bound_region_vars
                            );
                            error_or_panic!(self, span, err)
                        }
                    }
                }
            }
        }
    }

    /// Translate a Ty.
    ///
    /// Typically used in this module to translate the fields of a structure/
    /// enumeration definition, or later to translate the type of a variable.
    ///
    /// Note that we take as parameter a function to translate regions, because
    /// regions can be translated in several manners (non-erased region or erased
    /// regions), in which case the return type is different.
    pub(crate) fn translate_ty(
        &mut self,
        span: rustc_span::Span,
        erase_regions: bool,
        ty: &hax::Ty,
    ) -> Result<Ty, Error> {
        trace!("{:?}", ty);
        match ty {
            hax::Ty::Bool => Ok(Ty::Literal(LiteralTy::Bool)),
            hax::Ty::Char => Ok(Ty::Literal(LiteralTy::Char)),
            hax::Ty::Int(int_ty) => Ok(Ty::Literal(LiteralTy::Integer(
                IntegerTy::rust_int_ty_to_integer_ty(*int_ty),
            ))),
            hax::Ty::Uint(int_ty) => Ok(Ty::Literal(LiteralTy::Integer(
                IntegerTy::rust_uint_ty_to_integer_ty(*int_ty),
            ))),
            hax::Ty::Float(_) => {
                trace!("Float");
                error_or_panic!(self, span, "Floats are not supported yet")
            }
            hax::Ty::Never => Ok(Ty::Never),

            hax::Ty::Alias(alias_kind) => match alias_kind {
                hax::AliasKind::Projection {
                    impl_source,
                    substs,
                    name,
                } => {
                    let trait_ref =
                        self.translate_trait_impl_source(span, erase_regions, impl_source)?;
                    // This should succeed because no marker trait (that we may
                    // ignore) has associated types.
                    let trait_ref = trait_ref.unwrap();
                    let (regions, types, const_generics) =
                        self.translate_substs(span, erase_regions, None, substs)?;
                    let generics = GenericArgs {
                        regions,
                        types,
                        const_generics,
                        trait_refs: Vec::new(),
                    };
                    let name = TraitItemName(name.clone());
                    Ok(Ty::TraitType(trait_ref, generics, name))
                }
                _ => {
                    error_or_panic!(self, span, format!("Unimplemented: {:?}", ty))
                }
            },

            hax::Ty::Adt {
                generic_args: substs,
                trait_refs,
                def_id,
            } => {
                let adt_did = def_id.rust_def_id.unwrap();
                trace!("Adt: {:?}", adt_did);

                // Retrieve the list of used arguments
                let used_params = if adt_did.is_local() {
                    Option::None
                } else {
                    let name = self.t_ctx.def_id_to_name(def_id);
                    assumed::type_to_used_params(&name)
                };

                // Translate the type parameters instantiation
                let generics = self.translate_substs_and_trait_refs(
                    span,
                    erase_regions,
                    used_params,
                    substs,
                    trait_refs,
                )?;

                // Retrieve the ADT identifier
                let def_id = self.translate_type_id(span, def_id);

                // Return the instantiated ADT
                Ok(Ty::Adt(def_id, generics))
            }
            hax::Ty::Str => {
                trace!("Str");

                let id = TypeId::Assumed(AssumedTy::Str);
                Ok(Ty::Adt(id, GenericArgs::empty()))
            }
            hax::Ty::Array(ty, const_param) => {
                trace!("Array");

                let c = self.translate_constant_expr_to_const_generic(span, const_param)?;
                let tys = vec![self.translate_ty(span, erase_regions, ty)?];
                let cgs = vec![c];
                let id = TypeId::Assumed(AssumedTy::Array);
                Ok(Ty::Adt(
                    id,
                    GenericArgs::new(Vec::new(), tys, cgs, Vec::new()),
                ))
            }
            hax::Ty::Slice(ty) => {
                trace!("Slice");

                let tys = vec![self.translate_ty(span, erase_regions, ty)?];
                let id = TypeId::Assumed(AssumedTy::Slice);
                Ok(Ty::Adt(id, GenericArgs::new_from_types(tys)))
            }
            hax::Ty::Ref(region, ty, mutability) => {
                trace!("Ref");

                let region = self.translate_region(span, erase_regions, region)?;
                let ty = self.translate_ty(span, erase_regions, ty)?;
                let kind = if *mutability {
                    RefKind::Mut
                } else {
                    RefKind::Shared
                };
                Ok(Ty::Ref(region, Box::new(ty), kind))
            }
            hax::Ty::RawPtr(ty_and_mut) => {
                trace!("RawPtr: {:?}", ty_and_mut);
                let ty = self.translate_ty(span, erase_regions, &ty_and_mut.ty)?;
                let kind = if ty_and_mut.mutbl {
                    RefKind::Mut
                } else {
                    RefKind::Shared
                };
                Ok(Ty::RawPtr(Box::new(ty), kind))
            }
            hax::Ty::Tuple(substs) => {
                trace!("Tuple");

                let mut params = vec![];
                for param in substs.iter() {
                    let param_ty = self.translate_ty(span, erase_regions, param)?;
                    params.push(param_ty);
                }

                Ok(Ty::Adt(TypeId::Tuple, GenericArgs::new_from_types(params)))
            }

            hax::Ty::Param(param) => {
                // A type parameter, for example `T` in `fn f<T>(x : T) {}`.
                // Note that this type parameter may actually have been
                // instantiated (in our environment, we may map it to another
                // type): we just have to look it up.
                // Note that if we are using this function to translate a field
                // type in a type definition, it should actually map to a type
                // parameter.
                trace!("Param");

                // Retrieve the translation of the substituted type:
                match self.type_vars_map.get(&param.index) {
                    None => error_or_panic!(
                        self,
                        span,
                        format!(
                            "Could not find the type variable {:?} (index: {:?})",
                            param.name, param.index
                        )
                    ),
                    Some(var_id) => Ok(Ty::TypeVar(var_id)),
                }
            }

            hax::Ty::Foreign(id) => {
                trace!("Foreign");
                error_or_panic!(
                    self,
                    span,
                    format!(
                        "Unsupported type: foreign type: {:?}",
                        id.rust_def_id.unwrap()
                    )
                )
            }
            hax::Ty::Infer(_) => {
                trace!("Infer");
                error_or_panic!(self, span, "Unsupported type: infer type")
            }

            hax::Ty::Dynamic(_, _, _) => {
                trace!("Dynamic");
                error_or_panic!(self, span, "Dynamic types are not supported yet")
            }

            hax::Ty::Generator(_, _, _) => {
                trace!("Generator");
                error_or_panic!(self, span, "Generator types are not supported yet")
            }

            hax::Ty::Bound(_, _) => {
                trace!("Bound");
                error_or_panic!(self, span, "Unexpected type kind: bound")
            }
            hax::Ty::Placeholder(_) => {
                trace!("PlaceHolder");
                error_or_panic!(self, span, "Unsupported type: placeholder")
            }
            hax::Ty::Arrow(box sig) => {
                trace!("Arrow");
                trace!("bound vars: {:?}", sig.bound_vars);

                // Translate the generics parameters.
                // Note that there can only be bound regions.
                let bound_region_names: Vec<Option<String>> = sig
                    .bound_vars
                    .iter()
                    .map(|p| {
                        use hax::BoundVariableKind::*;
                        match p {
                            Region(region) => Ok(translate_bound_region_kind_name(region)),
                            Ty(_) => {
                                error_or_panic!(
                                    self,
                                    span,
                                    "Unexpected locally bound type variable"
                                );
                            }
                            Const => {
                                error_or_panic!(
                                    self,
                                    span,
                                    "Unexpected locally bound const generic variable"
                                );
                            }
                        }
                    })
                    .try_collect()?;

                // Push the ground region group
                let erase_regions = false;
                self.with_locally_bound_regions_group(bound_region_names, move |ctx| {
                    let regions = ctx.region_vars[0].clone();
                    let inputs = sig
                        .value
                        .inputs
                        .iter()
                        .map(|x| ctx.translate_ty(span, erase_regions, x))
                        .try_collect()?;
                    let output = ctx.translate_ty(span, erase_regions, &sig.value.output)?;
                    Ok(Ty::Arrow(regions, inputs, Box::new(output)))
                })
            }
            hax::Ty::Error => {
                trace!("Error");
                error_or_panic!(self, span, "Type checking error")
            }
            hax::Ty::Todo(s) => {
                trace!("Todo: {s}");
                error_or_panic!(self, span, format!("Unsupported type: {:?}", s))
            }
        }
    }

    #[allow(clippy::type_complexity)]
    pub fn translate_substs(
        &mut self,
        span: rustc_span::Span,
        erase_regions: bool,
        used_params: Option<Vec<bool>>,
        substs: &[hax::GenericArg],
    ) -> Result<(Vec<Region>, Vec<Ty>, Vec<ConstGeneric>), Error> {
        trace!("{:?}", substs);
        // Filter the parameters
        let substs: Vec<&hax::GenericArg> = match used_params {
            Option::None => substs.iter().collect(),
            Option::Some(used_args) => {
                error_assert!(self, span, substs.len() == used_args.len());
                substs
                    .iter()
                    .zip(used_args.into_iter())
                    .filter_map(|(param, used)| if used { Some(param) } else { None })
                    .collect()
            }
        };

        let mut regions: Vec<Region> = vec![];
        let mut params = vec![];
        let mut cgs = vec![];
        for param in substs.iter() {
            match param {
                hax::GenericArg::Type(param_ty) => {
                    let param_ty = self.translate_ty(span, erase_regions, param_ty)?;
                    params.push(param_ty);
                }
                hax::GenericArg::Lifetime(region) => {
                    regions.push(self.translate_region(span, erase_regions, region)?);
                }
                hax::GenericArg::Const(c) => {
                    cgs.push(self.translate_constant_expr_to_const_generic(span, c)?);
                }
            }
        }

        Ok((regions, params, cgs))
    }

    pub fn translate_substs_and_trait_refs(
        &mut self,
        span: rustc_span::Span,
        erase_regions: bool,
        used_params: Option<Vec<bool>>,
        substs: &[hax::GenericArg],
        trait_refs: &[hax::ImplSource],
    ) -> Result<GenericArgs, Error> {
        let (regions, types, const_generics) =
            self.translate_substs(span, erase_regions, used_params, substs)?;
        let trait_refs = self.translate_trait_impl_sources(span, erase_regions, trait_refs)?;
        Ok(GenericArgs {
            regions,
            types,
            const_generics,
            trait_refs,
        })
    }

    /// Translate a type def id
    pub(crate) fn translate_type_id(
        &mut self,
        span: rustc_span::Span,
        def_id: &hax::DefId,
    ) -> TypeId {
        trace!("{:?}", def_id);
        let rust_id = def_id.rust_def_id.unwrap();
        if rust_id.is_local() {
            TypeId::Adt(self.translate_type_decl_id(span, rust_id))
        } else {
            // Non-local: check if the type has primitive support

            // Retrieve the type name
            let name = self.t_ctx.def_id_to_name(def_id);

            match assumed::get_type_id_from_name(&name) {
                Option::Some(id) => {
                    // The type has primitive support
                    TypeId::Assumed(id)
                }
                Option::None => {
                    // The type is external
                    TypeId::Adt(self.translate_type_decl_id(span, rust_id))
                }
            }
        }
    }

    /// Translate the body of a type declaration.
    ///
    /// Note that the type may be external, in which case we translate the body
    /// only if it is public (i.e., it is a public enumeration, or it is a
    /// struct with only public fields).
    fn translate_type_body(
        &mut self,
        is_local: bool,
        trans_id: TypeDeclId::Id,
        adt: hax::AdtDef,
    ) -> Result<TypeDeclKind, Error> {
        trace!("{}", trans_id);
        let def_span = self.t_ctx.tcx.def_span(adt.did.rust_def_id.unwrap());

        // In case the type is external, check if we should consider the type as
        // transparent (i.e., extract its body). If it is an enumeration, then yes
        // (because the variants of public enumerations are public, together with their
        // fields). If it is a structure, we check if all the fields are public.
        let is_transparent = is_local
            || match &adt.adt_kind {
                hax::AdtKind::Enum => true,
                hax::AdtKind::Struct => {
                    // Check the unique variant
                    error_assert!(self, def_span, adt.variants.raw.len() == 1);
                    adt.variants.raw[0]
                        .fields
                        .iter()
                        .all(|f| matches!(f.vis, hax::Visibility::Public))
                }
                hax::AdtKind::Union => {
                    error_or_panic!(self, def_span, "Unions are not supported")
                }
            };

        if !is_transparent {
            return Ok(TypeDeclKind::Opaque);
        }

        // The type is transparent: explore the variants
        let mut var_id = VariantId::Id::new(0); // Variant index
        let mut variants: Vec<Variant> = vec![];
        let erase_regions = false;
        for var_def in adt.variants.raw {
            trace!("variant {}: {:?}", var_id, var_def);

            let mut fields: Vec<Field> = vec![];
            let mut field_id = FieldId::Id::new(0);
            /* This is for sanity: check that either all the fields have names, or
             * none of them has */
            let mut have_names: Option<bool> = Option::None;
            for field_def in var_def.fields.into_iter() {
                trace!("variant {}: field {}: {:?}", var_id, field_id, field_def);
                let field_span = field_def.span.rust_span;

                // Translate the field type
                let ty = self.translate_ty(field_span, erase_regions, &field_def.ty)?;

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
                        error_assert!(self, field_span, *b == field_name.is_some());
                    }
                };

                // Translate the span information
                let meta = self.translate_meta_from_rspan(field_def.span);

                // Store the field
                let field = Field {
                    meta,
                    name: field_name.clone(),
                    ty,
                };
                fields.push(field);

                field_id.incr();
            }

            let meta = self.translate_meta_from_rspan(var_def.span);
            let variant_name = var_def.name;
            variants.push(Variant {
                meta,
                name: variant_name,
                fields: FieldId::Vector::from(fields),
            });

            var_id.incr();
        }

        // Register the type
        use hax::AdtKind;
        let type_def_kind: TypeDeclKind = match adt.adt_kind {
            AdtKind::Struct => TypeDeclKind::Struct(variants[0].fields.clone()),
            AdtKind::Enum => TypeDeclKind::Enum(VariantId::Vector::from(variants)),
            AdtKind::Union => {
                let span = self.t_ctx.tcx.def_span(adt.did.rust_def_id.unwrap());
                error_or_panic!(self, span, "Union types are not supported")
            }
        };

        Ok(type_def_kind)
    }

    /// Sanity check: region names are pairwise distinct (this caused trouble
    /// when generating names for the backward functions in Aeneas): at some
    /// point, Rustc introduced names equal to `Some("'_")` for the anonymous
    /// regions, instead of using `None` (we now check in [translate_region_name]
    /// and ignore names equal to "'_").
    pub(crate) fn check_generics(&self) {
        let mut s = std::collections::HashSet::new();
        for r in self.region_vars.get(0).unwrap() {
            let name = &r.name;
            if name.is_some() {
                let name = name.as_ref().unwrap();
                assert!(
                    !s.contains(name),
                    "Name \"{}\" used for different lifetimes",
                    name
                );
                s.insert(name.clone());
            }
        }
    }

    /// Auxiliary helper.
    ///
    /// Translate the generics of a type definition.
    /// Returns the translation, together with an instantiated MIR substitution,
    /// which represents the generics on the MIR side (and is useful to translate
    /// the body of the type...).
    ///
    /// Rem.: this seems simpler in [crate::translate_functions_to_ullbc].
    /// TODO: compare and simplify/factorize?
    pub(crate) fn translate_generic_params(&mut self, def_id: DefId) -> Result<(), Error> {
        let tcx = self.t_ctx.tcx;
        let span = tcx.def_span(def_id);

        // We could use: TyCtxt::generics_of(DefId)
        // But using the identity substitution is simpler. For instance, we can
        // easily retrieve the type for the const parameters.
        let substs = rustc_middle::ty::subst::InternalSubsts::identity_for_item(tcx, def_id)
            .sinto(&self.hax_state);

        self.translate_generic_params_from_hax(span, &substs)
    }

    pub(crate) fn translate_generic_params_from_hax(
        &mut self,
        span: rustc_span::Span,
        substs: &Vec<hax::GenericArg>,
    ) -> Result<(), Error> {
        let erase_regions = false;
        for p in substs {
            use hax::GenericArg::*;
            match p {
                Type(p) => {
                    // The type should be a Param
                    if let hax::Ty::Param(p) = p {
                        let _ = self.push_type_var(p.index, p.name.clone());
                    } else {
                        unreachable!("unexpected");
                    }
                }
                Lifetime(region) => {
                    let name = translate_region_name(region);
                    let _ = self.push_free_region(region.clone(), name);
                }
                Const(c) => {
                    // The type should be primitive, meaning it shouldn't contain variables,
                    // non-primitive adts, etc. As a result, we can use an empty context.
                    let ty = self.translate_ty(span, erase_regions, &c.ty)?;
                    let ty = ty.to_literal();
                    if let hax::ConstantExprKind::ConstRef { id: cp } = &*c.contents {
                        self.push_const_generic_var(cp.index, ty, cp.name.clone());
                    } else {
                        unreachable!();
                    }
                }
            }
        }

        // Sanity check
        self.check_generics();

        Ok(())
    }
}

impl<'tcx, 'ctx> TransCtx<'tcx, 'ctx> {
    /// Translate a type definition.
    ///
    /// Note that we translate the types one by one: we don't need to take into
    /// account the fact that some types are mutually recursive at this point
    /// (we will need to take that into account when generating the code in a file).
    pub(crate) fn translate_type(&mut self, rust_id: DefId) {
        self.with_def_id(rust_id, |ctx| {
            if ctx.translate_type_aux(rust_id).is_err() {
                let span = ctx.tcx.def_span(rust_id);
                ctx.span_err(
                    span,
                    &format!("Ignoring the following type due to an error: {:?}", rust_id),
                );
                // Save the definition
                let _ = ctx.ignored_failed_decls.insert(rust_id);
            }
        });
    }

    /// Auxliary helper to properly handle errors, see [translate_type].
    fn translate_type_aux(&mut self, rust_id: DefId) -> Result<(), Error> {
        let trans_id = self.translate_type_decl_id(&None, rust_id);
        let is_transparent = self.id_is_transparent(rust_id);

        let mut bt_ctx = BodyTransCtx::new(rust_id, self);

        // Check and translate the generics
        bt_ctx.translate_generic_params(rust_id)?;

        // Translate the predicates
        bt_ctx.translate_predicates_solve_trait_obligations_of(None, rust_id)?;

        // Check if the type has been explicitely marked as opaque.
        // If yes, ignore it, otherwise, dive into the body. Note that for
        // external types we have to check the body: if the body is
        // public, we translate it, otherwise we consider the type as opaque.
        // For instance, because `core::option::Option` is public, we can
        // manipulate its variants. If we encounter this type, we must retrieve
        // its definition.
        let is_local = rust_id.is_local();
        let kind = if !is_transparent {
            TypeDeclKind::Opaque
        } else {
            let adt = bt_ctx.t_ctx.tcx.adt_def(rust_id).sinto(&bt_ctx.hax_state);
            match bt_ctx.translate_type_body(is_local, trans_id, adt) {
                Ok(kind) => kind,
                Err(err) => TypeDeclKind::Error(err.msg),
            }
        };

        // Register the type
        let name = bt_ctx
            .t_ctx
            .extended_def_id_to_name(&rust_id.sinto(&bt_ctx.hax_state));
        let generics = bt_ctx.get_generics();

        // Translate the span information
        let meta = bt_ctx.translate_meta_from_rid(rust_id);

        let type_def = TypeDecl {
            def_id: trans_id,
            meta,
            is_local,
            name,
            generics,
            preds: bt_ctx.get_predicates(),
            kind,
        };

        trace!("translate_type: preds: {:?}", &type_def.preds);

        trace!(
            "{} -> {}",
            trans_id.to_string(),
            type_def.fmt_with_ctx(&self.into_fmt())
        );

        self.type_decls.insert(trans_id, type_def);

        Ok(())
    }
}
