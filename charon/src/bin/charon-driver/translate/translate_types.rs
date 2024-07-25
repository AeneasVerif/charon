use crate::translate::translate_traits::PredicateLocation;

use super::translate_ctx::*;
use charon_lib::assumed;
use charon_lib::ast::*;
use charon_lib::common::*;
use charon_lib::formatter::IntoFormatter;
use charon_lib::ids::Vector;
use charon_lib::pretty::FmtWithCtx;
use core::convert::*;
use hax::Visibility;
use hax_frontend_exporter as hax;
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
        BrAnon => None,
        BrNamed(_, symbol) => Some(symbol.clone()),
        BrEnv => Some("@env".to_owned()),
    };
    check_region_name(s)
}

pub fn translate_region_name(region: &hax::Region) -> Option<String> {
    // Compute the region name
    use hax::{BoundRegionKind::*, RegionKind::*};
    let s = match &region.kind {
        ReEarlyParam(r) => Some(r.name.clone()),
        ReBound(_, br) => translate_bound_region_kind_name(&br.kind),
        ReLateParam(r) => match &r.bound_region {
            BrAnon => None,
            BrNamed(_, symbol) => Some(symbol.clone()),
            BrEnv => Some("@env".to_owned()),
        },
        ReErased => None,
        ReStatic => todo!(),
        ReVar(_) => todo!(),
        RePlaceholder(_) => todo!(),
        ReError(_) => todo!(),
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
                hax::RegionKind::ReBound(id, br) => {
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
                        if let hax::RegionKind::ReEarlyParam(eb) = &rk.kind {
                            if eb.index as usize == *re_var {
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
            hax::Ty::Int(int_ty) => {
                use hax::IntTy;
                Ok(Ty::Literal(LiteralTy::Integer(match int_ty {
                    IntTy::Isize => IntegerTy::Isize,
                    IntTy::I8 => IntegerTy::I8,
                    IntTy::I16 => IntegerTy::I16,
                    IntTy::I32 => IntegerTy::I32,
                    IntTy::I64 => IntegerTy::I64,
                    IntTy::I128 => IntegerTy::I128,
                })))
            }
            hax::Ty::Uint(int_ty) => {
                use hax::UintTy;
                Ok(Ty::Literal(LiteralTy::Integer(match int_ty {
                    UintTy::Usize => IntegerTy::Usize,
                    UintTy::U8 => IntegerTy::U8,
                    UintTy::U16 => IntegerTy::U16,
                    UintTy::U32 => IntegerTy::U32,
                    UintTy::U64 => IntegerTy::U64,
                    UintTy::U128 => IntegerTy::U128,
                })))
            }
            hax::Ty::Float(_) => {
                trace!("Float");
                error_or_panic!(self, span, "Floats are not supported yet")
            }
            hax::Ty::Never => Ok(Ty::Never),

            hax::Ty::Alias(alias) => match &alias.kind {
                hax::AliasKind::Projection {
                    impl_expr,
                    assoc_item,
                } => {
                    let trait_ref =
                        self.translate_trait_impl_expr(span, erase_regions, impl_expr)?;
                    // This should succeed because no marker trait (that we may
                    // ignore) has associated types.
                    let trait_ref = trait_ref.unwrap();
                    let name = TraitItemName(assoc_item.name.clone().into());
                    Ok(Ty::TraitType(trait_ref, name))
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
                let adt_did: DefId = def_id.into();
                trace!("Adt: {:?}", adt_did);

                // Retrieve the list of used arguments
                let used_params = if adt_did.is_local() {
                    None
                } else {
                    let name = self.t_ctx.def_id_to_name(DefId::from(def_id))?;
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
                let def_id = self.translate_type_id(span, def_id)?;

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
            hax::Ty::RawPtr(ty, mutbl) => {
                trace!("RawPtr: {:?}", (ty, mutbl));
                let ty = self.translate_ty(span, erase_regions, ty)?;
                let kind = if *mutbl {
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
                    format!("Unsupported type: foreign type: {:?}", DefId::from(id))
                )
            }
            hax::Ty::Infer(_) => {
                trace!("Infer");
                error_or_panic!(self, span, "Unsupported type: infer type")
            }

            hax::Ty::Dynamic(_existential_preds, _region, _) => {
                // TODO: we don't translate the predicates yet because our machinery can't handle
                // it.
                trace!("Dynamic");
                Ok(Ty::DynTrait(ExistentialPredicate))
            }

            hax::Ty::Coroutine(..) => {
                trace!("Coroutine");
                error_or_panic!(self, span, "Coroutine types are not supported yet")
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
            None => substs.iter().collect(),
            Some(used_args) => {
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
        use hax::GenericArg::*;
        for param in substs.iter() {
            match param {
                Type(param_ty) => {
                    let param_ty = self.translate_ty(span, erase_regions, param_ty)?;
                    params.push(param_ty);
                }
                Lifetime(region) => {
                    regions.push(self.translate_region(span, erase_regions, region)?);
                }
                Const(c) => {
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
        trait_refs: &[hax::ImplExpr],
    ) -> Result<GenericArgs, Error> {
        let (regions, types, const_generics) =
            self.translate_substs(span, erase_regions, used_params, substs)?;
        let trait_refs = self.translate_trait_impl_exprs(span, erase_regions, trait_refs)?;
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
    ) -> Result<TypeId, Error> {
        trace!("{:?}", def_id);
        let rust_id: DefId = def_id.into();
        if rust_id.is_local() {
            Ok(TypeId::Adt(self.register_type_decl_id(span, rust_id)))
        } else {
            // Non-local: check if the type has primitive support

            // Retrieve the type name
            let name = self.t_ctx.hax_def_id_to_name(def_id)?;
            match assumed::get_type_id_from_name(&name) {
                Some(id) => {
                    // The type has primitive support
                    Ok(TypeId::Assumed(id))
                }
                None => {
                    // The type is external
                    Ok(TypeId::Adt(self.register_type_decl_id(span, rust_id)))
                }
            }
        }
    }

    /// Translate the body of a type declaration.
    ///
    /// Note that the type may be external, in which case we translate the body
    /// only if it is public (i.e., it is a public enumeration, or it is a
    /// struct with only public fields).
    fn translate_adt_def(
        &mut self,
        trans_id: TypeDeclId,
        def_span: rustc_span::Span,
        item_meta: &ItemMeta,
        adt: &hax::AdtDef,
    ) -> Result<TypeDeclKind, Error> {
        use hax::AdtKind;
        let erase_regions = false;

        if item_meta.opacity.is_opaque() {
            return Ok(TypeDeclKind::Opaque);
        }

        trace!("{}", trans_id);

        // In case the type is external, check if we should consider the type as
        // transparent (i.e., extract its body). If it is an enumeration, then yes
        // (because the variants of public enumerations are public, together with their
        // fields). If it is a structure, we check if all the fields are public.
        let contents_are_public = match adt.adt_kind {
            AdtKind::Enum => true,
            AdtKind::Struct => {
                // Check the unique variant
                error_assert!(self, def_span, adt.variants.len() == 1);
                adt.variants[0]
                    .fields
                    .iter()
                    .all(|f| matches!(f.vis, Visibility::Public))
            }
            AdtKind::Union => {
                error_or_panic!(self, def_span, "Unions are not supported")
            }
        };

        if item_meta
            .opacity
            .with_content_visibility(contents_are_public)
            .is_opaque()
        {
            return Ok(TypeDeclKind::Opaque);
        }

        // The type is transparent: explore the variants
        let mut variants: Vector<VariantId, Variant> = Default::default();
        for (i, var_def) in adt.variants.iter().enumerate() {
            trace!("variant {i}: {var_def:?}");

            let mut fields: Vector<FieldId, Field> = Default::default();
            /* This is for sanity: check that either all the fields have names, or
             * none of them has */
            let mut have_names: Option<bool> = None;
            for (j, field_def) in var_def.fields.iter().enumerate() {
                trace!("variant {i}: field {j}: {field_def:?}");
                let field_span = self.t_ctx.translate_span_from_rspan(field_def.span.clone());
                let field_rspan = field_span.span.rust_span_data.span();
                // Translate the field type
                let ty = self.translate_ty(field_rspan, erase_regions, &field_def.ty)?;
                let field_attrs = self
                    .t_ctx
                    .translate_attr_info_from_rid(DefId::from(&field_def.did), field_span);

                // Retrieve the field name.
                let field_name = field_def.name.clone();
                // Sanity check
                match &have_names {
                    None => {
                        have_names = match &field_name {
                            None => Some(false),
                            Some(_) => Some(true),
                        }
                    }
                    Some(b) => {
                        error_assert!(self, field_rspan, *b == field_name.is_some());
                    }
                };

                // Store the field
                let field = Field {
                    span: field_span,
                    attr_info: field_attrs,
                    name: field_name.clone(),
                    ty,
                };
                fields.push(field);
            }

            let discriminant = self.translate_discriminant(def_span, &var_def.discr_val)?;
            let variant_span = self.t_ctx.translate_span_from_rspan(var_def.span.clone());
            let variant_name = var_def.name.clone();
            let variant_attrs = self
                .t_ctx
                .translate_attr_info_from_rid(DefId::from(&var_def.def_id), variant_span);

            let mut variant = Variant {
                span: variant_span,
                attr_info: variant_attrs,
                name: variant_name,
                fields,
                discriminant,
            };
            // Propagate a `#[charon::variants_prefix(..)]` or `#[charon::variants_suffix(..)]` attribute to the variants.
            if variant.attr_info.rename.is_none() {
                let prefix = item_meta
                    .attr_info
                    .attributes
                    .iter()
                    .find(|a| a.is_variants_prefix())
                    .map(|attr| attr.as_variants_prefix().as_str());
                let suffix = item_meta
                    .attr_info
                    .attributes
                    .iter()
                    .find(|a| a.is_variants_suffix())
                    .map(|attr| attr.as_variants_suffix().as_str());
                if prefix.is_some() || suffix.is_some() {
                    let prefix = prefix.unwrap_or_default();
                    let suffix = suffix.unwrap_or_default();
                    let name = &variant.name;
                    variant.attr_info.rename = Some(format!("{prefix}{name}{suffix}"));
                }
            }
            variants.push(variant);
        }

        // Register the type
        let type_def_kind: TypeDeclKind = match adt.adt_kind {
            AdtKind::Struct => TypeDeclKind::Struct(variants[0].fields.clone()),
            AdtKind::Enum => TypeDeclKind::Enum(variants),
            AdtKind::Union => {
                error_or_panic!(self, def_span, "Union types are not supported")
            }
        };

        Ok(type_def_kind)
    }

    fn translate_discriminant(
        &mut self,
        def_span: rustc_span::Span,
        discr: &hax::DiscriminantValue,
    ) -> Result<ScalarValue, Error> {
        let ty = self.translate_ty(def_span, true, &discr.ty)?;
        let int_ty = *ty.as_literal().as_integer();
        Ok(ScalarValue::from_bits(int_ty, discr.val))
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

    /// Add the generics and predicates of this item and its parents to the current context.
    pub(crate) fn push_generics_for_def(
        &mut self,
        span: rustc_span::Span,
        rust_id: DefId,
        def: &hax::Def,
    ) -> Result<(), Error> {
        // Add generics from the parent item, recursively (this is useful for closures, as they
        // could be nested).
        if let Some(parent) = def.parent() {
            let parent_id = parent.into();
            let parent_def = self.t_ctx.hax_def(parent_id);
            self.push_generics_for_def(span, parent_id, &parent_def)?;
        }
        if let Some((generics, predicates)) = def.generics() {
            // Add the generic params.
            self.push_generic_params(span, generics)?;
            // Add the self trait clause.
            match def {
                hax::Def::Impl { of_trait: true, .. } => {
                    self.translate_trait_impl_self_trait_clause(rust_id)?;
                }
                hax::Def::Trait { .. } => {
                    self.translate_trait_decl_self_trait_clause(rust_id)?;
                }
                _ => {}
            }
            // Add the predicates.
            let (origin, location) = match def {
                hax::Def::Struct { .. }
                | hax::Def::Union { .. }
                | hax::Def::Enum { .. }
                | hax::Def::TyAlias { .. }
                | hax::Def::AssocTy { .. } => {
                    (PredicateOrigin::WhereClauseOnType, PredicateLocation::Base)
                }
                hax::Def::Fn { .. }
                | hax::Def::AssocFn { .. }
                | hax::Def::Const { .. }
                | hax::Def::AssocConst { .. }
                | hax::Def::Static { .. } => {
                    (PredicateOrigin::WhereClauseOnFn, PredicateLocation::Base)
                }
                hax::Def::Impl { .. } => {
                    (PredicateOrigin::WhereClauseOnImpl, PredicateLocation::Base)
                }
                // TODO: distinguish trait where clauses from trait supertraits. Currently we
                // consider them all as parent clauses.
                hax::Def::Trait { .. } => {
                    let trait_id = self.register_trait_decl_id(span, rust_id)?.unwrap();
                    (
                        PredicateOrigin::WhereClauseOnTrait,
                        PredicateLocation::Parent(trait_id),
                    )
                }
                _ => panic!("Unexpected def: {def:?}"),
            };
            self.translate_predicates(predicates, origin, &location)?;
        }
        Ok(())
    }

    pub(crate) fn push_generic_params(
        &mut self,
        span: rustc_span::Span,
        generics: &hax::TyGenerics,
    ) -> Result<(), Error> {
        for param in &generics.params {
            self.push_generic_param(span, param)?;
        }
        Ok(())
    }

    pub(crate) fn push_generic_param(
        &mut self,
        span: rustc_span::Span,
        param: &hax::GenericParamDef,
    ) -> Result<(), Error> {
        match &param.kind {
            hax::GenericParamDefKind::Lifetime => {
                let region = hax::Region {
                    kind: hax::RegionKind::ReEarlyParam(hax::EarlyParamRegion {
                        index: param.index,
                        name: param.name.clone(),
                    }),
                };
                let _ = self.push_free_region(region);
            }
            hax::GenericParamDefKind::Type { .. } => {
                let _ = self.push_type_var(param.index, param.name.clone());
            }
            hax::GenericParamDefKind::Const { ty, .. } => {
                // The type should be primitive, meaning it shouldn't contain variables,
                // non-primitive adts, etc. As a result, we can use an empty context.
                let ty = self.translate_ty(span, false, ty)?;
                let ty = ty.to_literal();
                self.push_const_generic_var(param.index, ty, param.name.clone());
            }
        }

        Ok(())
    }
}

impl<'tcx, 'ctx> TranslateCtx<'tcx, 'ctx> {
    /// Translate a type definition.
    ///
    /// Note that we translate the types one by one: we don't need to take into
    /// account the fact that some types are mutually recursive at this point
    /// (we will need to take that into account when generating the code in a file).
    pub fn translate_type(
        &mut self,
        trans_id: TypeDeclId,
        rust_id: DefId,
        item_meta: ItemMeta,
        def: &hax::Def,
    ) -> Result<TypeDecl, Error> {
        let mut bt_ctx = BodyTransCtx::new(rust_id, self);

        let erase_regions = false;
        let span = item_meta.span.rust_span();

        // Translate generics and predicates
        bt_ctx.push_generics_for_def(span, rust_id, def)?;
        let generics = bt_ctx.get_generics();

        // Translate type body
        let kind = match def {
            _ if item_meta.opacity.is_opaque() => Ok(TypeDeclKind::Opaque),
            hax::Def::OpaqueTy | hax::Def::ForeignTy => Ok(TypeDeclKind::Opaque),
            hax::Def::TyAlias { ty, .. } => {
                // We only translate crate-local type aliases so the `unwrap` is ok.
                let ty = ty.as_ref().unwrap();
                bt_ctx
                    .translate_ty(span, erase_regions, ty)
                    .map(TypeDeclKind::Alias)
            }
            hax::Def::Struct { def, .. }
            | hax::Def::Enum { def, .. }
            | hax::Def::Union { def, .. } => {
                bt_ctx.translate_adt_def(trans_id, span, &item_meta, def)
            }
            _ => panic!("Unexpected item when translating types: {def:?}"),
        };

        let kind = match kind {
            Ok(kind) => kind,
            Err(err) => TypeDeclKind::Error(err.msg),
        };
        let type_def = TypeDecl {
            def_id: trans_id,
            item_meta,
            generics,
            kind,
        };

        trace!(
            "{} -> {}",
            trans_id.to_string(),
            type_def.fmt_with_ctx(&self.into_fmt())
        );

        Ok(type_def)
    }
}
