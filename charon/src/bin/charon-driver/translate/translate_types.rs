use crate::translate::translate_traits::PredicateLocation;

use super::translate_ctx::*;
use charon_lib::ast::*;
use charon_lib::builtins;
use charon_lib::common::*;
use charon_lib::formatter::IntoFormatter;
use charon_lib::ids::Vector;
use charon_lib::pretty::FmtWithCtx;
use core::convert::*;
use hax::Visibility;
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
                        .expect("Error: missing binder when translating lifetime")
                        .get(br.var)
                        .unwrap();
                    let br_id = DeBruijnId::new(*id);
                    Ok(Region::BVar(br_id, *rid))
                }
                hax::RegionKind::ReVar(_) => {
                    // Shouldn't exist outside of type inference.
                    let err = format!("Should not exist outside of type inference: {region:?}");
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
    #[tracing::instrument(skip(self, span, erase_regions))]
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
            hax::Ty::Float(float_ty) => {
                use hax::FloatTy;
                Ok(Ty::Literal(LiteralTy::Float(match float_ty {
                    FloatTy::F16 => charon_lib::ast::types::FloatTy::F16,
                    FloatTy::F32 => charon_lib::ast::types::FloatTy::F32,
                    FloatTy::F64 => charon_lib::ast::types::FloatTy::F64,
                    FloatTy::F128 => charon_lib::ast::types::FloatTy::F128,
                })))
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
                trace!("Adt: {:?}", def_id);

                // Retrieve the type identifier
                let type_id = self.translate_type_id(span, def_id)?;

                // Retrieve the list of used arguments
                let used_params = if let TypeId::Builtin(builtin_ty) = type_id {
                    Some(builtins::type_to_used_params(builtin_ty))
                } else {
                    None
                };

                // Translate the type parameters instantiation
                let generics = self.translate_substs_and_trait_refs(
                    span,
                    erase_regions,
                    used_params,
                    substs,
                    trait_refs,
                )?;

                // Return the instantiated ADT
                Ok(Ty::Adt(type_id, generics))
            }
            hax::Ty::Str => {
                trace!("Str");

                let id = TypeId::Builtin(BuiltinTy::Str);
                Ok(Ty::Adt(id, GenericArgs::empty()))
            }
            hax::Ty::Array(ty, const_param) => {
                trace!("Array");

                let c = self.translate_constant_expr_to_const_generic(span, const_param)?;
                let tys = vec![self.translate_ty(span, erase_regions, ty)?].into();
                let cgs = vec![c].into();
                let id = TypeId::Builtin(BuiltinTy::Array);
                Ok(Ty::Adt(
                    id,
                    GenericArgs::new(Vector::new(), tys, cgs, Vector::new()),
                ))
            }
            hax::Ty::Slice(ty) => {
                trace!("Slice");

                let tys = vec![self.translate_ty(span, erase_regions, ty)?].into();
                let id = TypeId::Builtin(BuiltinTy::Slice);
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

                let mut params = Vector::new();
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
                    Some(var_id) => Ok(Ty::TypeVar(*var_id)),
                }
            }

            hax::Ty::Foreign(def_id) => {
                trace!("Foreign");
                let def_id = self.translate_type_id(span, def_id)?;
                Ok(Ty::Adt(def_id, GenericArgs::empty()))
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

                let erase_regions = false;
                let binder = sig.as_ref().map(|_| ());
                self.with_locally_bound_regions_group(span, binder, move |ctx| {
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
    ) -> Result<
        (
            Vector<RegionId, Region>,
            Vector<TypeVarId, Ty>,
            Vector<ConstGenericVarId, ConstGeneric>,
        ),
        Error,
    > {
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

        let mut regions = Vector::new();
        let mut params = Vector::new();
        let mut cgs = Vector::new();
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

    /// Checks whether the given id corresponds to a built-in type.
    fn recognize_builtin_type(&mut self, def_id: &hax::DefId) -> Result<Option<BuiltinTy>, Error> {
        use rustc_hir::lang_items::LangItem;
        let tcx = self.t_ctx.tcx;
        let rust_id = DefId::from(def_id);
        let ty = if tcx.is_lang_item(rust_id, LangItem::OwnedBox) {
            Some(BuiltinTy::Box)
        } else {
            None
        };
        Ok(ty)
    }

    /// Translate a type def id
    pub(crate) fn translate_type_id(
        &mut self,
        span: rustc_span::Span,
        def_id: &hax::DefId,
    ) -> Result<TypeId, Error> {
        trace!("{:?}", def_id);
        let type_id = match self.recognize_builtin_type(def_id)? {
            Some(id) => TypeId::Builtin(id),
            None => TypeId::Adt(self.register_type_decl_id(span, def_id)),
        };
        Ok(type_id)
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
            AdtKind::Struct | AdtKind::Union => {
                // Check the unique variant
                error_assert!(self, def_span, adt.variants.len() == 1);
                adt.variants[0]
                    .fields
                    .iter()
                    .all(|f| matches!(f.vis, Visibility::Public))
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
                let field_span = self.t_ctx.translate_span_from_hax(field_def.span.clone());
                let field_rspan = field_span.span.rust_span_data.span();
                // Translate the field type
                let ty = self.translate_ty(field_rspan, erase_regions, &field_def.ty)?;
                let field_full_def = self.t_ctx.hax_def(&field_def.did);
                let field_attrs = self.t_ctx.translate_attr_info(&field_full_def);

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
            let variant_span = self.t_ctx.translate_span_from_hax(var_def.span.clone());
            let variant_name = var_def.name.clone();
            let variant_full_def = self.t_ctx.hax_def(&var_def.def_id);
            let variant_attrs = self.t_ctx.translate_attr_info(&variant_full_def);

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
                    .filter_map(|a| a.as_variants_prefix())
                    .next()
                    .map(|attr| attr.as_str());
                let suffix = item_meta
                    .attr_info
                    .attributes
                    .iter()
                    .filter_map(|a| a.as_variants_suffix())
                    .next()
                    .map(|attr| attr.as_str());
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
            AdtKind::Union => TypeDeclKind::Union(variants[0].fields.clone()),
        };

        Ok(type_def_kind)
    }

    fn translate_discriminant(
        &mut self,
        def_span: rustc_span::Span,
        discr: &hax::DiscriminantValue,
    ) -> Result<ScalarValue, Error> {
        let ty = self.translate_ty(def_span, true, &discr.ty)?;
        let int_ty = *ty.as_literal().unwrap().as_integer().unwrap();
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
        def: &hax::FullDef,
    ) -> Result<(), Error> {
        use hax::FullDefKind;
        // Add generics from the parent item, recursively (recursivity is useful for closures, as
        // they could be nested).
        match &def.kind {
            FullDefKind::AssocTy { parent, .. }
            | FullDefKind::AssocFn { parent, .. }
            | FullDefKind::AssocConst { parent, .. }
            | FullDefKind::Closure { parent, .. } => {
                let parent_def = self.t_ctx.hax_def(parent);
                self.push_generics_for_def(span, &parent_def)?;
            }
            _ => {}
        }
        if let Some((generics, predicates)) = def.generics() {
            // Add the generic params.
            self.push_generic_params(span, generics)?;
            // Add the self trait clause.
            match &def.kind {
                FullDefKind::Impl {
                    impl_subject: hax::ImplSubject::Trait(self_predicate),
                    ..
                }
                | FullDefKind::Trait { self_predicate, .. } => {
                    self.register_trait_decl_id(span, &self_predicate.trait_ref.def_id);
                    let hax_span = span.sinto(&self.t_ctx.hax_state);
                    self.translate_self_trait_clause(&hax_span, &self_predicate)?;
                }
                _ => {}
            }
            // Add the predicates.
            let (origin, location) = match &def.kind {
                FullDefKind::Struct { .. }
                | FullDefKind::Union { .. }
                | FullDefKind::Enum { .. }
                | FullDefKind::TyAlias { .. }
                | FullDefKind::AssocTy { .. } => {
                    (PredicateOrigin::WhereClauseOnType, PredicateLocation::Base)
                }
                FullDefKind::Fn { .. }
                | FullDefKind::AssocFn { .. }
                | FullDefKind::Const { .. }
                | FullDefKind::AssocConst { .. }
                | FullDefKind::Static { .. } => {
                    (PredicateOrigin::WhereClauseOnFn, PredicateLocation::Base)
                }
                FullDefKind::Impl { .. } => {
                    (PredicateOrigin::WhereClauseOnImpl, PredicateLocation::Base)
                }
                // TODO: distinguish trait where clauses from trait supertraits. Currently we
                // consider them all as parent clauses.
                FullDefKind::Trait { .. } => {
                    let trait_id = self.register_trait_decl_id(span, &def.def_id);
                    (
                        PredicateOrigin::WhereClauseOnTrait,
                        PredicateLocation::Parent(trait_id),
                    )
                }
                _ => panic!("Unexpected def: {def:?}"),
            };
            self.register_predicates(predicates, origin, &location)?;
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
                let ty = ty.to_literal().unwrap();
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
    #[tracing::instrument(skip(self, rust_id, item_meta))]
    pub fn translate_type(
        &mut self,
        trans_id: TypeDeclId,
        rust_id: DefId,
        item_meta: ItemMeta,
        def: &hax::FullDef,
    ) -> Result<TypeDecl, Error> {
        let mut bt_ctx = BodyTransCtx::new(rust_id, self);

        let erase_regions = false;
        let span = item_meta.span.rust_span();

        // Translate generics and predicates
        bt_ctx.push_generics_for_def(span, def)?;
        let generics = bt_ctx.get_generics();

        // Translate type body
        let kind = match &def.kind {
            _ if item_meta.opacity.is_opaque() => Ok(TypeDeclKind::Opaque),
            hax::FullDefKind::OpaqueTy | hax::FullDefKind::ForeignTy => Ok(TypeDeclKind::Opaque),
            hax::FullDefKind::TyAlias { ty, .. } => {
                // We only translate crate-local type aliases so the `unwrap` is ok.
                let ty = ty.as_ref().unwrap();
                bt_ctx
                    .translate_ty(span, erase_regions, ty)
                    .map(TypeDeclKind::Alias)
            }
            hax::FullDefKind::Struct { def, .. }
            | hax::FullDefKind::Enum { def, .. }
            | hax::FullDefKind::Union { def, .. } => {
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
