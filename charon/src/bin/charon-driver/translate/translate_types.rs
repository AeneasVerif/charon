use crate::translate::translate_traits::PredicateLocation;

use super::translate_ctx::*;
use charon_lib::ast::*;
use charon_lib::builtins;
use charon_lib::common::hash_by_addr::HashByAddr;
use charon_lib::ids::Vector;
use core::convert::*;
use hax::Visibility;
use hax_frontend_exporter as hax;

/// Small helper: we ignore some region names (when they are equal to "'_")
fn check_region_name(s: String) -> Option<String> {
    if s == "'_" {
        None
    } else {
        Some(s)
    }
}

pub fn translate_bound_region_kind_name(kind: &hax::BoundRegionKind) -> Option<String> {
    use hax::BoundRegionKind::*;
    let s = match kind {
        BrAnon => None,
        BrNamed(_, symbol) => Some(symbol.clone()),
        BrEnv => Some("@env".to_owned()),
    };
    s.and_then(check_region_name)
}

pub fn translate_region_name(region: &hax::EarlyParamRegion) -> Option<String> {
    let s = region.name.clone();
    check_region_name(s)
}

impl<'tcx, 'ctx> BodyTransCtx<'tcx, 'ctx> {
    // Translate a region
    pub(crate) fn translate_region(
        &mut self,
        span: Span,
        region: &hax::Region,
    ) -> Result<Region, Error> {
        use hax::RegionKind::*;
        match &region.kind {
            ReErased => Ok(Region::Erased),
            ReStatic => Ok(Region::Static),
            ReBound(id, br) => {
                let var = self.lookup_bound_region(span, *id, br.var)?;
                Ok(Region::Var(var))
            }
            ReEarlyParam(region) => {
                let var = self.lookup_early_region(span, region)?;
                Ok(Region::Var(var))
            }
            ReVar(..) | RePlaceholder(..) => {
                // Shouldn't exist outside of type inference.
                let err = format!("Should not exist outside of type inference: {region:?}");
                error_or_panic!(self, span, err)
            }
            ReLateParam(..) | ReError(..) => {
                let err = format!("Unexpected region kind: {region:?}");
                error_or_panic!(self, span, err)
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
    #[tracing::instrument(skip(self, span))]
    pub(crate) fn translate_ty(&mut self, span: Span, ty: &hax::Ty) -> Result<Ty, Error> {
        trace!("{:?}", ty);
        let cache_key = HashByAddr(ty.inner().clone());
        if let Some(ty) = self.lookup_cached_type(&cache_key) {
            return Ok(ty.clone());
        }

        let kind = match ty.kind() {
            hax::TyKind::Bool => TyKind::Literal(LiteralTy::Bool),
            hax::TyKind::Char => TyKind::Literal(LiteralTy::Char),
            hax::TyKind::Int(int_ty) => {
                use hax::IntTy;
                TyKind::Literal(LiteralTy::Integer(match int_ty {
                    IntTy::Isize => IntegerTy::Isize,
                    IntTy::I8 => IntegerTy::I8,
                    IntTy::I16 => IntegerTy::I16,
                    IntTy::I32 => IntegerTy::I32,
                    IntTy::I64 => IntegerTy::I64,
                    IntTy::I128 => IntegerTy::I128,
                }))
            }
            hax::TyKind::Uint(int_ty) => {
                use hax::UintTy;
                TyKind::Literal(LiteralTy::Integer(match int_ty {
                    UintTy::Usize => IntegerTy::Usize,
                    UintTy::U8 => IntegerTy::U8,
                    UintTy::U16 => IntegerTy::U16,
                    UintTy::U32 => IntegerTy::U32,
                    UintTy::U64 => IntegerTy::U64,
                    UintTy::U128 => IntegerTy::U128,
                }))
            }
            hax::TyKind::Float(float_ty) => {
                use hax::FloatTy;
                TyKind::Literal(LiteralTy::Float(match float_ty {
                    FloatTy::F16 => charon_lib::ast::types::FloatTy::F16,
                    FloatTy::F32 => charon_lib::ast::types::FloatTy::F32,
                    FloatTy::F64 => charon_lib::ast::types::FloatTy::F64,
                    FloatTy::F128 => charon_lib::ast::types::FloatTy::F128,
                }))
            }
            hax::TyKind::Never => TyKind::Never,

            hax::TyKind::Alias(alias) => match &alias.kind {
                hax::AliasKind::Projection {
                    impl_expr,
                    assoc_item,
                } => {
                    let trait_ref = self.translate_trait_impl_expr(span, impl_expr)?;
                    let name = TraitItemName(assoc_item.name.clone());
                    TyKind::TraitType(trait_ref, name)
                }
                hax::AliasKind::Opaque { hidden_ty, .. } => {
                    return self.translate_ty(span, hidden_ty)
                }
                _ => {
                    error_or_panic!(
                        self,
                        span,
                        format!("Unsupported alias type: {:?}", alias.kind)
                    )
                }
            },

            hax::TyKind::Adt {
                generic_args: substs,
                trait_refs,
                def_id,
            } => {
                trace!("Adt: {:?}", def_id);

                // Retrieve the type identifier
                let type_id = self.translate_type_id(span, def_id)?;

                // Translate the type parameters instantiation
                let mut generics = self.translate_generic_args(
                    span,
                    substs,
                    trait_refs,
                    None,
                    type_id.generics_target(),
                )?;

                // Filter the type arguments.
                // TODO: do this in a micro-pass
                if let TypeId::Builtin(builtin_ty) = type_id {
                    let used_args = builtins::type_to_used_params(builtin_ty);
                    error_assert!(self, span, generics.types.len() == used_args.len());
                    let types = std::mem::take(&mut generics.types)
                        .into_iter()
                        .zip(used_args)
                        .filter(|(_, used)| *used)
                        .map(|(ty, _)| ty)
                        .collect();
                    generics.types = types;
                }

                // Return the instantiated ADT
                TyKind::Adt(type_id, generics)
            }
            hax::TyKind::Str => {
                trace!("Str");

                let id = TypeId::Builtin(BuiltinTy::Str);
                TyKind::Adt(id, GenericArgs::empty(GenericsSource::Builtin))
            }
            hax::TyKind::Array(ty, const_param) => {
                trace!("Array");

                let c = self.translate_constant_expr_to_const_generic(span, const_param)?;
                let tys = vec![self.translate_ty(span, ty)?].into();
                let cgs = vec![c].into();
                let id = TypeId::Builtin(BuiltinTy::Array);
                TyKind::Adt(
                    id,
                    GenericArgs::new(
                        Vector::new(),
                        tys,
                        cgs,
                        Vector::new(),
                        GenericsSource::Builtin,
                    ),
                )
            }
            hax::TyKind::Slice(ty) => {
                trace!("Slice");

                let tys = vec![self.translate_ty(span, ty)?].into();
                let id = TypeId::Builtin(BuiltinTy::Slice);
                TyKind::Adt(id, GenericArgs::new_for_builtin(tys))
            }
            hax::TyKind::Ref(region, ty, mutability) => {
                trace!("Ref");

                let region = self.translate_region(span, region)?;
                let ty = self.translate_ty(span, ty)?;
                let kind = if *mutability {
                    RefKind::Mut
                } else {
                    RefKind::Shared
                };
                TyKind::Ref(region, ty, kind)
            }
            hax::TyKind::RawPtr(ty, mutbl) => {
                trace!("RawPtr: {:?}", (ty, mutbl));
                let ty = self.translate_ty(span, ty)?;
                let kind = if *mutbl {
                    RefKind::Mut
                } else {
                    RefKind::Shared
                };
                TyKind::RawPtr(ty, kind)
            }
            hax::TyKind::Tuple(substs) => {
                trace!("Tuple");

                let mut params = Vector::new();
                for param in substs.iter() {
                    let param_ty = self.translate_ty(span, param)?;
                    params.push(param_ty);
                }

                TyKind::Adt(TypeId::Tuple, GenericArgs::new_for_builtin(params))
            }

            hax::TyKind::Param(param) => {
                // A type parameter, for example `T` in `fn f<T>(x : T) {}`.
                // Note that this type parameter may actually have been
                // instantiated (in our environment, we may map it to another
                // type): we just have to look it up.
                // Note that if we are using this function to translate a field
                // type in a type definition, it should actually map to a type
                // parameter.
                trace!("Param");

                // Retrieve the translation of the substituted type:
                let var = self.lookup_type_var(span, param)?;
                TyKind::TypeVar(var)
            }

            hax::TyKind::Foreign(def_id) => {
                trace!("Foreign");
                let adt_id = self.translate_type_id(span, def_id)?;
                TyKind::Adt(adt_id, GenericArgs::empty(adt_id.generics_target()))
            }
            hax::TyKind::Infer(_) => {
                trace!("Infer");
                error_or_panic!(self, span, "Unsupported type: infer type")
            }

            hax::TyKind::Dynamic(_existential_preds, _region, _) => {
                // TODO: we don't translate the predicates yet because our machinery can't handle
                // it.
                trace!("Dynamic");
                TyKind::DynTrait(ExistentialPredicate)
            }

            hax::TyKind::Coroutine(..) => {
                trace!("Coroutine");
                error_or_panic!(self, span, "Coroutine types are not supported yet")
            }

            hax::TyKind::Bound(_, _) => {
                trace!("Bound");
                error_or_panic!(self, span, "Unexpected type kind: bound")
            }
            hax::TyKind::Placeholder(_) => {
                trace!("PlaceHolder");
                error_or_panic!(self, span, "Unsupported type: placeholder")
            }
            hax::TyKind::Arrow(box sig)
            | hax::TyKind::Closure(
                _,
                hax::ClosureArgs {
                    untupled_sig: sig, ..
                },
            ) => {
                trace!("Arrow");
                trace!("bound vars: {:?}", sig.bound_vars);
                let sig = self.translate_region_binder(span, sig, |ctx, sig| {
                    let inputs = sig
                        .inputs
                        .iter()
                        .map(|x| ctx.translate_ty(span, x))
                        .try_collect()?;
                    let output = ctx.translate_ty(span, &sig.output)?;
                    Ok((inputs, output))
                })?;
                TyKind::Arrow(sig)
            }
            hax::TyKind::Error => {
                trace!("Error");
                error_or_panic!(self, span, "Type checking error")
            }
            hax::TyKind::Todo(s) => {
                trace!("Todo: {s}");
                error_or_panic!(self, span, format!("Unsupported type: {:?}", s))
            }
        };
        let ty = kind.into_ty();
        self.innermost_binder_mut()
            .type_trans_cache
            .insert(cache_key, ty.clone());
        Ok(ty)
    }

    pub fn translate_generic_args(
        &mut self,
        span: Span,
        substs: &[hax::GenericArg],
        trait_refs: &[hax::ImplExpr],
        late_bound: Option<hax::Binder<()>>,
        target: GenericsSource,
    ) -> Result<GenericArgs, Error> {
        use hax::GenericArg::*;
        trace!("{:?}", substs);

        let mut regions = Vector::new();
        let mut types = Vector::new();
        let mut const_generics = Vector::new();
        for param in substs {
            match param {
                Type(param_ty) => {
                    types.push(self.translate_ty(span, param_ty)?);
                }
                Lifetime(region) => {
                    regions.push(self.translate_region(span, region)?);
                }
                Const(c) => {
                    const_generics.push(self.translate_constant_expr_to_const_generic(span, c)?);
                }
            }
        }
        // Add the late-bounds lifetimes if any.
        if let Some(binder) = late_bound {
            for v in &binder.bound_vars {
                match v {
                    hax::BoundVariableKind::Region(_) => {
                        regions.push(Region::Erased);
                    }
                    hax::BoundVariableKind::Ty(_) => {
                        error_or_panic!(self, span, "Unexpected locally bound type variable")
                    }
                    hax::BoundVariableKind::Const => {
                        error_or_panic!(self, span, "Unexpected locally bound const generic")
                    }
                }
            }
        }
        let trait_refs = self.translate_trait_impl_exprs(span, trait_refs)?;

        Ok(GenericArgs {
            regions,
            types,
            const_generics,
            trait_refs,
            target,
        })
    }

    /// Checks whether the given id corresponds to a built-in type.
    fn recognize_builtin_type(&mut self, def_id: &hax::DefId) -> Result<Option<BuiltinTy>, Error> {
        let def = self.t_ctx.hax_def(def_id)?;
        let ty = if def.lang_item.as_deref() == Some("owned_box") {
            Some(BuiltinTy::Box)
        } else {
            None
        };
        Ok(ty)
    }

    /// Translate a type def id
    pub(crate) fn translate_type_id(
        &mut self,
        span: Span,
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
        def_span: Span,
        item_meta: &ItemMeta,
        adt: &hax::AdtDef,
    ) -> Result<TypeDeclKind, Error> {
        use hax::AdtKind;

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
                let field_span = self.t_ctx.translate_span_from_hax(&field_def.span);
                // Translate the field type
                let ty = self.translate_ty(field_span, &field_def.ty)?;
                let field_full_def = self.t_ctx.hax_def(&field_def.did)?;
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
                        error_assert!(self, field_span, *b == field_name.is_some());
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
            let variant_span = self.t_ctx.translate_span_from_hax(&var_def.span);
            let variant_name = var_def.name.clone();
            let variant_full_def = self.t_ctx.hax_def(&var_def.def_id)?;
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
        def_span: Span,
        discr: &hax::DiscriminantValue,
    ) -> Result<ScalarValue, Error> {
        let ty = self.translate_ty(def_span, &discr.ty)?;
        let int_ty = *ty.kind().as_literal().unwrap().as_integer().unwrap();
        Ok(ScalarValue::from_bits(int_ty, discr.val))
    }

    /// Translate the generics and predicates of this item and its parents.
    pub(crate) fn translate_def_generics(
        &mut self,
        span: Span,
        def: &hax::FullDef,
    ) -> Result<(), Error> {
        assert!(self.binding_levels.len() == 0);
        self.binding_levels.push_front(BindingLevel::new(true));
        self.push_generics_for_def(span, def, false)?;
        self.innermost_binder_mut().params.check_consistency();
        Ok(())
    }

    /// Translate the generics and predicates of this item without its parents.
    pub(crate) fn translate_def_generics_without_parents(
        &mut self,
        span: Span,
        def: &hax::FullDef,
    ) -> Result<(), Error> {
        self.binding_levels.push_front(BindingLevel::new(true));
        self.push_generics_for_def_without_parents(span, def, true, true)?;
        self.innermost_binder().params.check_consistency();
        Ok(())
    }

    pub(crate) fn into_generics(mut self) -> GenericParams {
        assert!(self.binding_levels.len() == 1);
        self.binding_levels.pop_back().unwrap().params
    }

    /// Add the generics and predicates of this item and its parents to the current context.
    fn push_generics_for_def(
        &mut self,
        span: Span,
        def: &hax::FullDef,
        is_parent: bool,
    ) -> Result<(), Error> {
        use hax::FullDefKind;
        // Add generics from the parent item, recursively (recursivity is important for closures,
        // as they could be nested).
        match &def.kind {
            FullDefKind::AssocTy { .. }
            | FullDefKind::AssocFn { .. }
            | FullDefKind::AssocConst { .. }
            | FullDefKind::Closure { .. }
            | FullDefKind::Ctor { .. }
            | FullDefKind::Variant { .. } => {
                let parent_def_id = def.parent.as_ref().unwrap();
                let parent_def = self.t_ctx.hax_def(parent_def_id)?;
                self.push_generics_for_def(span, &parent_def, true)?;
            }
            _ => {}
        }
        self.push_generics_for_def_without_parents(span, def, !is_parent, !is_parent)?;
        Ok(())
    }

    /// Add the generics and predicates of this item. This does not include the parent generics;
    /// use `push_generics_for_def` to get the full list.
    fn push_generics_for_def_without_parents(
        &mut self,
        span: Span,
        def: &hax::FullDef,
        include_late_bound: bool,
        include_assoc_ty_clauses: bool,
    ) -> Result<(), Error> {
        use hax::FullDefKind;
        if let Some((generics, predicates)) = def.generics() {
            // Add the generic params.
            self.push_generic_params(generics)?;
            // Add the self trait clause.
            match &def.kind {
                FullDefKind::TraitImpl {
                    trait_pred: self_predicate,
                    ..
                }
                | FullDefKind::Trait { self_predicate, .. } => {
                    self.register_trait_decl_id(span, &self_predicate.trait_ref.def_id);
                    let _ = self.translate_trait_predicate(span, self_predicate)?;
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
                FullDefKind::TraitImpl { .. } | FullDefKind::InherentImpl { .. } => {
                    (PredicateOrigin::WhereClauseOnImpl, PredicateLocation::Base)
                }
                // TODO: distinguish trait where clauses from trait supertraits. Currently we
                // consider them all as parent clauses.
                FullDefKind::Trait { .. } => {
                    let _ = self.register_trait_decl_id(span, &def.def_id);
                    (
                        PredicateOrigin::WhereClauseOnTrait,
                        PredicateLocation::Parent,
                    )
                }
                _ => panic!("Unexpected def: {def:?}"),
            };
            self.register_predicates(predicates, origin, &location)?;

            if let hax::FullDefKind::Trait { items, .. } = &def.kind
                && include_assoc_ty_clauses
            {
                // Also add the predicates on associated types.
                // FIXME(gat): don't skip GATs.
                for (item, item_def) in items {
                    if let hax::FullDefKind::AssocTy {
                        generics,
                        predicates,
                        ..
                    } = &item_def.kind
                        && generics.params.is_empty()
                    {
                        let name = TraitItemName(item.name.clone());
                        self.register_predicates(
                            &predicates,
                            PredicateOrigin::TraitItem(name.clone()),
                            &PredicateLocation::Item(name),
                        )?;
                    }
                }
            }
        }

        // The parameters (and in particular the lifetimes) are split between
        // early bound and late bound parameters. See those blog posts for explanations:
        // https://smallcultfollowing.com/babysteps/blog/2013/10/29/intermingled-parameter-lists/
        // https://smallcultfollowing.com/babysteps/blog/2013/11/04/intermingled-parameter-lists/
        // Note that only lifetimes can be late bound.
        //
        // [TyCtxt.generics_of] gives us the early-bound parameters. We add the late-bound
        // parameters here.
        let signature = match &def.kind {
            hax::FullDefKind::Closure { args, .. } => Some(&args.tupled_sig),
            hax::FullDefKind::Fn { sig, .. } => Some(sig),
            hax::FullDefKind::AssocFn { sig, .. } => Some(sig),
            _ => None,
        };
        if let Some(signature) = signature
            && include_late_bound
        {
            let innermost_binder = self.innermost_binder_mut();
            assert!(innermost_binder.bound_region_vars.is_empty());
            innermost_binder.push_params_from_binder(signature.rebind(()))?;
        }

        Ok(())
    }

    pub(crate) fn push_generic_params(&mut self, generics: &hax::TyGenerics) -> Result<(), Error> {
        for param in &generics.params {
            self.push_generic_param(param)?;
        }
        Ok(())
    }

    pub(crate) fn push_generic_param(&mut self, param: &hax::GenericParamDef) -> Result<(), Error> {
        match &param.kind {
            hax::GenericParamDefKind::Lifetime => {
                let region = hax::EarlyParamRegion {
                    index: param.index,
                    name: param.name.clone(),
                };
                let _ = self.innermost_binder_mut().push_early_region(region);
            }
            hax::GenericParamDefKind::Type { .. } => {
                let _ = self
                    .innermost_binder_mut()
                    .push_type_var(param.index, param.name.clone());
            }
            hax::GenericParamDefKind::Const { ty, .. } => {
                let span = self.def_span(&param.def_id);
                // The type should be primitive, meaning it shouldn't contain variables,
                // non-primitive adts, etc. As a result, we can use an empty context.
                let ty = self.translate_ty(span, ty)?;
                match ty.kind().as_literal() {
                    Some(ty) => self.innermost_binder_mut().push_const_generic_var(
                        param.index,
                        *ty,
                        param.name.clone(),
                    ),
                    None => error_or_panic!(
                        self,
                        span,
                        "Constant parameters of non-literal type are not supported"
                    ),
                }
            }
        }

        Ok(())
    }
}

impl BodyTransCtx<'_, '_> {
    /// Translate a type definition.
    ///
    /// Note that we translate the types one by one: we don't need to take into
    /// account the fact that some types are mutually recursive at this point
    /// (we will need to take that into account when generating the code in a file).
    #[tracing::instrument(skip(self, item_meta))]
    pub fn translate_type(
        mut self,
        trans_id: TypeDeclId,
        item_meta: ItemMeta,
        def: &hax::FullDef,
    ) -> Result<TypeDecl, Error> {
        let span = item_meta.span;

        // Translate generics and predicates
        self.translate_def_generics(span, def)?;

        // Translate type body
        let kind = match &def.kind {
            _ if item_meta.opacity.is_opaque() => Ok(TypeDeclKind::Opaque),
            hax::FullDefKind::OpaqueTy | hax::FullDefKind::ForeignTy => Ok(TypeDeclKind::Opaque),
            hax::FullDefKind::TyAlias { ty, .. } => {
                // Don't error on missing trait refs.
                self.error_on_impl_expr_error = false;
                // We only translate crate-local type aliases so the `unwrap` is ok.
                let ty = ty.as_ref().unwrap();
                self.translate_ty(span, ty).map(TypeDeclKind::Alias)
            }
            hax::FullDefKind::Struct { def, .. }
            | hax::FullDefKind::Enum { def, .. }
            | hax::FullDefKind::Union { def, .. } => {
                self.translate_adt_def(trans_id, span, &item_meta, def)
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
            generics: self.into_generics(),
            kind,
        };

        Ok(type_def)
    }
}
