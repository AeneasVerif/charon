use crate::assumed;
use crate::common::*;
use crate::formatter::*;
use crate::gast::*;
use crate::names_utils::{def_id_to_name, extended_def_id_to_name};
use crate::regions_hierarchy::RegionGroups;
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

/// We need this to easily switch between translation of [ETy] and [RTy].
///
/// TODO: actually, we should have only one [Ty] type, because it is possible
/// to mix erased and non-erased regions. For instance, if we instantiate
/// a type parameter with a type containing regions, those regions will not
/// be erased at call site.
pub(crate) trait TyTranslator<R> {
    /// Necessary to translate trait refs: if the trait ref is a parameter,
    /// we need to find the relavant clause. Trait clauses use [RTy], while
    /// the trait ref may use either [ETy] or [RTy], which means we need to
    /// convert the trait clause types.
    fn convert_rty(&self, ty: &RTy) -> Ty<R>;

    /// Necessary to register unsolved trait obligations
    fn convert_to_rty(&self, ty: &Ty<R>) -> RTy;

    /// Necessary to register unsolved trait obligations
    fn convert_to_rtrait_ref(&self, t: &TraitRef<R>) -> RTraitRef;

    fn translate_region(&self, region: &hax::Region) -> R;
}

impl<'tcx, 'ctx, 'ctx1> TyTranslator<ErasedRegion> for BodyTransCtx<'tcx, 'ctx, 'ctx1> {
    fn convert_rty(&self, ty: &RTy) -> ETy {
        ty.erase_regions()
    }

    fn convert_to_rty(&self, ty: &ETy) -> RTy {
        ty.substitute(
            &|_| unreachable!("Unexpected region"),
            &|tid| Ty::TypeVar(*tid),
            &|cgid| ConstGeneric::Var(*cgid),
        )
    }

    fn convert_to_rtrait_ref(&self, t: &ETraitRef) -> RTraitRef {
        t.substitute(
            &|_| unreachable!("Unexpected region"),
            &|tid| Ty::TypeVar(*tid),
            &|cgid| ConstGeneric::Var(*cgid),
        )
    }

    /// Translate a region which is expected to be erased.
    ///
    /// The regions are expected to be erased inside the function bodies (i.e.:
    /// we believe MIR uses regions only in the function signatures).
    fn translate_region(&self, region: &hax::Region) -> ErasedRegion {
        match region.kind {
            hax::RegionKind::ReErased => ErasedRegion::Erased,
            _ => {
                // Actually, not all regions are erased. My understanding is that the early
                // bound regions are erased, but when a region appears in a type it is
                // not. We need to update that.
                unreachable!()
            }
        }
    }
}

impl<'tcx, 'ctx, 'ctx1> TyTranslator<Region<RegionVarId::Id>> for BodyTransCtx<'tcx, 'ctx, 'ctx1> {
    fn convert_rty(&self, ty: &RTy) -> RTy {
        ty.clone()
    }

    fn convert_to_rty(&self, ty: &RTy) -> RTy {
        ty.clone()
    }

    fn convert_to_rtrait_ref(&self, t: &RTraitRef) -> RTraitRef {
        t.clone()
    }

    fn translate_region(&self, region: &hax::Region) -> Region<RegionVarId::Id> {
        match &region.kind {
            hax::RegionKind::ReErased => unreachable!(),
            hax::RegionKind::ReStatic => Region::Static,
            hax::RegionKind::ReLateBound(id, br) => {
                // See the comments in [BodyTransCtx.bound_vars]:
                // - the De Bruijn index identifies the group of variables
                // - the var id identifies the variable inside the group
                let rid = self.bound_vars.get(*id).unwrap().get(br.var).unwrap();
                Region::Var(*rid)
            }
            _ => {
                // For the other regions, we use the regions map
                let rid = self.region_vars_map.get(region).unwrap();
                Region::Var(rid)
            }
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
    pub(crate) fn translate_ty<R>(&mut self, ty: &hax::Ty) -> Result<Ty<R>>
    where
        R: Clone + Eq,
        Self: TyTranslator<R> + for<'a> Formatter<&'a R>,
    {
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
                unimplemented!();
            }
            hax::Ty::Never => Ok(Ty::Never),

            hax::Ty::Alias(alias_kind) => match alias_kind {
                hax::AliasKind::Projection {
                    impl_source,
                    substs,
                    name,
                } => {
                    let trait_ref = self.translate_trait_impl_source(impl_source);
                    // This should succeed because no marker trait (that we may
                    // ignore) has associated types.
                    let trait_ref = trait_ref.unwrap();
                    let (regions, types, const_generics) =
                        self.translate_substs(None, substs).unwrap();
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
                    unimplemented!("{:?}", ty)
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
                    let name = def_id_to_name(self.t_ctx.tcx, def_id);
                    assumed::type_to_used_params(&name)
                };

                // Translate the type parameters instantiation
                let generics =
                    self.translate_substs_and_trait_refs(used_params, substs, trait_refs)?;

                // Retrieve the ADT identifier
                let def_id = self.translate_type_id(def_id);

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

                let c = self.translate_constant_expr_to_const_generic(const_param);
                let tys = vec![self.translate_ty(ty)?];
                let cgs = vec![c];
                let id = TypeId::Assumed(AssumedTy::Array);
                Ok(Ty::Adt(
                    id,
                    GenericArgs::new(Vec::new(), tys, cgs, Vec::new()),
                ))
            }
            hax::Ty::Slice(ty) => {
                trace!("Slice");

                let tys = vec![self.translate_ty(ty)?];
                let id = TypeId::Assumed(AssumedTy::Slice);
                Ok(Ty::Adt(id, GenericArgs::new_from_types(tys)))
            }
            hax::Ty::Ref(region, ty, mutability) => {
                trace!("Ref");

                let region = self.translate_region(region);
                let ty = self.translate_ty(ty)?;
                let kind = if *mutability {
                    RefKind::Mut
                } else {
                    RefKind::Shared
                };
                Ok(Ty::Ref(region, Box::new(ty), kind))
            }
            hax::Ty::RawPtr(ty_and_mut) => {
                trace!("RawPtr: {:?}", ty_and_mut);
                let ty = self.translate_ty(&ty_and_mut.ty)?;
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
                    let param_ty = self.translate_ty(param)?;
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
                let var_id = self.type_vars_map.get(&param.index).unwrap();
                let ty = Ty::TypeVar(var_id);

                Ok(ty)
            }

            hax::Ty::Foreign(_) => {
                trace!("Foreign");
                unimplemented!();
            }
            hax::Ty::Infer(_) => {
                trace!("Infer");
                unimplemented!();
            }

            hax::Ty::Dynamic(_, _, _) => {
                trace!("Dynamic");
                unimplemented!();
            }

            hax::Ty::Generator(_, _, _) => {
                trace!("Generator");
                unimplemented!();
            }

            hax::Ty::Bound(_, _) => {
                trace!("Bound");
                unimplemented!();
            }
            hax::Ty::Placeholder(_) => {
                trace!("PlaceHolder");
                unimplemented!();
            }
            hax::Ty::Arrow(box sig) => {
                trace!("Arrow");
                assert!(sig.bound_vars.is_empty());
                let inputs = sig
                    .value
                    .inputs
                    .iter()
                    .map(|x| self.translate_ty(x).unwrap())
                    .collect();
                let output = self.translate_ty(&sig.value.output).unwrap();
                Ok(Ty::Arrow(inputs, Box::new(output)))
            }
            hax::Ty::Error => {
                trace!("Error");
                unimplemented!();
            }
            hax::Ty::Todo(s) => {
                trace!("Todo: {s}");
                unimplemented!();
            }
        }
    }

    /// Translate a signature type, where the regions are not erased and use region
    /// variable ids.
    /// Simply calls [`translate_ty`](translate_ty)
    pub(crate) fn translate_sig_ty(&mut self, ty: &hax::Ty) -> Result<RTy> {
        self.translate_ty(ty)
    }

    /// Translate a type where the regions are erased
    /// Simply calls [translate_ty]
    pub(crate) fn translate_ety(&mut self, ty: &hax::Ty) -> Result<ETy> {
        self.translate_ty(ty)
    }

    pub fn translate_substs<R>(
        &mut self,
        used_params: Option<Vec<bool>>,
        substs: &Vec<hax::GenericArg>,
    ) -> Result<(Vec<R>, Vec<Ty<R>>, Vec<ConstGeneric>)>
    where
        R: Clone + Eq,
        Self: TyTranslator<R> + for<'a> Formatter<&'a R>,
    {
        trace!("{:?}", substs);
        // Filter the parameters
        let substs: Vec<&hax::GenericArg> = match used_params {
            Option::None => substs.iter().collect(),
            Option::Some(used_args) => {
                assert!(substs.len() == used_args.len());
                substs
                    .iter()
                    .zip(used_args.into_iter())
                    .filter_map(|(param, used)| if used { Some(param) } else { None })
                    .collect()
            }
        };

        let mut regions: Vec<R> = vec![];
        let mut params = vec![];
        let mut cgs = vec![];
        for param in substs.iter() {
            match param {
                hax::GenericArg::Type(param_ty) => {
                    let param_ty = self.translate_ty(&param_ty)?;
                    params.push(param_ty);
                }
                hax::GenericArg::Lifetime(region) => {
                    regions.push(self.translate_region(&region));
                }
                hax::GenericArg::Const(c) => {
                    cgs.push(self.translate_constant_expr_to_const_generic(c));
                }
            }
        }

        Ok((regions, params, cgs))
    }

    pub fn translate_substs_and_trait_refs<R>(
        &mut self,
        used_params: Option<Vec<bool>>,
        substs: &Vec<hax::GenericArg>,
        trait_refs: &Vec<hax::ImplSource>,
    ) -> Result<GenericArgs<R>>
    where
        R: Clone + Eq,
        Self: TyTranslator<R> + for<'a> Formatter<&'a R>,
    {
        let (regions, types, const_generics) = self.translate_substs(used_params, substs)?;
        let trait_refs = self.translate_trait_impl_sources(trait_refs);
        Ok(GenericArgs {
            regions,
            types,
            const_generics,
            trait_refs,
        })
    }

    /// Translate a type def id
    pub(crate) fn translate_type_id(&mut self, def_id: &hax::DefId) -> TypeId {
        trace!("{:?}", def_id);

        let rust_id = def_id.rust_def_id.unwrap();
        if rust_id.is_local() {
            TypeId::Adt(self.translate_type_decl_id(rust_id))
        } else {
            // Non-local: check if the type has primitive support

            // Retrieve the type name
            let name = def_id_to_name(self.t_ctx.tcx, def_id);

            match assumed::get_type_id_from_name(&name) {
                Option::Some(id) => {
                    // The type has primitive support
                    TypeId::Assumed(id)
                }
                Option::None => {
                    // The type is external
                    TypeId::Adt(self.translate_type_decl_id(rust_id))
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
    ) -> TypeDeclKind {
        trace!("{}", trans_id);

        // In case the type is external, check if we should consider the type as
        // transparent (i.e., extract its body). If it is an enumeration, then yes
        // (because the variants of public enumerations are public, together with their
        // fields). If it is a structure, we check if all the fields are public.
        let is_transparent = is_local
            || match &adt.adt_kind {
                hax::AdtKind::Enum => true,
                hax::AdtKind::Struct => {
                    // Check the unique variant
                    assert!(adt.variants.raw.len() == 1);
                    adt.variants.raw[0]
                        .fields
                        .iter()
                        .all(|f| matches!(f.vis, hax::Visibility::Public))
                }
                hax::AdtKind::Union => unimplemented!(),
            };

        if !is_transparent {
            return TypeDeclKind::Opaque;
        }

        // The type is transparent: explore the variants
        let mut var_id = VariantId::Id::new(0); // Variant index
        let mut variants: Vec<Variant> = vec![];
        for var_def in adt.variants.raw {
            trace!("variant {}: {:?}", var_id, var_def);

            let mut fields: Vec<Field> = vec![];
            let mut field_id = FieldId::Id::new(0);
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
                unimplemented!();
            }
        };

        type_def_kind
    }

    /// Sanity check: region names are pairwise distinct (this caused trouble
    /// when generating names for the backward functions in Aeneas): at some
    /// point, Rustc introduced names equal to `Some("'_")` for the anonymous
    /// regions, instead of using `None` (we now check in [translate_region_name]
    /// and ignore names equal to "'_").
    pub(crate) fn check_generics(&self) {
        let mut s = std::collections::HashSet::new();
        for r in &self.region_vars {
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
    pub(crate) fn translate_generic_params(&mut self, def_id: DefId) {
        let tcx = self.t_ctx.tcx;

        // We could use: TyCtxt::generics_of(DefId)
        // But using the identity substitution is simpler. For instance, we can
        // easily retrieve the type for the const parameters.
        let substs = rustc_middle::ty::subst::InternalSubsts::identity_for_item(tcx, def_id)
            .sinto(&self.hax_state);

        for p in &substs {
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
                    let _ = self.push_region(region.clone(), name);
                }
                Const(c) => {
                    // The type should be primitive, meaning it shouldn't contain variables,
                    // non-primitive adts, etc. As a result, we can use an empty context.
                    let ty = self.translate_ety(&c.ty).unwrap();
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
    }
}

impl<'tcx, 'ctx> TransCtx<'tcx, 'ctx> {
    /// Translate a type definition.
    ///
    /// Note that we translate the types one by one: we don't need to take into
    /// account the fact that some types are mutually recursive at this point
    /// (we will need to take that into account when generating the code in a file).
    pub(crate) fn translate_type(&mut self, rust_id: DefId) {
        let trans_id = self.translate_type_decl_id(rust_id);
        let is_transparent = self.id_is_transparent(rust_id);

        let mut bt_ctx = BodyTransCtx::new(rust_id, self);

        // Check and translate the generics
        // TODO: use the body trans context as input, and don't return anything.
        bt_ctx.translate_generic_params(rust_id);

        // Translate the predicates
        bt_ctx.translate_predicates_solve_trait_obligations_of(None, rust_id);

        // Check if the type has been explicitely marked as opaque.
        // If yes, ignore it, otherwise, dive into the body. Note that for
        // external types we have to check the body: if the body is
        // public, we translate it, otherwise we consider the type as opaque.
        let is_local = rust_id.is_local();
        let kind = if !is_transparent {
            TypeDeclKind::Opaque
        } else {
            let adt = bt_ctx.t_ctx.tcx.adt_def(rust_id).sinto(&bt_ctx.hax_state);
            bt_ctx.translate_type_body(is_local, trans_id, adt)
        };

        // Register the type
        let name = extended_def_id_to_name(&rust_id.sinto(&bt_ctx.hax_state));
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
            // Dummy value for now: we compute this later
            regions_hierarchy: RegionGroups::new(),
        };

        trace!("{} -> {}", trans_id.to_string(), type_def.to_string());

        self.type_defs.insert(trans_id, type_def);
    }
}
