use crate::assumed;
use crate::common::*;
use crate::formatter::Formatter;
use crate::generics;
use crate::get_mir::MirLevel;
use crate::id_vector::ToUsize;
use crate::meta;
use crate::names::type_def_id_to_name;
use crate::regions_hierarchy;
use crate::regions_hierarchy::TypesConstraintsMap;
use crate::reorder_decls::DeclarationGroup;
use crate::rust_to_local_ids::*;
use crate::translate_constants::translate_const_kind_as_const_generic;
use crate::translate_ctx::*;
use crate::types as ty;
use crate::types::ConstGeneric;
use crate::ullbc_ast as ast;
use core::convert::*;
use rustc_hir::def_id::DefId;
use rustc_middle::mir::Mutability;
use rustc_middle::ty::{Ty, TyCtxt, TyKind};
use rustc_session::Session;

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

/// Translate a Ty.
///
/// Typically used in this module to translate the fields of a structure/
/// enumeration definition, or later to translate the type of a variable.
///
/// Note that we take as parameter a function to translate regions, because
/// regions can be translated in several manners (non-erased region or erased
/// regions), in which case the return type is different.
pub(crate) fn translate_ty<'tcx, R>(
    bt_ctx: &BodyTransContext<'tcx, '_, '_>,
    region_translator: &dyn Fn(&rustc_middle::ty::RegionKind<'tcx>) -> R,
    ty: &Ty<'tcx>,
) -> Result<ty::Ty<R>>
where
    R: Clone + Eq,
{
    translate_ty_kind(bt_ctx, region_translator, ty.kind())
}

/// Translate a [TyKind].
///
/// See the comments for [translate_ty] (the two functions do the same thing,
/// they simply don't take the same input parameters).
pub(crate) fn translate_ty_kind<'tcx, R>(
    bt_ctx: &BodyTransContext<'tcx, '_, '_>,
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
                let name = type_def_id_to_name(bt_ctx.t_ctx.tcx, adt_did);
                assumed::type_to_used_params(&name)
            };

            // Translate the type parameters instantiation
            let (regions, params, cgs) =
                translate_substs(bt_ctx, region_translator, used_params, substs)?;

            // Retrieve the ADT identifier
            let def_id = translate_defid(bt_ctx, adt_did);

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

            let c = translate_const_kind_as_const_generic(bt_ctx, *const_param);
            let tys = vec![translate_ty(bt_ctx, region_translator, ty)?];
            let cgs = vec![c];
            let id = ty::TypeId::Assumed(ty::AssumedTy::Array);
            Ok(ty::Ty::Adt(id, Vec::new(), tys, cgs))
        }
        TyKind::Slice(ty) => {
            trace!("Slice");

            let tys = vec![translate_ty(bt_ctx, region_translator, ty)?];
            let id = ty::TypeId::Assumed(ty::AssumedTy::Slice);
            Ok(ty::Ty::Adt(id, Vec::new(), tys, Vec::new()))
        }
        TyKind::Ref(region, ty, mutability) => {
            trace!("Ref");

            let region = region_translator(region);
            let ty = translate_ty(bt_ctx, region_translator, ty)?;
            let kind = match *mutability {
                Mutability::Not => ty::RefKind::Shared,
                Mutability::Mut => ty::RefKind::Mut,
            };
            Ok(ty::Ty::Ref(region, Box::new(ty), kind))
        }
        TyKind::RawPtr(ty_and_mut) => {
            trace!("RawPtr: {:?}", ty_and_mut);
            let ty = translate_ty(bt_ctx, region_translator, &ty_and_mut.ty)?;
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
                let param_ty = translate_ty(bt_ctx, region_translator, &param)?;
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
            let ty = bt_ctx.type_vars_map.get(&param.index).unwrap();
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
pub(crate) fn translate_sig_ty<'tcx>(
    bt_ctx: &BodyTransContext<'tcx, '_, '_>,
    ty: &Ty<'tcx>,
) -> Result<ty::RTy> {
    translate_ty(
        bt_ctx,
        &|r| translate_non_erased_region(&bt_ctx.region_vars_map, *r),
        ty,
    )
}

/// Translate a type where the regions are erased
/// Simply calls [translate_ty]
pub(crate) fn translate_ety<'tcx>(
    bt_ctx: &BodyTransContext<'tcx, '_, '_>,
    ty: &Ty<'tcx>,
) -> Result<ty::ETy> {
    translate_ty(bt_ctx, &|r| translate_erased_region(*r), ty)
}

fn translate_substs<'tcx, R>(
    bt_ctx: &BodyTransContext<'tcx, '_, '_>,
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
                let param_ty = translate_ty(bt_ctx, region_translator, &param_ty)?;
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
fn translate_defid(bt_ctx: &BodyTransContext, def_id: DefId) -> ty::TypeId {
    trace!("{:?}", def_id);

    if def_id.is_local() {
        ty::TypeId::Adt(bt_ctx.get_type_decl_id_from_rid(def_id))
    } else {
        // Non-local: check if the type has primitive support

        // Retrieve the type name
        let name = type_def_id_to_name(bt_ctx.t_ctx.tcx, def_id);

        match assumed::get_type_id_from_name(&name) {
            Option::Some(id) => {
                // The type has primitive support
                ty::TypeId::Assumed(id)
            }
            Option::None => {
                // The type is external
                ty::TypeId::Adt(bt_ctx.get_type_decl_id_from_rid(def_id))
            }
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
fn translate_type_generics<'tcx, 'ctx, 'ctx1>(
    t_ctx: &'ctx TransContext<'tcx, 'ctx1>,
    def_id: DefId,
) -> (
    BodyTransContext<'tcx, 'ctx, 'ctx1>,
    rustc_middle::ty::subst::SubstsRef<'tcx>,
) {
    // Check the generics
    generics::check_type_generics(t_ctx.tcx, def_id);

    // Use a dummy substitution to instantiate the type parameters
    let substs = rustc_middle::ty::subst::InternalSubsts::identity_for_item(t_ctx.tcx, def_id);

    // Initialize the body translation context
    let mut bt_ctx = BodyTransContext::new(def_id, t_ctx);

    for p in substs.iter() {
        match p.unpack() {
            rustc_middle::ty::subst::GenericArgKind::Type(param_ty) => {
                // The type should be a Param:
                match param_ty.kind() {
                    rustc_middle::ty::TyKind::Param(param_ty) => {
                        let _ =
                            bt_ctx.push_type_var(param_ty.index, param_ty.name.to_ident_string());
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
                let ty = translate_ety(&bt_ctx, &c.ty()).unwrap();
                let ty = ty.to_literal();
                match c.kind() {
                    rustc_middle::ty::ConstKind::Param(cp) => {
                        let _ =
                            bt_ctx.push_const_generic_var(cp.index, ty, cp.name.to_ident_string());
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

/// Translate one local type definition which has not been flagged as opaque.
fn translate_transparent_type<'tcx>(
    sess: &Session,
    bt_ctx: &BodyTransContext<'tcx, '_, '_>,
    trans_id: ty::TypeDeclId::Id,
    substs: &rustc_middle::ty::subst::SubstsRef<'tcx>,
) -> Result<ty::TypeDeclKind> {
    trace!("{}", trans_id);

    // Retrieve the definition
    trace!("{:?}", bt_ctx.def_id);
    let adt = bt_ctx.t_ctx.tcx.adt_def(bt_ctx.def_id);

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

            let ty = field_def.ty(bt_ctx.t_ctx.tcx, substs);

            // Translate the field type
            let ty = translate_sig_ty(&bt_ctx, &ty)?;

            // Retrieve the field name.
            // Note that the only way to check if the user wrote the name or
            // if it is just an integer generated by rustc is by checking if
            // if is just made of numerals...
            let field_name = field_def.ident(bt_ctx.t_ctx.tcx).name.to_ident_string();
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
            let meta = meta::get_meta_from_rid(
                sess,
                bt_ctx.t_ctx.tcx,
                &bt_ctx.t_ctx.ordered.file_to_id,
                field_def.did,
            );

            // Store the field
            let field = ty::Field {
                meta,
                name: field_name.clone(),
                ty,
            };
            fields.push(field);

            field_id.incr();
        }

        let meta = meta::get_meta_from_rid(
            sess,
            bt_ctx.t_ctx.tcx,
            &bt_ctx.t_ctx.ordered.file_to_id,
            var_def.def_id,
        );
        let variant_name = var_def.ident(bt_ctx.t_ctx.tcx).name.to_ident_string();
        variants.push(ty::Variant {
            meta,
            name: variant_name,
            fields: ty::FieldId::Vector::from(fields),
        });

        var_id.incr();
    }

    // Register the type
    let type_def_kind: ty::TypeDeclKind = match adt.adt_kind() {
        rustc_middle::ty::AdtKind::Struct => ty::TypeDeclKind::Struct(variants[0].fields.clone()),
        rustc_middle::ty::AdtKind::Enum => {
            ty::TypeDeclKind::Enum(ty::VariantId::Vector::from(variants))
        }
        rustc_middle::ty::AdtKind::Union => {
            // Should have been filtered during the registration phase
            unreachable!();
        }
    };

    Ok(type_def_kind)
}

/// Translate a type definition.
///
/// Note that we translate the types one by one: we don't need to take into
/// account the fact that some types are mutually recursive at this point
/// (we will need to take that into account when generating the code in a file).
fn translate_type<'tcx>(
    sess: &Session,
    tcx: TyCtxt<'tcx>,
    decls: &OrderedDecls,
    type_defs: &mut ty::TypeDecls,
    fun_defs: &ast::FunDecls,
    global_defs: &ast::GlobalDecls,
    trans_id: ty::TypeDeclId::Id,
    mir_level: MirLevel,
) -> Result<()> {
    let info = decls.decls_info.get(&AnyDeclId::Type(trans_id)).unwrap();

    // Initialize the translation context
    let t_ctx = TransContext {
        sess,
        tcx,
        ordered: decls,
        type_defs,
        fun_defs,
        global_defs,
        mir_level,
    };

    // Check and translate the generics
    // TODO: use the body trans context as input, and don't return anything.
    let (bt_ctx, substs) = translate_type_generics(&t_ctx, info.rid);

    // Check if the type is opaque or external, and delegate the translation
    // of the "body" to the proper function
    let kind = if !info.is_local() || !info.is_transparent {
        // Opaque types are:
        // - external types
        // - local types flagged as opaque
        ty::TypeDeclKind::Opaque
    } else {
        translate_transparent_type(sess, &bt_ctx, trans_id, &substs)?
    };

    // Register the type
    let name = type_def_id_to_name(tcx, info.rid);
    let region_params = bt_ctx.region_vars.clone();
    let type_params = bt_ctx.type_vars.clone();
    let const_generic_params = bt_ctx.const_generic_vars.clone();

    // Translate the span information
    let meta = meta::get_meta_from_rid(sess, tcx, &decls.file_to_id, info.rid);

    let type_def = ty::TypeDecl {
        def_id: trans_id,
        meta,
        name,
        region_params,
        type_params,
        const_generic_params,
        kind,
        // For now, initialize the regions hierarchy with a dummy value:
        // we compute it later (after returning to [translate_types]
        regions_hierarchy: regions_hierarchy::RegionGroups::new(),
    };

    trace!("{} -> {}", trans_id.to_string(), type_def.to_string());
    // Small sanity check - we have to translate the definitions in the proper
    // order, otherwise we mess up with the vector of ids
    assert!(type_defs.len() == trans_id.to_usize());

    type_defs.push_back(type_def);
    Ok(())
}

/// Translate the types.
///
/// Note that in practice, we don't really need to know in which order we should
/// extract them (i.e.: the `Declarations` parameter is not really
/// necessary), because what is important is the file generation later.
/// Still, now that the order is computed, it's better to use it (leads to a
/// better indexing, for instance).
pub fn translate_types<'tcx>(
    sess: &Session,
    tcx: TyCtxt<'tcx>,
    decls: &OrderedDecls,
    mir_level: MirLevel,
) -> Result<(TypesConstraintsMap, ty::TypeDecls)> {
    trace!();

    let mut types_cover_regions = TypesConstraintsMap::new();
    let mut type_defs = ty::TypeDecls::new();

    // TODO: for now we initialize the global/funs maps as empty maps
    // This won't be an issue once we merge the contexts.
    let global_defs = ast::GlobalDeclId::Vector::new();
    let fun_defs = ast::FunDeclId::Vector::new();

    // Translate the types one by one
    for decl in &decls.decls {
        match decl {
            DeclarationGroup::Type(decl) => match decl {
                TypeDeclarationGroup::NonRec(id) => {
                    translate_type(
                        sess,
                        tcx,
                        decls,
                        &mut type_defs,
                        &fun_defs,
                        &global_defs,
                        *id,
                        mir_level,
                    )?;
                    regions_hierarchy::compute_regions_hierarchy_for_type_decl_group(
                        &mut types_cover_regions,
                        &mut type_defs,
                        decl,
                    );
                }
                TypeDeclarationGroup::Rec(ids) => {
                    for id in ids {
                        translate_type(
                            sess,
                            tcx,
                            decls,
                            &mut type_defs,
                            &fun_defs,
                            &global_defs,
                            *id,
                            mir_level,
                        )?;
                    }
                    regions_hierarchy::compute_regions_hierarchy_for_type_decl_group(
                        &mut types_cover_regions,
                        &mut type_defs,
                        decl,
                    );
                }
            },
            DeclarationGroup::Fun(_) | DeclarationGroup::Global(_) => {
                // Ignore the functions and constants
            }
        }
    }

    // Print the type constraints map
    trace!(
        "types constraints map:\n{}\n",
        regions_hierarchy::types_constraints_map_fmt_with_ctx(&types_cover_regions, &type_defs)
    );

    // Print the translated types
    for d in type_defs.iter() {
        let formatter = TypeDeclFormatter {
            type_defs: &type_defs,
            global_defs: &global_defs,
            region_params: &d.region_params,
            type_params: &d.type_params,
            const_generic_params: &d.const_generic_params,
        };
        trace!("translated type:\n{}\n", formatter.format_object(d));
    }

    Ok((types_cover_regions, type_defs))
}
