use crate::common::*;
use crate::formatter::Formatter;
use crate::reorder_decls::Declarations;
use crate::types as ty;
use crate::vars::Name;
use im;
use im::Vector;
use rustc_hir::def_id::DefId;
use rustc_middle::mir::Mutability;
use rustc_middle::ty::TyCtxt;
use rustc_middle::ty::{Ty, TyKind};
use std::collections::HashMap;

/// Translation context for type declarations
#[derive(Clone)]
pub struct TypeTransContext {
    pub types: ty::TypeDecls,
    type_decl_id_generator: ty::TypeDefId::Generator,
    /// Rust identifiers to translation identifiers
    pub rid_to_id: HashMap<DefId, ty::TypeDefId::Id>,
}

impl TypeTransContext {
    fn new() -> TypeTransContext {
        TypeTransContext {
            types: ty::TypeDecls::new(),
            type_decl_id_generator: ty::TypeDefId::Generator::new(),
            rid_to_id: HashMap::new(),
        }
    }

    fn fresh_def_id(&mut self) -> ty::TypeDefId::Id {
        self.type_decl_id_generator.fresh_id()
    }
}

impl Formatter<ty::TypeDefId::Id> for TypeTransContext {
    fn format_object(&self, id: ty::TypeDefId::Id) -> String {
        self.types.format_object(id)
    }
}

/// Auxiliary definition used to format declarations.
struct TypeDeclFormatter<'a> {
    tt_ctx: &'a TypeTransContext,
    /// The region parameters of the declaration we are printing (needed to
    /// correctly pretty print region var ids)
    region_params: &'a ty::RegionVarId::Vector<ty::RegionVar>,
    /// The type parameters of the declaration we are printing (needed to
    /// correctly pretty print type var ids)
    type_params: &'a ty::TypeVarId::Vector<ty::TypeVar>,
}

impl<'a> Formatter<ty::RegionVarId::Id> for TypeDeclFormatter<'a> {
    fn format_object(&self, id: ty::RegionVarId::Id) -> String {
        // Lookup the region parameter
        let v = self.region_params.get(id).unwrap();
        // Format
        v.to_string()
    }
}

impl<'a> Formatter<ty::TypeVarId::Id> for TypeDeclFormatter<'a> {
    fn format_object(&self, id: ty::TypeVarId::Id) -> String {
        // Lookup the type parameter
        let v = self.type_params.get(id).unwrap();
        // Format
        v.to_string()
    }
}

impl<'a> Formatter<&ty::Region<ty::RegionVarId::Id>> for TypeDeclFormatter<'a> {
    fn format_object(&self, r: &ty::Region<ty::RegionVarId::Id>) -> String {
        r.fmt_with_ctx(self)
    }
}

impl<'a> Formatter<&ty::ErasedRegion> for TypeDeclFormatter<'a> {
    fn format_object(&self, _: &ty::ErasedRegion) -> String {
        "".to_owned()
    }
}

impl<'a> Formatter<&ty::TypeDecl> for TypeDeclFormatter<'a> {
    fn format_object(&self, decl: &ty::TypeDecl) -> String {
        decl.fmt_with_ctx(self)
    }
}

impl<'a> Formatter<ty::TypeDefId::Id> for TypeDeclFormatter<'a> {
    fn format_object(&self, id: ty::TypeDefId::Id) -> String {
        self.tt_ctx.format_object(id)
    }
}

impl Formatter<&ty::TypeDecl> for TypeTransContext {
    fn format_object(&self, decl: &ty::TypeDecl) -> String {
        // Create a type decl formatter (which will take care of the
        // type parameters)
        let (region_params, type_params) = match decl {
            ty::TypeDecl::Enum(decl) => (&decl.region_params, &decl.type_params),
            ty::TypeDecl::Struct(decl) => (&decl.region_params, &decl.type_params),
        };
        let formatter = TypeDeclFormatter {
            tt_ctx: self,
            region_params,
            type_params,
        };
        formatter.format_object(decl)
    }
}

pub fn translate_region_name(region: &rustc_middle::ty::RegionKind) -> Option<String> {
    match region {
        rustc_middle::ty::RegionKind::ReEarlyBound(r) => Some(r.name.to_ident_string()),
        rustc_middle::ty::RegionKind::ReLateBound(_, br) => match br.kind {
            rustc_middle::ty::BoundRegionKind::BrAnon(_) => None,
            rustc_middle::ty::BoundRegionKind::BrNamed(_, symbol) => Some(symbol.to_ident_string()),
            rustc_middle::ty::BoundRegionKind::BrEnv => Some("@env".to_owned()),
        },
        rustc_middle::ty::RegionKind::ReFree(r) => match r.bound_region {
            rustc_middle::ty::BoundRegionKind::BrAnon(_) => None,
            rustc_middle::ty::BoundRegionKind::BrNamed(_, symbol) => Some(symbol.to_ident_string()),
            rustc_middle::ty::BoundRegionKind::BrEnv => Some("@env".to_owned()),
        },
        _ => {
            unreachable!();
        }
    }
}

/// Translate one type declaration.
///
/// Note that we translate the types one by one: we don't need to take into
/// account the fact that some types are mutually recursive at this point
/// (we will need to take that into account when generating the code in a file).
fn translate_type(tcx: &TyCtxt, trans_ctx: &mut TypeTransContext, def_id: DefId) -> Result<()> {
    trace!("{:?}", def_id);

    // Retrieve the definition
    let adt = tcx.adt_def(def_id);

    // Use a dummy substitution to instantiate the type parameters
    let substs = rustc_middle::ty::subst::InternalSubsts::identity_for_item(*tcx, adt.did);

    // Handle the region and type parameters.
    // - we need to know how many parameters there are
    // - we need to create a map linking the rust parameters to our pure
    //   parameters
    let mut region_params: Vec<ty::RegionVar> = vec![];
    let mut region_params_map: im::OrdMap<rustc_middle::ty::RegionKind, ty::RegionVarId::Id> =
        im::OrdMap::new();
    let mut region_params_counter = ty::RegionVarId::Generator::new();
    let mut type_params: Vec<ty::TypeVar> = vec![];
    let mut type_params_map: im::OrdMap<u32, ty::SigTy> = im::OrdMap::new();
    let mut type_params_counter = ty::TypeVarId::Generator::new();
    for p in substs.iter() {
        match p.unpack() {
            rustc_middle::ty::subst::GenericArgKind::Type(param_ty) => {
                // The type should be a Param:
                match param_ty.kind() {
                    rustc_middle::ty::TyKind::Param(param_ty) => {
                        let type_var = ty::TypeVar {
                            index: type_params_counter.fresh_id(),
                            name: param_ty.name.to_ident_string(),
                        };
                        type_params.push(type_var.clone());
                        let type_var = ty::Ty::TypeVar(type_var.index);
                        type_params_map.insert(param_ty.index, type_var);
                    }
                    _ => {
                        panic!("Inconsistent state");
                    }
                }
            }
            rustc_middle::ty::subst::GenericArgKind::Lifetime(region) => {
                let name = translate_region_name(region);
                let t_region = ty::RegionVar {
                    index: region_params_counter.fresh_id(),
                    name: name,
                };
                region_params_map.insert(*region, t_region.index);
                region_params.push(t_region);
            }
            rustc_middle::ty::subst::GenericArgKind::Const(_) => {
                unimplemented!();
            }
        }
    }

    trace!("type parameters:\n{:?}", type_params_map);

    // Explore the variants
    let mut var_id = ty::VariantId::Id::new(0); // Variant index
    let mut variants: Vec<ty::Variant> = vec![];
    let mut variants_map: im::HashMap<String, ty::VariantId::Id> = im::HashMap::new();
    for var_def in adt.variants.iter() {
        trace!("variant {}: {:?}", var_id, var_def);

        let mut fields: Vec<ty::Field> = vec![];
        let mut fields_map: im::HashMap<String, ty::FieldId::Id> = im::HashMap::new();
        let mut field_id = ty::FieldId::Id::new(0);
        for field_def in var_def.fields.iter() {
            trace!("variant {}: field {}: {:?}", var_id, field_id, field_def);

            let ty = field_def.ty(*tcx, substs);

            // Translate the field type
            let ty = translate_sig_ty(tcx, trans_ctx, &region_params_map, &type_params_map, &ty)?;

            // Retrieve the field name
            let field_name = field_def.ident.name.to_ident_string();

            // Store the field
            let field = ty::Field {
                name: field_name.clone(),
                ty: ty,
            };
            fields.push(field);
            fields_map.insert(field_name, field_id);

            field_id.incr();
        }

        let variant_name = var_def.ident.name.to_ident_string();
        variants_map.insert(variant_name.clone(), var_id);
        variants.push(ty::Variant {
            name: variant_name,
            fields: ty::FieldId::Vector::from(fields),
        });

        var_id.incr();
    }

    // Register the type
    let trans_id = trans_ctx.rid_to_id.get(&def_id).unwrap();
    let region_params = ty::RegionVarId::Vector::from(region_params);
    let type_params = ty::TypeVarId::Vector::from(type_params);
    let type_decl: ty::TypeDecl = match adt.adt_kind() {
        rustc_middle::ty::AdtKind::Struct => {
            assert!(variants.len() == 1);

            let name = type_def_id_to_name(tcx, def_id)?;
            let fields = variants[0].fields.clone();
            let mut fields_map = im::HashMap::new();
            for i in 0..fields.len() {
                let id = ty::FieldId::Id::new(i);
                let f = fields.get(id).unwrap();
                fields_map.insert(f.name.clone(), id);
            }

            ty::TypeDecl::Struct(ty::StructDecl {
                def_id: *trans_id,
                name: Name::from(name),
                region_params: region_params,
                type_params: type_params,
                fields: fields,
                fields_map: fields_map,
            })
        }
        rustc_middle::ty::AdtKind::Enum => {
            let name = type_def_id_to_name(tcx, def_id)?;

            ty::TypeDecl::Enum(ty::EnumDecl {
                def_id: *trans_id,
                name: Name::from(name),
                region_params: region_params,
                type_params: type_params,
                variants: ty::VariantId::Vector::from(variants),
                variants_map: variants_map,
            })
        }
        rustc_middle::ty::AdtKind::Union => {
            // Should have been filtered during the registration phase
            unreachable!();
        }
    };

    trace!("{} -> {}", trans_id.to_string(), type_decl.to_string());
    trans_ctx.types.types.push_back(type_decl);
    Ok(())
}

pub fn translate_non_erased_region<'tcx>(
    region_params: &im::OrdMap<rustc_middle::ty::RegionKind, ty::RegionVarId::Id>,
    region: rustc_middle::ty::Region<'tcx>,
) -> ty::Region<ty::RegionVarId::Id> {
    match region {
        rustc_middle::ty::RegionKind::ReErased => unreachable!(),
        rustc_middle::ty::RegionKind::ReStatic => ty::Region::Static,
        _ => {
            let rid = region_params.get(region).unwrap();
            ty::Region::Var(*rid)
        }
    }
}

/// Translate a region which is expected to be erased.
///
/// The regions are expected to be erased inside the function bodies (i.e.:
/// we believe MIR uses regions only in the function signatures).
pub fn translate_erased_region<'tcx>(region: rustc_middle::ty::Region<'tcx>) -> ty::ErasedRegion {
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
/// enumeration declaration, or later to translate the type of a variable.
///
/// This function is also used in other modules, like
/// [`translate_functions`](crate::translate_functions).
/// This is the reason why the `type_params` parameter is quite general,
/// and links rust identifiers to types, rather than type variables (in
/// this module, this map should always link to the translation of the
/// type variables, but in other variables it may define a real substitution,
/// in the case the interpreter dives into functions for example).
///
/// Note that we take as parameter a function to translate regions, because
/// regions can be translated in several manners (non-erased region or erased
/// regions), in which case the return type is different.
pub fn translate_ty<R>(
    tcx: &TyCtxt,
    trans_ctx: &TypeTransContext,
    region_translator: &dyn Fn(&rustc_middle::ty::RegionKind) -> R,
    type_params: &im::OrdMap<u32, ty::Ty<R>>,
    ty: &Ty,
) -> Result<ty::Ty<R>>
where
    R: Clone + Eq,
{
    trace!("{:?}", ty);
    match ty.kind() {
        TyKind::Bool => Ok(ty::Ty::Bool),
        TyKind::Char => Ok(ty::Ty::Char),
        TyKind::Int(int_ty) => Ok(ty::Ty::Integer(ty::IntegerTy::rust_int_ty_to_integer_ty(
            *int_ty,
        ))),
        TyKind::Uint(int_ty) => Ok(ty::Ty::Integer(ty::IntegerTy::rust_uint_ty_to_integer_ty(
            *int_ty,
        ))),
        TyKind::Str => Ok(ty::Ty::Str),
        TyKind::Float(_) => {
            trace!("Float");
            // This case should have been filtered during the registration phase
            unreachable!();
        }
        TyKind::Never => {
            return Ok(ty::Ty::Never);
        }

        TyKind::Adt(adt, substs) => {
            trace!("Adt: {:?}", adt.did);

            // Case disjunction on whether this is a box
            if adt.is_box() {
                trace!("Adt: is box");

                // Boxes have two type parameters: the stored type and the
                // allocator type. We ignore the allocator type.

                // Sanity check:
                let mut it = substs.iter();
                assert!(it.len() == 2);

                // The first parameter is the type of the stored element
                let param = it.next().unwrap();
                let param_ty = match param.unpack() {
                    rustc_middle::ty::subst::GenericArgKind::Type(param_ty) => param_ty,
                    _ => {
                        unreachable!();
                    }
                };

                // Translate the parameter type
                let ty = translate_ty(tcx, trans_ctx, region_translator, type_params, &param_ty)?;

                let regions = Vector::new();
                let tys = Vector::from(vec![ty]);

                return Ok(ty::Ty::Assumed(ty::AssumedTy::Box, regions, tys));
            } else {
                // Translate the type parameters instantiation
                let mut regions: Vec<R> = vec![];
                let mut params = vec![];
                let mut param_i = 0;
                for param in substs.iter() {
                    trace!("Adt: param {}: {:?}", param_i, param);
                    match param.unpack() {
                        rustc_middle::ty::subst::GenericArgKind::Type(param_ty) => {
                            let param_ty = translate_ty(
                                tcx,
                                trans_ctx,
                                region_translator,
                                type_params,
                                &param_ty,
                            )?;
                            params.push(param_ty);
                        }
                        rustc_middle::ty::subst::GenericArgKind::Lifetime(region) => {
                            regions.push(region_translator(region));
                        }
                        rustc_middle::ty::subst::GenericArgKind::Const(_) => {
                            unimplemented!();
                        }
                    }
                    param_i += 1;
                }

                // Retrieve the ADT identifier - should be a local def id
                if !adt.did.is_local() {
                    trace!("non local defid: {:?}", adt.did);
                    let _ = translate_non_local_defid(tcx, trans_ctx, type_params, adt.did);
                    unimplemented!();
                } else {
                    let id = trans_ctx.rid_to_id.get(&adt.did).unwrap();

                    // Return the instantiated ADT
                    return Ok(ty::Ty::Adt(
                        *id,
                        Vector::from(regions),
                        Vector::from(params),
                    ));
                }
            }
        }
        TyKind::Array(ty, _const_param) => {
            trace!("Array");

            let ty = translate_ty(tcx, trans_ctx, region_translator, type_params, ty)?;
            return Ok(ty::Ty::Array(Box::new(ty)));
        }
        TyKind::Slice(ty) => {
            trace!("Slice");

            let ty = translate_ty(tcx, trans_ctx, region_translator, type_params, ty)?;
            return Ok(ty::Ty::Slice(Box::new(ty)));
        }
        TyKind::Ref(region, ty, mutability) => {
            trace!("Ref");

            let region = region_translator(region);
            let ty = translate_ty(tcx, trans_ctx, region_translator, type_params, ty)?;
            let kind = match *mutability {
                Mutability::Not => ty::RefKind::Shared,
                Mutability::Mut => ty::RefKind::Mut,
            };
            return Ok(ty::Ty::Ref(region, Box::new(ty), kind));
        }
        TyKind::Tuple(substs) => {
            trace!("Tuple");

            let mut params = vec![];
            for param in substs.iter() {
                let param_ty = param.expect_ty();
                let param_ty =
                    translate_ty(tcx, trans_ctx, region_translator, type_params, &param_ty)?;
                params.push(param_ty);
            }

            return Ok(ty::Ty::Tuple(Vector::from(params)));
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
            // type in a type declaration, it should actually map to a type
            // parameter.
            trace!("Param");

            // Retrieve the translation of the substituted type:
            let ty = type_params.get(&param.index).unwrap();

            return Ok(ty.clone());
        }

        // Below: those types should be unreachable: if such types are used in
        // the MIR, we should have found them and failed during the registration
        // phase.
        TyKind::RawPtr(_) => {
            trace!("RawPtr");
            unreachable!();
        }
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

        TyKind::Dynamic(_, _) => {
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
        TyKind::Projection(_) => {
            trace!("Projection");
            unreachable!();
        }
        TyKind::Opaque(_, _) => {
            trace!("Opaque");
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
pub fn translate_sig_ty(
    tcx: &TyCtxt,
    trans_ctx: &TypeTransContext,
    region_params: &im::OrdMap<rustc_middle::ty::RegionKind, ty::RegionVarId::Id>,
    type_params: &im::OrdMap<u32, ty::SigTy>,
    ty: &Ty,
) -> Result<ty::SigTy> {
    translate_ty(
        tcx,
        trans_ctx,
        &|r| translate_non_erased_region(region_params, &r),
        type_params,
        ty,
    )
}

/// Translate a type where the regions are erased
/// Simply calls [`translate_ty`](translate_ty)
pub fn translate_ety(
    tcx: &TyCtxt,
    trans_ctx: &TypeTransContext,
    type_params: &im::OrdMap<u32, ty::ETy>,
    ty: &Ty,
) -> Result<ty::ETy> {
    translate_ty(
        tcx,
        trans_ctx,
        &|r| translate_erased_region(&r),
        type_params,
        ty,
    )
}

/// The non-local def ids benefit from a special treatment.
///
/// For now, we spot some specific def ids from the Rust standard libraries,
/// that we translate to specific types.
/// In the future, we'll implement proper support for projects divided into
/// different crates.
fn translate_non_local_defid<R>(
    tcx: &TyCtxt,
    _trans_ctx: &TypeTransContext,
    _type_params: &im::OrdMap<u32, ty::Ty<R>>,
    def_id: DefId,
) -> Result<ty::Ty<R>>
where
    R: Clone + Eq,
{
    trace!("{:?}", def_id);

    let _def_path = tcx.def_path(def_id);
    let _def_kind = tcx.def_kind(def_id);
    let _crate_name = tcx.crate_name(def_id.krate).to_string();
    unimplemented!();
}

/// Compute a name from a type [`DefId`](DefId).
///
/// This only works for def ids coming from types! For values, it is a bit
/// more complex.
pub fn type_def_id_to_name(tcx: &TyCtxt, def_id: DefId) -> Result<Vec<String>> {
    trace!("{:?}", def_id);

    let def_path = tcx.def_path(def_id);
    let crate_name = tcx.crate_name(def_id.krate).to_string();

    trace!("def path: {:?}", def_path);
    let mut name: Vec<String> = vec![crate_name];
    for path in def_path.data.iter() {
        // The path disambiguator may be <> 0, but I'm not sure in which cases
        // nor how to handle that case. For sanity, we thus check that it is
        // equal to 0.
        assert!(path.disambiguator == 0);
        match &path.data {
            rustc_hir::definitions::DefPathData::TypeNs(symbol) => {
                name.push(symbol.to_ident_string());
            }
            _ => {
                trace!("unexpected DefPathData: {:?}", &path.data);
                unreachable!();
            }
        }
    }

    trace!("resulting name: {:?}", &name);

    Ok(name)
}

/// Translate the types.
///
/// Note that in practice, we don't really need to know in which order we should
/// extract them (i.e.: the `Declarations` parameter is not really
/// necessary), because what is important is the file generation later.
/// Still, now that the order is computed, it's better to use it (leads to a
/// better indexing, for instance).
pub fn translate_types(tcx: &TyCtxt, decls: &Declarations) -> Result<TypeTransContext> {
    trace!();

    // Initialize the type context
    let mut trans_ctx = TypeTransContext::new();

    // Generate indices for all the types
    for def_id in &decls.type_ids {
        let id = trans_ctx.fresh_def_id();
        trans_ctx.rid_to_id.insert(*def_id, id);
    }

    // Translate the types.
    // Note that we can translate them one by one: what is important is to
    // generate code for all the types in a mutually recursive group at once,
    // when generating the files.
    for def_id in &decls.type_ids {
        translate_type(tcx, &mut trans_ctx, *def_id)?;
    }

    // Print the translated types
    for d in trans_ctx.types.types.iter() {
        trace!("translated type:\n{}", trans_ctx.format_object(d));
    }

    Ok(trans_ctx)
}
