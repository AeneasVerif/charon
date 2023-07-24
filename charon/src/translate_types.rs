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
use crate::types as ty;
use crate::types::{ConstGeneric, TypeDeclId};
use crate::ullbc_ast as ast;
use crate::values::{PrimitiveValue, ScalarValue};
use core::convert::*;
use im::Vector;
use rustc_hir::def_id::DefId;
use rustc_middle::mir::Mutability;
use rustc_middle::ty::{ParamEnv, Ty, TyCtxt, TyKind};
use rustc_session::Session;

/// Translation context for type definitions
/// TODO: merge with BodyTransContext
#[derive(Clone)]
pub struct TypeTransContext<'tcx, 'ctx> {
    /// This is used in very specific situations, for instance to retrieve parameter
    /// environments in [crate::translate_constants]. This should be the id of the
    /// definition we are exploring (can be the id of a type or function definition, for
    /// instance).
    pub def_id: DefId,
    ///
    pub tcx: TyCtxt<'tcx>,
    /// The type definitions
    pub type_defs: &'ctx ty::TypeDecls,
    /// The global definitions
    pub global_defs: &'ctx ast::GlobalDecls,
    /// Ordered declarations allowing to convert id to and from rid.
    pub ordered: &'ctx OrderedDecls,
    /// The map from Rust region var to LLBC region var
    pub region_params_map: im::OrdMap<rustc_middle::ty::RegionKind<'tcx>, ty::RegionVarId::Id>,
    /// The map from Rust type var identifier to LLBC type var
    pub type_params_map: im::OrdMap<u32, ty::TypeVarId::Id>,
    /// The level at which to extract the MIR
    pub mir_level: MirLevel,
}

impl<'tcx, 'ctx> TypeTransContext<'tcx, 'ctx> {
    pub fn new(
        def_id: DefId,
        tcx: TyCtxt<'tcx>,
        type_defs: &'ctx ty::TypeDecls,
        global_defs: &'ctx ast::GlobalDecls,
        ordered: &'ctx OrderedDecls,
        region_params_map: im::OrdMap<rustc_middle::ty::RegionKind<'tcx>, ty::RegionVarId::Id>,
        type_params_map: im::OrdMap<u32, ty::TypeVarId::Id>,
        mir_level: MirLevel,
    ) -> Self {
        Self {
            def_id,
            tcx,
            type_defs,
            global_defs,
            ordered,
            region_params_map,
            type_params_map,
            mir_level,
        }
    }

    pub fn get_id(&self, rid: DefId) -> TypeDeclId::Id {
        *self.ordered.type_rid_to_id.get(&rid).unwrap()
    }
}

/// Auxiliary definition used to format definitions.
struct TypeDeclFormatter<'a> {
    type_defs: &'a ty::TypeDecls,
    /// The region parameters of the definition we are printing (needed to
    /// correctly pretty print region var ids)
    region_params: &'a ty::RegionVarId::Vector<ty::RegionVar>,
    /// The type parameters of the definition we are printing (needed to
    /// correctly pretty print type var ids)
    type_params: &'a ty::TypeVarId::Vector<ty::TypeVar>,
    /// The const generic parameters of the definition we are printing (needed to
    /// correctly pretty print type var ids)
    const_generic_params: &'a ty::ConstGenericVarId::Vector<ty::ConstGenericVar>,
}

impl<'tcx, 'ctx> Formatter<ty::TypeDeclId::Id> for TypeTransContext<'tcx, 'ctx> {
    fn format_object(&self, id: ty::TypeDeclId::Id) -> String {
        self.type_defs.format_object(id)
    }
}

impl<'a> Formatter<ty::RegionVarId::Id> for TypeDeclFormatter<'a> {
    fn format_object(&self, id: ty::RegionVarId::Id) -> String {
        // Lookup the region parameter
        let v = self.region_params.get(id).unwrap();
        // Format
        v.to_string()
    }
}

impl<'a> Formatter<ty::ConstGenericVarId::Id> for TypeDeclFormatter<'a> {
    fn format_object(&self, id: ty::ConstGenericVarId::Id) -> String {
        // Lookup the region parameter
        let v = self.const_generic_params.get(id).unwrap();
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
    fn format_object(&self, def: &ty::TypeDecl) -> String {
        def.fmt_with_ctx(self)
    }
}

impl<'a> Formatter<ty::TypeDeclId::Id> for TypeDeclFormatter<'a> {
    fn format_object(&self, id: ty::TypeDeclId::Id) -> String {
        self.type_defs.format_object(id)
    }
}

impl<'tcx, 'ctx> Formatter<&ty::TypeDecl> for TypeTransContext<'tcx, 'ctx> {
    fn format_object(&self, def: &ty::TypeDecl) -> String {
        // Create a type def formatter (which will take care of the
        // type parameters)
        let formatter = TypeDeclFormatter {
            type_defs: self.type_defs,
            region_params: &def.region_params,
            type_params: &def.type_params,
            const_generic_params: &def.const_generic_params,
        };
        formatter.format_object(def)
    }
}

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
pub fn translate_ty<'tcx, R>(
    tt_ctx: &TypeTransContext<'tcx, '_>,
    region_translator: &dyn Fn(&rustc_middle::ty::RegionKind<'tcx>) -> R,
    ty: &Ty<'tcx>,
) -> Result<ty::Ty<R>>
where
    R: Clone + Eq,
{
    translate_ty_kind(tt_ctx, region_translator, ty.kind())
}

/// Translate a [TyKind].
///
/// See the comments for [translate_ty] (the two functions do the same thing,
/// they simply don't take the same input parameters).
pub fn translate_ty_kind<'tcx, R>(
    tt_ctx: &TypeTransContext<'tcx, '_>,
    region_translator: &dyn Fn(&rustc_middle::ty::RegionKind<'tcx>) -> R,
    ty_kind: &TyKind<'tcx>,
) -> Result<ty::Ty<R>>
where
    R: Clone + Eq,
{
    trace!("{:?}", ty_kind);
    match ty_kind {
        TyKind::Bool => Ok(ty::Ty::Primitive(ty::PrimitiveValueTy::Bool)),
        TyKind::Char => Ok(ty::Ty::Primitive(ty::PrimitiveValueTy::Char)),
        TyKind::Int(int_ty) => Ok(ty::Ty::Primitive(ty::PrimitiveValueTy::Integer(
            ty::IntegerTy::rust_int_ty_to_integer_ty(*int_ty),
        ))),
        TyKind::Uint(int_ty) => Ok(ty::Ty::Primitive(ty::PrimitiveValueTy::Integer(
            ty::IntegerTy::rust_uint_ty_to_integer_ty(*int_ty),
        ))),
        TyKind::Str => Ok(ty::Ty::Primitive(ty::PrimitiveValueTy::Str)),
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
                let name = type_def_id_to_name(tt_ctx.tcx, adt_did);
                assumed::type_to_used_params(&name)
            };

            // Translate the type parameters instantiation
            let (regions, params, cgs) =
                translate_substs(tt_ctx, region_translator, used_params, substs)?;

            // Retrieve the ADT identifier
            let def_id = translate_defid(tt_ctx, adt_did);

            // Return the instantiated ADT
            Ok(ty::Ty::Adt(
                def_id,
                Vector::from(regions),
                Vector::from(params),
                Vector::from(cgs),
            ))
        }
        TyKind::Array(ty, const_param) => {
            trace!("Array");

            let c = const_param
                .try_eval_usize(tt_ctx.tcx, ParamEnv::empty())
                .unwrap();
            let ty = vec![translate_ty(tt_ctx, region_translator, ty)?];
            let cgs = vec![ty::ConstGeneric::Value(PrimitiveValue::Scalar(
                ScalarValue::Usize(c as usize),
            ))];
            let id = ty::TypeId::Assumed(ty::AssumedTy::Array);
            Ok(ty::Ty::Adt(
                id,
                Vector::new(),
                Vector::from(ty),
                Vector::from(cgs),
            ))
        }
        TyKind::Slice(ty) => {
            trace!("Slice");

            let ty = vec![translate_ty(tt_ctx, region_translator, ty)?];
            let id = ty::TypeId::Assumed(ty::AssumedTy::Slice);
            Ok(ty::Ty::Adt(
                id,
                Vector::new(),
                Vector::from(ty),
                Vector::new(),
            ))
        }
        TyKind::Ref(region, ty, mutability) => {
            trace!("Ref");

            let region = region_translator(region);
            let ty = translate_ty(tt_ctx, region_translator, ty)?;
            let kind = match *mutability {
                Mutability::Not => ty::RefKind::Shared,
                Mutability::Mut => ty::RefKind::Mut,
            };
            Ok(ty::Ty::Ref(region, Box::new(ty), kind))
        }
        TyKind::RawPtr(ty_and_mut) => {
            trace!("RawPtr: {:?}", ty_and_mut);
            let ty = translate_ty(tt_ctx, region_translator, &ty_and_mut.ty)?;
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
                let param_ty = translate_ty(tt_ctx, region_translator, &param)?;
                params.push(param_ty);
            }

            Ok(ty::Ty::Adt(
                ty::TypeId::Tuple,
                Vector::new(),
                Vector::from(params),
                Vector::new(),
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
            let ty = tt_ctx.type_params_map.get(&param.index).unwrap();
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
pub fn translate_sig_ty<'tcx>(
    tt_ctx: &TypeTransContext<'tcx, '_>,
    ty: &Ty<'tcx>,
) -> Result<ty::RTy> {
    translate_ty(
        tt_ctx,
        &|r| translate_non_erased_region(&tt_ctx.region_params_map, *r),
        ty,
    )
}

/// Translate a type where the regions are erased
/// Simply calls [translate_ty]
pub fn translate_ety<'tcx>(tt_ctx: &TypeTransContext<'tcx, '_>, ty: &Ty<'tcx>) -> Result<ty::ETy> {
    translate_ty(tt_ctx, &|r| translate_erased_region(*r), ty)
}

/// Simply calls [translate_ty_kind]
pub fn translate_ety_kind<'tcx>(
    tt_ctx: &TypeTransContext<'tcx, '_>,
    ty: &TyKind<'tcx>,
) -> Result<ty::ETy> {
    translate_ty_kind(tt_ctx, &|r| translate_erased_region(*r), ty)
}

fn translate_substs<'tcx, R>(
    tt_ctx: &TypeTransContext<'tcx, '_>,
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
                let param_ty = translate_ty(tt_ctx, region_translator, &param_ty)?;
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
fn translate_defid(tt_ctx: &TypeTransContext, def_id: DefId) -> ty::TypeId {
    trace!("{:?}", def_id);

    if def_id.is_local() {
        ty::TypeId::Adt(tt_ctx.get_id(def_id))
    } else {
        // Non-local: check if the type has primitive support

        // Retrieve the type name
        let name = type_def_id_to_name(tt_ctx.tcx, def_id);

        match assumed::get_type_id_from_name(&name) {
            Option::Some(id) => {
                // The type has primitive support
                ty::TypeId::Assumed(id)
            }
            Option::None => {
                // The type is external
                ty::TypeId::Adt(tt_ctx.get_id(def_id))
            }
        }
    }
}

/// Helper type
struct TypeGenericsInfo<'tcx> {
    substs: rustc_middle::ty::subst::SubstsRef<'tcx>,
    region_params: Vec<ty::RegionVar>,
    region_params_map: im::OrdMap<rustc_middle::ty::RegionKind<'tcx>, ty::RegionVarId::Id>,
    type_params: Vec<ty::TypeVar>,
    type_params_map: im::OrdMap<u32, ty::TypeVarId::Id>,
    const_generic_params: Vec<ty::ConstGenericVar>,
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
fn translate_type_generics<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> TypeGenericsInfo<'tcx> {
    // Check the generics
    generics::check_type_generics(tcx, def_id);

    // Use a dummy substitution to instantiate the type parameters
    let substs = rustc_middle::ty::subst::InternalSubsts::identity_for_item(tcx, def_id);

    // Handle the region and type parameters:
    // - we need to know how many parameters there are
    // - we need to create a map linking the rust parameters to our pure
    //   parameters
    let mut region_params: Vec<ty::RegionVar> = vec![];
    let mut region_params_map: im::OrdMap<rustc_middle::ty::RegionKind<'tcx>, ty::RegionVarId::Id> =
        im::OrdMap::new();
    let mut region_params_counter = ty::RegionVarId::Generator::new();
    let mut type_params: Vec<ty::TypeVar> = vec![];
    let mut type_params_map: im::OrdMap<u32, ty::TypeVarId::Id> = im::OrdMap::new();
    let mut type_params_counter = ty::TypeVarId::Generator::new();
    let const_generic_params = vec![];
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
                        let index = type_var.index;
                        type_params.push(type_var);
                        type_params_map.insert(param_ty.index, index);
                    }
                    _ => {
                        panic!("Inconsistent state");
                    }
                }
            }
            rustc_middle::ty::subst::GenericArgKind::Lifetime(region) => {
                let name = translate_region_name(&region);
                let t_region = ty::RegionVar {
                    index: region_params_counter.fresh_id(),
                    name,
                };
                region_params_map.insert(*region, t_region.index);
                region_params.push(t_region);
            }
            rustc_middle::ty::subst::GenericArgKind::Const(_) => {
                unimplemented!();
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
        for r in &region_params {
            let name = &r.name;
            if name.is_some() {
                let name = name.as_ref().unwrap();
                assert!(s.contains(name));
                s.insert(name.clone());
            }
        }
    }

    TypeGenericsInfo {
        substs,
        region_params,
        region_params_map,
        type_params,
        type_params_map,
        const_generic_params,
    }
}

/// Translate one local type definition which has not been flagged as opaque.
fn translate_transparent_type<'tcx>(
    sess: &Session,
    tt_ctx: &TypeTransContext<'tcx, '_>,
    trans_id: ty::TypeDeclId::Id,
    substs: &rustc_middle::ty::subst::SubstsRef<'tcx>,
) -> Result<ty::TypeDeclKind> {
    trace!("{}", trans_id);

    // Retrieve the definition
    trace!("{:?}", tt_ctx.def_id);
    let adt = tt_ctx.tcx.adt_def(tt_ctx.def_id);

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

            let ty = field_def.ty(tt_ctx.tcx, substs);

            // Translate the field type
            let ty = translate_sig_ty(&tt_ctx, &ty)?;

            // Retrieve the field name.
            // Note that the only way to check if the user wrote the name or
            // if it is just an integer generated by rustc is by checking if
            // if is just made of numerals...
            let field_name = field_def.ident(tt_ctx.tcx).name.to_ident_string();
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
                tt_ctx.tcx,
                &tt_ctx.ordered.file_to_id,
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

        let meta =
            meta::get_meta_from_rid(sess, tt_ctx.tcx, &tt_ctx.ordered.file_to_id, var_def.def_id);
        let variant_name = var_def.ident(tt_ctx.tcx).name.to_ident_string();
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
    global_defs: &ast::GlobalDecls,
    trans_id: ty::TypeDeclId::Id,
    mir_level: MirLevel,
) -> Result<()> {
    let info = decls.decls_info.get(&AnyDeclId::Type(trans_id)).unwrap();

    // Check and translate the generics
    let TypeGenericsInfo {
        substs,
        region_params,
        region_params_map,
        type_params,
        type_params_map,
        const_generic_params,
    } = translate_type_generics(tcx, info.rid);

    // Initialize the type translation context
    let tt_ctx = TypeTransContext::new(
        info.rid,
        tcx,
        type_defs,
        global_defs,
        decls,
        region_params_map,
        type_params_map,
        mir_level,
    );

    // Check if the type is opaque or external, and delegate the translation
    // of the "body" to the proper function
    let kind = if !info.is_local() || !info.is_transparent {
        // Opaque types are:
        // - external types
        // - local types flagged as opaque
        ty::TypeDeclKind::Opaque
    } else {
        translate_transparent_type(sess, &tt_ctx, trans_id, &substs)?
    };

    // Register the type
    let name = type_def_id_to_name(tcx, info.rid);
    let region_params = ty::RegionVarId::Vector::from(region_params);
    let type_params = ty::TypeVarId::Vector::from(type_params);
    let const_generic_params = ty::ConstGenericVarId::Vector::from(const_generic_params);

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
    assert!(type_defs.types.len() == trans_id.to_usize());

    type_defs.types.push_back(type_def);
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

    // TODO: for now we initialize the global map as an empty map
    // This won't be an issue once we merge the contexts
    let global_defs = ast::GlobalDeclId::Vector::new();

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
    for d in type_defs.types.iter() {
        let formatter = TypeDeclFormatter {
            type_defs: &type_defs,
            region_params: &d.region_params,
            type_params: &d.type_params,
            const_generic_params: &d.const_generic_params,
        };
        trace!("translated type:\n{}\n", formatter.format_object(d));
    }

    Ok((types_cover_regions, type_defs))
}
