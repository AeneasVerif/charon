//! Translate functions from the rust compiler MIR to our internal representation.
//! Our internal representation is very close to MIR, but is more convenient for
//! us to handle, and easier to maintain - rustc's representation can evolve
//! independently.

#![allow(dead_code)]
use crate::assumed;
use crate::common::*;
use crate::expressions as e;
use crate::formatter::Formatter;
use crate::generics;
use crate::im_ast as ast;
use crate::names::function_def_id_to_name;
use crate::regions_hierarchy as rh;
use crate::regions_hierarchy::TypesConstraintsMap;
use crate::rust_to_local_ids::*;
use crate::translate_types;
use crate::types as ty;
use crate::types::{FieldId, VariantId};
use crate::values as v;
use hashlink::linked_hash_map::LinkedHashMap;
use im;
use im::Vector;
use rustc_hir::def_id::DefId;
use rustc_middle::mir;
use rustc_middle::mir::{
    BasicBlock, Body, Operand, Place, PlaceElem, SourceScope, Statement, StatementKind, Terminator,
    TerminatorKind, START_BLOCK,
};
use rustc_middle::ty as mir_ty;
use rustc_middle::ty::{ConstKind, Ty, TyCtxt, TyKind};
use rustc_span::BytePos;
use rustc_span::Span;
use std::cmp::Ordering;
use std::collections::HashMap;
use std::iter::FromIterator;
use translate_types::{translate_erased_region, translate_region_name, TypeTransContext};

/// Translation context for function definitions (contains a type context)
pub struct FunTransContext<'ctx> {
    /// The ordered declarations
    pub ordered: &'ctx OrderedDecls,
    /// Type definitions
    pub type_defs: &'ctx ty::TypeDecls,
    /// The function definitions
    /// TODO: rename to fun_defs
    pub defs: &'ctx ast::FunDefs,
}

/// A translation context for function bodies.
///
/// We use `im::OrdMap` a lot in places where we could use a
/// `std::collections::BTreeMap` (because we actually don't do context
/// duplication). For now the performance doesn't matter, and it allows
/// not to mix too many very similar data structures, but we might consider
/// using `std::collections::BTreeMap` instead.
#[derive(Clone)]
struct BodyTransContext<'ctx, 'ctx1> {
    /// This is used in very specific situations.
    def_id: DefId,
    /// The function translation context, containing the function definitions.
    /// Also contains the type translation context.
    ft_ctx: &'ctx FunTransContext<'ctx1>,
    /// Region counter
    regions_counter: ty::RegionVarId::Generator,
    /// The regions
    regions: ty::RegionVarId::Vector<ty::RegionVar>,
    /// The map from rust region to translated region indices
    rregions_to_ids: im::OrdMap<rustc_middle::ty::RegionKind, ty::RegionVarId::Id>,
    /// Id counter for the type variables
    type_vars_counter: ty::TypeVarId::Generator,
    /// The type variables
    type_vars: ty::TypeVarId::Vector<ty::TypeVar>,
    /// The map from rust type variable indices to translated type variable
    /// indices.
    rtype_vars_to_ids: im::OrdMap<u32, ty::TypeVarId::Id>,
    /// Redundant with `rtype_vars_to_ids`. We need this for [`translate_ty`](translate_ty).
    /// This maps type variables to types with regions used in signatures.
    rtype_vars_to_rtypes: im::OrdMap<u32, ty::RTy>,
    /// Redundant with `rtype_vars_to_ids`. We need this for [`translate_ty`](translate_ty).
    /// This maps type variables to types with erased regions.
    rtype_vars_to_etypes: im::OrdMap<u32, ty::ETy>,
    /// Id counter for the variables
    vars_counter: v::VarId::Generator,
    /// The "regular" variables
    vars: v::VarId::Vector<ast::Var>,
    /// The map from rust variable indices to translated variables indices.
    rvars_to_ids: im::OrdMap<u32, v::VarId::Id>,
    /// Block id counter
    blocks_counter: ast::BlockId::Generator,
    /// The translated blocks. We can't use `ast::BlockId::Vector<ast::BlockData>`
    /// here because we might generate several fresh indices before actually
    /// adding the resulting blocks to the map.
    blocks: im::OrdMap<ast::BlockId::Id, ast::BlockData>,
    /// The map from rust blocks to translated blocks
    rblocks_to_ids: im::OrdMap<BasicBlock, ast::BlockId::Id>,
}

impl<'ctx> FunTransContext<'ctx> {
    fn get_def_id_from_rid(&self, def_id: DefId) -> Option<ast::FunDefId::Id> {
        self.ordered.fun_rid_to_id.get(&def_id).map(|x| *x)
    }

    fn get_def_rid_from_id(&self, def_id: ast::FunDefId::Id) -> Option<DefId> {
        self.ordered.fun_id_to_rid.get(&def_id).map(|x| *x)
    }
}

impl<'ctx, 'ctx1> BodyTransContext<'ctx, 'ctx1> {
    /// Create a new `ExecContext`.
    fn new(def_id: DefId, ft_ctx: &'ctx FunTransContext<'ctx1>) -> BodyTransContext<'ctx, 'ctx1> {
        BodyTransContext {
            def_id,
            ft_ctx,
            regions_counter: ty::RegionVarId::Generator::new(),
            regions: ty::RegionVarId::Vector::new(),
            rregions_to_ids: im::OrdMap::new(),
            type_vars_counter: ty::TypeVarId::Generator::new(),
            type_vars: ty::TypeVarId::Vector::new(),
            rtype_vars_to_ids: im::OrdMap::new(),
            rtype_vars_to_rtypes: im::OrdMap::new(),
            rtype_vars_to_etypes: im::OrdMap::new(),
            vars_counter: v::VarId::Generator::new(),
            vars: v::VarId::Vector::new(),
            rvars_to_ids: im::OrdMap::new(),
            blocks_counter: ast::BlockId::Generator::new(),
            blocks: im::OrdMap::new(),
            rblocks_to_ids: im::OrdMap::new(),
        }
    }

    fn get_local(&self, local: &mir::Local) -> Option<v::VarId::Id> {
        self.rvars_to_ids.get(&local.as_u32()).map(|x| *x)
    }

    fn get_block_id_from_rid(&self, rid: BasicBlock) -> Option<ast::BlockId::Id> {
        self.rblocks_to_ids.get(&rid).map(|x| *x)
    }

    fn get_var_from_id(&self, var_id: v::VarId::Id) -> Option<&ast::Var> {
        self.vars.get(var_id)
    }

    fn get_region_from_rust(&self, r: rustc_middle::ty::RegionKind) -> Option<ty::RegionVarId::Id> {
        self.rregions_to_ids.get(&r).map(|x| *x)
    }

    fn push_region(
        &mut self,
        r: rustc_middle::ty::RegionKind,
        name: Option<String>,
    ) -> ty::RegionVarId::Id {
        use crate::id_vector::ToUsize;
        let rid = self.regions_counter.fresh_id();
        assert!(rid.to_usize() == self.regions.len());
        let var = ty::RegionVar {
            index: rid,
            name: name.clone(),
        };
        self.regions.insert(rid, var);
        self.rregions_to_ids.insert(r, rid);
        return rid;
    }

    fn push_type_var(&mut self, rindex: u32, name: String) -> ty::TypeVarId::Id {
        use crate::id_vector::ToUsize;
        let var_id = self.type_vars_counter.fresh_id();
        assert!(var_id.to_usize() == self.type_vars.len());
        let var = ty::TypeVar {
            index: var_id,
            name: name.clone(),
        };
        self.type_vars.insert(var_id, var);
        self.rtype_vars_to_ids.insert(rindex, var_id);
        self.rtype_vars_to_rtypes
            .insert(rindex, ty::Ty::TypeVar(var_id));
        self.rtype_vars_to_etypes
            .insert(rindex, ty::Ty::TypeVar(var_id));
        return var_id;
    }

    fn push_var(&mut self, rid: u32, ty: ty::ETy, name: Option<String>) {
        use crate::id_vector::ToUsize;
        let var_id = self.vars_counter.fresh_id();
        assert!(var_id.to_usize() == self.vars.len());
        let var = ast::Var {
            index: var_id,
            name: name.clone(),
            ty,
        };
        self.vars.insert(var_id, var);
        self.rvars_to_ids.insert(rid, var_id);
    }

    fn fresh_block_id(&mut self, rid: BasicBlock) -> ast::BlockId::Id {
        let block_id = self.blocks_counter.fresh_id();
        self.rblocks_to_ids.insert(rid, block_id);
        return block_id;
    }

    fn push_block(&mut self, id: ast::BlockId::Id, block: ast::BlockData) {
        self.blocks.insert(id, block);
    }

    fn get_type_defs(&self) -> &ty::TypeDecls {
        &self.ft_ctx.type_defs
    }
}

impl<'ctx> Formatter<ty::TypeDeclId::Id> for FunTransContext<'ctx> {
    fn format_object(&self, id: ty::TypeDeclId::Id) -> String {
        self.type_defs.format_object(id)
    }
}

impl<'ctx, 'ctx1> Formatter<ty::TypeVarId::Id> for BodyTransContext<'ctx, 'ctx1> {
    fn format_object(&self, id: ty::TypeVarId::Id) -> String {
        let v = self.type_vars.get(id).unwrap();
        v.to_string()
    }
}

impl<'ctx, 'ctx1> Formatter<v::VarId::Id> for BodyTransContext<'ctx, 'ctx1> {
    fn format_object(&self, id: v::VarId::Id) -> String {
        let v = self.vars.get(id).unwrap();
        v.to_string()
    }
}

impl<'ctx, 'ctx1> Formatter<ty::RegionVarId::Id> for BodyTransContext<'ctx, 'ctx1> {
    fn format_object(&self, id: ty::RegionVarId::Id) -> String {
        let v = self.regions.get(id).unwrap();
        v.to_string()
    }
}

impl<'ctx, 'ctx1> Formatter<&ty::Region<ty::RegionVarId::Id>> for BodyTransContext<'ctx, 'ctx1> {
    fn format_object(&self, r: &ty::Region<ty::RegionVarId::Id>) -> String {
        r.fmt_with_ctx(self)
    }
}

impl<'ctx, 'ctx1> Formatter<&ty::ErasedRegion> for BodyTransContext<'ctx, 'ctx1> {
    fn format_object(&self, _: &ty::ErasedRegion) -> String {
        "'_".to_owned()
    }
}

impl<'ctx, 'ctx1> Formatter<ty::TypeDeclId::Id> for BodyTransContext<'ctx, 'ctx1> {
    fn format_object(&self, id: ty::TypeDeclId::Id) -> String {
        self.ft_ctx.type_defs.format_object(id)
    }
}

impl<'ctx, 'ctx1> Formatter<&ty::Ty<ty::Region<ty::RegionVarId::Id>>>
    for BodyTransContext<'ctx, 'ctx1>
{
    fn format_object(&self, ty: &ty::Ty<ty::Region<ty::RegionVarId::Id>>) -> String {
        ty.fmt_with_ctx(self)
    }
}

impl<'ctx, 'ctx1> Formatter<&ty::Ty<ty::ErasedRegion>> for BodyTransContext<'ctx, 'ctx1> {
    fn format_object(&self, ty: &ty::Ty<ty::ErasedRegion>) -> String {
        ty.fmt_with_ctx(self)
    }
}

fn translate_ety<'tcx, 'ctx, 'ctx1>(
    tcx: TyCtxt,
    bt_ctx: &BodyTransContext<'ctx, 'ctx1>,
    ty: &mir_ty::Ty,
) -> Result<ty::ETy> {
    let ty_ctx = TypeTransContext {
        types: &bt_ctx.ft_ctx.type_defs,
        type_rid_to_id: &bt_ctx.ft_ctx.ordered.type_rid_to_id,
        type_id_to_rid: &bt_ctx.ft_ctx.ordered.type_id_to_rid,
    };
    translate_types::translate_ety(tcx, &ty_ctx, &bt_ctx.rtype_vars_to_etypes, &ty)
}

fn translate_sig_ty<'tcx, 'ctx, 'ctx1>(
    tcx: TyCtxt<'tcx>,
    bt_ctx: &BodyTransContext<'ctx, 'ctx1>,
    ty: &mir_ty::Ty<'tcx>,
) -> Result<ty::RTy> {
    let ty_ctx = TypeTransContext {
        types: &bt_ctx.ft_ctx.type_defs,
        type_rid_to_id: &bt_ctx.ft_ctx.ordered.type_rid_to_id,
        type_id_to_rid: &bt_ctx.ft_ctx.ordered.type_id_to_rid,
    };
    translate_types::translate_sig_ty(
        tcx,
        &ty_ctx,
        &bt_ctx.rregions_to_ids,
        &bt_ctx.rtype_vars_to_rtypes,
        &ty,
    )
}

/// Translate a function's local variables by adding them in the environment.
fn translate_body_locals<'tcx, 'ctx, 'ctx1>(
    tcx: TyCtxt<'tcx>,
    bt_ctx: &mut BodyTransContext<'ctx, 'ctx1>,
    body: &Body<'tcx>,
) -> Result<()> {
    // First, retrieve the debug info - we want to retrieve the names
    // of the variables (which otherwise are just referenced with indices).
    // This is mostly to generate a clean and readable translation later on.
    // It seems the only way of linking the locals to the debug info is
    // through the spans.
    let mut span_to_var_name: im::OrdMap<Span, String> = im::OrdMap::new();
    for info in &body.var_debug_info {
        span_to_var_name.insert(info.source_info.span, info.name.to_ident_string());
    }

    // Translate the parameters
    for (index, var) in body.local_decls.iter_enumerated() {
        trace!(
            "Translating local of index {} and type {:?}",
            index.as_usize(),
            var.ty
        );

        // Find the name of the variable
        let span = var.source_info.span;
        let name: Option<String> = span_to_var_name.get(&span).map(|s| s.clone());

        // Translate the type
        let ty = translate_ety(tcx, bt_ctx, &var.ty)?;

        // Add the variable to the environment
        bt_ctx.push_var(index.as_u32(), ty, name);
    }

    return Ok(());
}

/// Translate a function's body.
///
/// The local variables should already have been translated and inserted in
/// the context.
fn translate_transparent_function_body<'tcx, 'ctx, 'ctx1>(
    tcx: TyCtxt<'tcx>,
    bt_ctx: &mut BodyTransContext<'ctx, 'ctx1>,
    body: &Body<'tcx>,
) -> Result<()> {
    trace!();

    let id = translate_basic_block(tcx, bt_ctx, body, START_BLOCK)?;
    assert!(id == ast::START_BLOCK_ID);

    Ok(())
}

fn translate_basic_block<'tcx, 'ctx, 'ctx1>(
    tcx: TyCtxt<'tcx>,
    bt_ctx: &mut BodyTransContext<'ctx, 'ctx1>,
    body: &Body<'tcx>,
    block_id: BasicBlock,
) -> Result<ast::BlockId::Id> {
    // Check if the block has already been translated
    let id = bt_ctx.rblocks_to_ids.get(&block_id);
    if id.is_some() {
        return Ok(*id.unwrap());
    }
    let nid = bt_ctx.fresh_block_id(block_id);

    // Retrieve the block data
    let block = body.basic_blocks().get(block_id).unwrap();

    // Translate the statements
    let mut statements = Vec::new();
    for statement in &block.statements {
        trace!("statement: {:?}", statement);

        // Some statements might be ignored, hence the optional returned value
        let opt_statement = translate_statement(tcx, bt_ctx, &statement)?;
        match opt_statement {
            Some(statement) => statements.push(statement),
            None => (),
        }
    }

    // Translate the terminator
    let terminator = block.terminator();
    let terminator = translate_terminator(tcx, bt_ctx, body, terminator)?;

    // Insert the block in the translated blocks
    let block = ast::BlockData {
        statements,
        terminator,
    };

    bt_ctx.push_block(nid, block);

    Ok(nid)
}

/// Translate a place
fn translate_place<'tcx, 'ctx, 'ctx1>(
    bt_ctx: &'ctx BodyTransContext<'ctx, 'ctx1>,
    place: &Place<'tcx>,
) -> e::Place {
    let var_id = bt_ctx.get_local(&place.local).unwrap();
    let var = bt_ctx.get_var_from_id(var_id).unwrap();
    let projection =
        translate_projection(&bt_ctx.ft_ctx.type_defs, var.ty.clone(), place.projection);

    e::Place { var_id, projection }
}

/// Translate a projection
///
/// We use the variable type to disambiguate between different kinds of
/// projections. For instance, rust uses `Deref` both to dereference mutable/shared
/// references and to move values from inside a box. On our side, we distinguish
/// the two kinds of dereferences.
fn translate_projection<'tcx>(
    type_defs: &ty::TypeDecls,
    var_ty: ty::ETy,
    rprojection: &rustc_middle::ty::List<PlaceElem<'tcx>>,
) -> e::Projection {
    trace!("- projection: {:?}\n- var_ty: {:?}", rprojection, var_ty);

    // We need to track the type of the value we look at, while exploring the path.
    // This is important to disambiguate, for instance, dereferencement operations.
    let mut path_type = var_ty;
    // When projection an ADT's field, we need to remember what variant it
    // should be in case of an enumeration (such information is introduced
    // by Downcast projections *before* the field projection).
    let mut downcast_id: Option<VariantId::Id> = None;

    let mut projection = e::Projection::new();
    for pelem in rprojection {
        match pelem {
            mir::ProjectionElem::Deref => {
                downcast_id = None;
                // We need to disambiguate the two kinds of dereferences
                use std::ops::Deref;
                match path_type {
                    ty::Ty::Ref(_, ty, _) => {
                        path_type = ty.deref().clone();
                        projection.push_back(e::ProjectionElem::Deref);
                    }
                    ty::Ty::Adt(ty::TypeId::Assumed(ty::AssumedTy::Box), regions, tys) => {
                        assert!(regions.is_empty());
                        assert!(tys.len() == 1);
                        path_type = tys[0].clone();
                        projection.push_back(e::ProjectionElem::DerefBox);
                    }
                    _ => {
                        unreachable!();
                    }
                }
            }
            mir::ProjectionElem::Field(field, _) => {
                let field_id = translate_field(field);
                // Update the path type and generate the proj kind at the
                // same time.
                let proj_kind = match path_type {
                    ty::Ty::Adt(ty::TypeId::Adt(type_id), _regions, tys) => {
                        let type_def = type_defs.get_type_def(type_id).unwrap();

                        // If (and only if) the ADT is an enumeration, we should
                        // have downcast information (that we need to figure out
                        // the variant, and thus know how to project).
                        assert!(type_def.kind.is_enum() == downcast_id.is_some());

                        path_type = type_def.get_erased_regions_instantiated_field_type(
                            downcast_id,
                            &tys,
                            field_id,
                        );

                        e::FieldProjKind::Adt(type_id, downcast_id)
                    }
                    ty::Ty::Adt(ty::TypeId::Tuple, regions, tys) => {
                        assert!(regions.len() == 0);
                        assert!(downcast_id.is_none());
                        path_type = tys.get(field.as_usize()).unwrap().clone();
                        e::FieldProjKind::Tuple(tys.len())
                    }
                    ty::Ty::Adt(ty::TypeId::Assumed(ty::AssumedTy::Option), regions, tys) => {
                        assert!(regions.len() == 0);
                        assert!(tys.len() == 1);
                        assert!(downcast_id.is_some());
                        assert!(field_id == ty::FieldId::ZERO);

                        path_type = tys.get(0).unwrap().clone();
                        let variant_id = downcast_id.unwrap();
                        assert!(variant_id == assumed::OPTION_SOME_VARIANT_ID);
                        e::FieldProjKind::Option(variant_id)
                    }
                    _ => {
                        trace!("{:?}", path_type);
                        unreachable!();
                    }
                };
                projection.push_back(e::ProjectionElem::Field(proj_kind, field_id));
                downcast_id = None;
            }
            mir::ProjectionElem::Index(_local) => {
                unimplemented!();
            }
            mir::ProjectionElem::ConstantIndex {
                offset: _,
                min_length: _,
                from_end: _,
            } => {
                unimplemented!();
            }
            mir::ProjectionElem::Subslice {
                from: _,
                to: _,
                from_end: _,
            } => {
                unimplemented!();
            }
            mir::ProjectionElem::Downcast(_, variant_id) => {
                // Downcast an enum to a specific variant.
                // For example, the left value of:
                // `((_0 as Right).0: T2) = move _1;`
                // Note that on the above example, the downcast preceeds the
                // field projection.
                let vid = translate_variant_id(variant_id);
                // Don't update the variable type
                // Remember the new downcast
                downcast_id = Some(vid);
                // We don't translate downcasts: the information is merged with
                // field projections
            }
        }
    }

    return projection;
}

/// Translate some cases of a constant operand.
///
/// A constant operand is usually an instance of a primitive type (bool, char,
/// integer...). However, it may also be an instance of a degenerate ADT or
/// tuple (if an ADT has only one variant and no fields, it is a constant,
/// and unit is encoded by MIR as a 0-tuple). This function handles the
/// primitive type cases: the other cases should have been filtered and
/// handled elsewhere.
fn translate_operand_constant_value_constant_value<'tcx>(
    ty: &Ty<'tcx>,
    value: &mir::interpret::ConstValue<'tcx>,
) -> (ty::ETy, v::ConstantValue) {
    trace!();
    match value {
        mir::interpret::ConstValue::Scalar(scalar) => {
            // The documentation explicitly says not to match on a
            // scalar. We match on the type and convert the value
            // following this, by calling the appropriate `to_*`
            // method
            match ty.kind() {
                TyKind::Bool => (
                    ty::Ty::Bool,
                    v::ConstantValue::Bool(scalar.to_bool().unwrap()),
                ),
                TyKind::Char => (
                    ty::Ty::Char,
                    v::ConstantValue::Char(scalar.to_char().unwrap()),
                ),
                TyKind::Int(int_ty) => {
                    match int_ty {
                        rustc_middle::ty::IntTy::Isize => {
                            // This is a bit annoying: there is no
                            // `to_isize`. For now, we make the hypothesis
                            // that isize is an int64
                            assert!(std::mem::size_of::<isize>() == 8);
                            return (
                                ty::Ty::Integer(ty::IntegerTy::Isize),
                                v::ConstantValue::Scalar(v::ScalarValue::Isize(
                                    scalar.to_i64().unwrap() as isize,
                                )),
                            );
                        }
                        rustc_middle::ty::IntTy::I8 => (
                            ty::Ty::Integer(ty::IntegerTy::I8),
                            v::ConstantValue::Scalar(v::ScalarValue::I8(scalar.to_i8().unwrap())),
                        ),
                        rustc_middle::ty::IntTy::I16 => (
                            ty::Ty::Integer(ty::IntegerTy::I16),
                            v::ConstantValue::Scalar(v::ScalarValue::I16(scalar.to_i16().unwrap())),
                        ),
                        rustc_middle::ty::IntTy::I32 => (
                            ty::Ty::Integer(ty::IntegerTy::I32),
                            v::ConstantValue::Scalar(v::ScalarValue::I32(scalar.to_i32().unwrap())),
                        ),
                        rustc_middle::ty::IntTy::I64 => (
                            ty::Ty::Integer(ty::IntegerTy::I64),
                            v::ConstantValue::Scalar(v::ScalarValue::I64(scalar.to_i64().unwrap())),
                        ),
                        rustc_middle::ty::IntTy::I128 => (
                            ty::Ty::Integer(ty::IntegerTy::I128),
                            v::ConstantValue::Scalar(v::ScalarValue::I128(
                                scalar.to_i128().unwrap(),
                            )),
                        ),
                    }
                }
                TyKind::Uint(uint_ty) => {
                    match uint_ty {
                        rustc_middle::ty::UintTy::Usize => {
                            // This is a bit annoying: there is no
                            // `to_usize`. For now, we make the hypothesis
                            // that usize is a uint64
                            assert!(std::mem::size_of::<usize>() == 8);
                            return (
                                ty::Ty::Integer(ty::IntegerTy::Usize),
                                v::ConstantValue::Scalar(v::ScalarValue::Usize(
                                    scalar.to_u64().unwrap() as usize,
                                )),
                            );
                        }
                        rustc_middle::ty::UintTy::U8 => (
                            ty::Ty::Integer(ty::IntegerTy::U8),
                            v::ConstantValue::Scalar(v::ScalarValue::U8(scalar.to_u8().unwrap())),
                        ),
                        rustc_middle::ty::UintTy::U16 => (
                            ty::Ty::Integer(ty::IntegerTy::U16),
                            v::ConstantValue::Scalar(v::ScalarValue::U16(scalar.to_u16().unwrap())),
                        ),
                        rustc_middle::ty::UintTy::U32 => (
                            ty::Ty::Integer(ty::IntegerTy::U32),
                            v::ConstantValue::Scalar(v::ScalarValue::U32(scalar.to_u32().unwrap())),
                        ),
                        rustc_middle::ty::UintTy::U64 => (
                            ty::Ty::Integer(ty::IntegerTy::U64),
                            v::ConstantValue::Scalar(v::ScalarValue::U64(scalar.to_u64().unwrap())),
                        ),
                        rustc_middle::ty::UintTy::U128 => (
                            ty::Ty::Integer(ty::IntegerTy::U128),
                            v::ConstantValue::Scalar(v::ScalarValue::U128(
                                scalar.to_u128().unwrap(),
                            )),
                        ),
                    }
                }
                TyKind::Float(_) => {
                    // We don't support floating point numbers:
                    // this should have been detected and eliminated
                    // before.
                    unreachable!();
                }
                _ => {
                    // The remaining types should not be used for constants, or
                    // should have been filtered by the caller.
                    error!("unexpected type: {:?}", ty.kind());
                    unreachable!();
                }
            }
        }
        mir::interpret::ConstValue::Slice {
            data: _,
            start: _,
            end: _,
        } => {
            unimplemented!();
        }
        mir::interpret::ConstValue::ByRef {
            alloc: _,
            offset: _,
        } => {
            unimplemented!();
        }
    }
}

/// Translate a constant value in the case it is not a scalar constant
/// ([ConstValue::Slice] and [ConstValue::ByRef]).
fn translate_operand_constant_value_non_scalar<'tcx, 'ctx, 'ctx1>(
    tcx: TyCtxt<'tcx>,
    bt_ctx: &BodyTransContext<'ctx, 'ctx1>,
    ty: &Ty<'tcx>,
    value: &mir::interpret::ConstValue<'tcx>,
) -> (ty::ETy, e::OperandConstantValue) {
    match value {
        mir::interpret::ConstValue::Scalar(_) => {
            // Should have been treated elsewhere
            unreachable!();
        }
        mir::interpret::ConstValue::ByRef {
            alloc: _,
            offset: _,
        } => {
            // If we are here, the constant is likely a tuple or an enumration
            // variant.
            // We use [destructure_const] to destructure the constant
            // We need a param_env: we use the function def id as a dummy id...
            let param_env = tcx.param_env(bt_ctx.def_id);
            // I have to clone some values: it is a bit annoying, but I manage
            // to get the lifetimes working otherwise...
            let cvalue = rustc_middle::ty::Const::from_value(tcx, value.clone(), ty.clone());
            let param_env_and_const = rustc_middle::ty::ParamEnvAnd {
                param_env,
                value: cvalue,
            };
            let dc = tcx.destructure_const(param_env_and_const);
            trace!("{:?}", dc);

            // Match on the type to destructure
            match ty.kind() {
                TyKind::Tuple(substs) => {
                    let (region_params, type_params) =
                        translate_subst_in_body(tcx, bt_ctx, None, substs).unwrap();
                    assert!(region_params.is_empty());
                    trace!("{:?}", type_params);

                    // Check that there are as many fields as there are constant
                    // values in the destructured constant
                    assert!(type_params.len() == dc.fields.len());

                    let mut field_tys: Vector<ty::ETy> = Vector::new();
                    let mut field_values: Vector<e::OperandConstantValue> = Vector::new();

                    // Iterate over the fields
                    for (field, field_trans_ty) in dc.fields.iter().zip(type_params.iter()) {
                        let (field_ty, field_v) = match &field.val {
                            ConstKind::Value(v) => (&field.ty, v),
                            _ => {
                                unreachable!()
                            }
                        };
                        let (field_trans_ty1, field_cv) =
                            translate_operand_constant_value(tcx, bt_ctx, field_ty, field_v);
                        assert!(field_trans_ty1 == *field_trans_ty);

                        field_tys.push_back(field_trans_ty1);
                        field_values.push_back(field_cv);
                    }

                    // Return
                    let ty = ty::Ty::Adt(ty::TypeId::Tuple, Vector::new(), field_tys);
                    let value = e::OperandConstantValue::Adt(Option::None, field_values);
                    (ty, value)
                }
                TyKind::Adt(_, _) => {
                    // Following tests, it seems rustc doesn't introduce constants
                    // when initializing ADTs, only when initializing tuples.
                    // Anyway, our `OperandConstantValue` handles all cases
                    // so updating the code to handle ADTs in a general manner
                    // wouldn't be a problem.
                    error!("unexpected type: Adt");
                    unreachable!();
                }
                _ => {
                    // The remaining types should not be used for constants, or
                    // should have been filtered by the caller.
                    error!("unexpected type: {:?}", ty.kind());
                    unreachable!();
                }
            }
        }
        mir::interpret::ConstValue::Slice {
            data: _,
            start: _,
            end: _,
        } => {
            unimplemented!();
        }
    }
}

/// Translate a constant operand
fn translate_operand_constant_value<'tcx, 'ctx, 'ctx1>(
    tcx: TyCtxt<'tcx>,
    bt_ctx: &BodyTransContext<'ctx, 'ctx1>,
    ty: &Ty<'tcx>,
    value: &mir::interpret::ConstValue<'tcx>,
) -> (ty::ETy, e::OperandConstantValue) {
    trace!("{:?}", value);
    match value {
        mir::interpret::ConstValue::Scalar(_scalar) => {
            // The documentation explicitly says not to match on a
            // salar. We match on the type and convert the value
            // following this, by calling the appropriate `to_*`
            // method
            match ty.kind() {
                TyKind::Bool | TyKind::Char | TyKind::Int(_) | TyKind::Uint(_) => {
                    let (ty, cv) = translate_operand_constant_value_constant_value(ty, value);
                    (ty, e::OperandConstantValue::ConstantValue(cv))
                }
                TyKind::Float(_) => {
                    // We don't support floating point numbers:
                    // this should have been detected and eliminated
                    // before.
                    unreachable!();
                }
                TyKind::Adt(adt_def, substs) => {
                    // It seems we can have ADTs when there is only one
                    // variant, and this variant doesn't take parameters
                    let ft_ctx = &bt_ctx.ft_ctx;

                    // Retrieve the definition
                    let id = ft_ctx.ordered.type_rid_to_id.get(&adt_def.did).unwrap();
                    let def = ft_ctx.type_defs.get_type_def(*id).unwrap();

                    // Check that there is only one variant, with no fields
                    // and no parameters. Construct the value at the same time.
                    assert!(substs.len() == 0);
                    assert!(def.type_params.len() == 0);
                    let variant_id = match &def.kind {
                        ty::TypeDeclKind::Enum(variants) => {
                            assert!(variants.len() == 1);
                            Option::Some(ty::VariantId::ZERO)
                        }
                        ty::TypeDeclKind::Struct(_) => Option::None,
                        ty::TypeDeclKind::Opaque => {
                            unreachable!("Can't analyze a constant value built from an opaque type")
                        }
                    };

                    let ty = ty::Ty::Adt(ty::TypeId::Adt(*id), Vector::new(), Vector::new());
                    let v = e::OperandConstantValue::Adt(variant_id, Vector::new());
                    (ty, v)
                }
                TyKind::Tuple(substs) => {
                    // There can be tuple([]) for unit
                    assert!(substs.len() == 0);
                    let ty = ty::Ty::Adt(ty::TypeId::Tuple, Vector::new(), Vector::new());
                    let cv = e::OperandConstantValue::Adt(Option::None, Vector::new());
                    (ty, cv)
                }
                TyKind::Never => {
                    // Not sure what to do here
                    unimplemented!();
                }
                _ => {
                    // The remaining types should not be used for constants
                    error!(
                        "unexpected type: {:?}, for constant value: {:?}",
                        ty.kind(),
                        value
                    );
                    unreachable!();
                }
            }
        }
        mir::interpret::ConstValue::Slice {
            data: _,
            start: _,
            end: _,
        }
        | mir::interpret::ConstValue::ByRef {
            alloc: _,
            offset: _,
        } => {
            // Note that we should get here only for types like string, tuple, etc.
            translate_operand_constant_value_non_scalar(tcx, bt_ctx, ty, value)
        }
    }
}

/// Translate a constant
fn translate_operand_constant<'tcx, 'ctx, 'ctx1>(
    tcx: TyCtxt<'tcx>,
    bt_ctx: &BodyTransContext<'ctx, 'ctx1>,
    constant: &mir::Constant<'tcx>,
) -> (ty::ETy, e::OperandConstantValue) {
    trace!("{:?}", constant);
    use std::ops::Deref;
    let constant = &constant.deref();
    match constant.literal {
        // This is the "normal" constant case
        mir::ConstantKind::Ty(c) => match c.val {
            rustc_middle::ty::ConstKind::Value(cvalue) => {
                translate_operand_constant_value(tcx, bt_ctx, &c.ty, &cvalue)
            }
            rustc_middle::ty::ConstKind::Unevaluated(unev) => {
                // Evaluate the constant
                // We need a param_env: we use the function def id as a dummy id...
                let param_env = tcx.param_env(bt_ctx.def_id);
                let evaluated = tcx.const_eval_resolve(param_env, unev, Option::None);
                match evaluated {
                    std::result::Result::Ok(c) => {
                        let ty = constant.ty();
                        translate_operand_constant_value(tcx, bt_ctx, &ty, &c)
                    }
                    std::result::Result::Err(_) => {
                        unreachable!("Could not evaluate an unevaluated constant");
                    }
                }
            }
            rustc_middle::ty::ConstKind::Param(_)
            | rustc_middle::ty::ConstKind::Infer(_)
            | rustc_middle::ty::ConstKind::Bound(_, _)
            | rustc_middle::ty::ConstKind::Placeholder(_)
            | rustc_middle::ty::ConstKind::Error(_) => {
                unreachable!("Unexpected: {:?}", constant.literal);
            }
        },
        // I'm not sure what this is about: the documentation is weird.
        mir::ConstantKind::Val(_value, _ty) => {
            unimplemented!();
        }
    }
}

/// Translate an operand
fn translate_operand<'tcx, 'ctx, 'ctx1>(
    tcx: TyCtxt<'tcx>,
    bt_ctx: &BodyTransContext<'ctx, 'ctx1>,
    operand: &mir::Operand<'tcx>,
) -> e::Operand {
    trace!();
    match operand {
        Operand::Copy(place) => e::Operand::Copy(translate_place(bt_ctx, place)),
        Operand::Move(place) => e::Operand::Move(translate_place(bt_ctx, place)),
        Operand::Constant(constant) => {
            let (ty, constant) = translate_operand_constant(tcx, bt_ctx, constant);
            e::Operand::Constant(ty, constant)
        }
    }
}

/// Translate an operand which should be `move b.0` where `b` is a box (such
/// operands are sometimes introduced here and there).
/// This is a degenerate case where we can't use
/// [`translate_operand`](translate_operand) on this kind of operands because
/// it will panic, due to the fact that we precisely track the type of the
/// values we go through during the path exploration.
/// We also prefer not to tweak `translate_operand` to account for this
/// ad-hoc behaviour (which comes from the fact that we abstract boxes, while
/// the rust compiler is too precise when manipulating those boxes, which
/// reveals implementation details).
fn translate_move_box_first_projector_operand<'tcx, 'ctx, 'ctx1>(
    bt_ctx: &BodyTransContext<'ctx, 'ctx1>,
    operand: &mir::Operand<'tcx>,
) -> e::Operand {
    trace!();
    match operand {
        Operand::Move(place) => {
            let var_id = bt_ctx.get_local(&place.local).unwrap();

            // Sanity check
            let var = bt_ctx.get_var_from_id(var_id).unwrap();
            assert!(var.ty.is_box());

            assert!(place.projection.len() == 1);
            let proj_elem = place.projection.get(0).unwrap();
            match proj_elem {
                mir::ProjectionElem::Field(field, _) => {
                    assert!(field.as_usize() == 0);
                }
                _ => {
                    unreachable!();
                }
            }
            e::Operand::Move(e::Place {
                var_id,
                projection: e::Projection::new(),
            })
        }
        _ => {
            unreachable!();
        }
    }
}

/// Translate a `BorrowKind`
fn translate_borrow_kind(borrow_kind: mir::BorrowKind) -> e::BorrowKind {
    match borrow_kind {
        mir::BorrowKind::Shared => {
            return e::BorrowKind::Shared;
        }
        mir::BorrowKind::Mut {
            allow_two_phase_borrow,
        } => {
            if allow_two_phase_borrow {
                return e::BorrowKind::TwoPhaseMut;
            } else {
                return e::BorrowKind::Mut;
            }
        }
        mir::BorrowKind::Unique => {
            unimplemented!();
        }
        mir::BorrowKind::Shallow => {
            unimplemented!();
        }
    }
}

fn translate_variant_id(id: rustc_target::abi::VariantIdx) -> VariantId::Id {
    VariantId::Id::new(id.as_usize())
}

fn translate_field(id: mir::Field) -> FieldId::Id {
    FieldId::Id::new(id.as_usize())
}

fn translate_binaryop_kind(binop: mir::BinOp) -> e::BinOp {
    use mir::BinOp;
    match binop {
        BinOp::BitXor => e::BinOp::BitXor,
        BinOp::BitAnd => e::BinOp::BitAnd,
        BinOp::BitOr => e::BinOp::BitOr,
        BinOp::Eq => e::BinOp::Eq,
        BinOp::Lt => e::BinOp::Lt,
        BinOp::Le => e::BinOp::Le,
        BinOp::Ne => e::BinOp::Ne,
        BinOp::Ge => e::BinOp::Ge,
        BinOp::Gt => e::BinOp::Gt,
        BinOp::Div => e::BinOp::Div,
        BinOp::Rem => e::BinOp::Rem,
        BinOp::Add => e::BinOp::Add,
        BinOp::Sub => e::BinOp::Sub,
        BinOp::Mul => e::BinOp::Mul,
        BinOp::Shl => e::BinOp::Shl,
        BinOp::Shr => e::BinOp::Shr,
        _ => {
            unreachable!();
        }
    }
}

fn translate_unaryop_kind(binop: mir::UnOp) -> e::UnOp {
    use mir::UnOp;
    match binop {
        UnOp::Not => e::UnOp::Not,
        UnOp::Neg => e::UnOp::Neg,
    }
}

/// Translate an rvalue
fn translate_rvalue<'tcx, 'ctx, 'ctx1>(
    tcx: TyCtxt<'tcx>,
    bt_ctx: &BodyTransContext<'ctx, 'ctx1>,
    rvalue: &mir::Rvalue<'tcx>,
) -> e::Rvalue {
    use std::ops::Deref;
    match rvalue {
        mir::Rvalue::Use(operand) => e::Rvalue::Use(translate_operand(tcx, bt_ctx, operand)),
        mir::Rvalue::Repeat(_operand, _const) => {
            // [x; 32]
            unimplemented!();
        }
        mir::Rvalue::Ref(_region, borrow_kind, place) => {
            let place = translate_place(bt_ctx, place);
            let borrow_kind = translate_borrow_kind(*borrow_kind);
            e::Rvalue::Ref(place, borrow_kind)
        }
        mir::Rvalue::ThreadLocalRef(_) => {
            unreachable!();
        }
        mir::Rvalue::AddressOf(_, _) => {
            unreachable!();
        }
        mir::Rvalue::Len(_place) => {
            unimplemented!();
        }
        mir::Rvalue::Cast(_, _, _) => {
            unimplemented!();
        }
        mir::Rvalue::BinaryOp(binop, operands) | mir::Rvalue::CheckedBinaryOp(binop, operands) => {
            // We merge checked and unchecked binary operations
            let (left, right) = operands.deref();
            e::Rvalue::BinaryOp(
                translate_binaryop_kind(*binop),
                translate_operand(tcx, bt_ctx, left),
                translate_operand(tcx, bt_ctx, right),
            )
        }
        mir::Rvalue::NullaryOp(nullop, _ty) => {
            trace!("NullOp: {:?}", nullop);
            // Nullary operations are very low-level and shouldn't be necessary
            // unless one needs to write unsafe code.
            unreachable!();
        }
        mir::Rvalue::UnaryOp(unop, operand) => e::Rvalue::UnaryOp(
            translate_unaryop_kind(*unop),
            translate_operand(tcx, bt_ctx, operand),
        ),
        mir::Rvalue::Discriminant(place) => e::Rvalue::Discriminant(translate_place(bt_ctx, place)),
        mir::Rvalue::Aggregate(aggregate_kind, operands) => {
            // It seems this instruction is not present in certain passes:
            // for example, it seems it is not used in optimized MIR, where
            // ADT initialization is split into several instructions, for
            // instance:
            // ```
            // p = Pair { x:xv, y:yv };
            // ```
            // Might become:
            // ```
            // p.x = x;
            // p.y = yv;
            // ```
            //
            // Our semantics is designed to handle both cases (aggregated and
            // non-aggregated initialization).

            // First translate the operands
            let operands_t: Vec<e::Operand> = operands
                .iter()
                .map(|op| translate_operand(tcx, bt_ctx, op))
                .collect();

            match aggregate_kind.deref() {
                mir::AggregateKind::Array(_ty) => {
                    unimplemented!();
                }
                mir::AggregateKind::Tuple => {
                    e::Rvalue::Aggregate(e::AggregateKind::Tuple, operands_t)
                }
                mir::AggregateKind::Adt(
                    adt_id,
                    variant_idx,
                    substs,
                    user_annotation,
                    field_index,
                ) => {
                    trace!("{:?}", rvalue);
                    assert!(adt_id.is_local());

                    // Not sure what those two parameters are used for, so
                    // panicking if they are not none (to catch a use case).
                    // I'm not even sure that "field_index" is a proper name:
                    // the documentation seems outdated (it says the 4th parameter
                    // is a field index, while it makes more sense for it to be
                    // the 5th, and I don't know how I should use it anyway).
                    assert!(user_annotation.is_none());
                    assert!(field_index.is_none());

                    // Translate the substitution
                    let (region_params, type_params) =
                        translate_subst_in_body(tcx, bt_ctx, None, substs).unwrap();

                    // Retrieve the definition
                    let id_t = *bt_ctx.ft_ctx.ordered.type_rid_to_id.get(adt_id).unwrap();
                    let def = bt_ctx.get_type_defs().get_type_def(id_t).unwrap();

                    assert!(region_params.len() == def.region_params.len());
                    assert!(type_params.len() == def.type_params.len());

                    let variant_id = match &def.kind {
                        ty::TypeDeclKind::Enum(variants) => {
                            let variant_id = translate_variant_id(*variant_idx);
                            assert!(
                                operands_t.len() == variants.get(variant_id).unwrap().fields.len()
                            );

                            Some(variant_id)
                        }
                        ty::TypeDeclKind::Struct(_) => {
                            assert!(variant_idx.as_usize() == 0);
                            None
                        }
                        ty::TypeDeclKind::Opaque => {
                            unreachable!("Can't build an aggregate from an opaque type")
                        }
                    };
                    let akind = e::AggregateKind::Adt(id_t, variant_id, region_params, type_params);

                    e::Rvalue::Aggregate(akind, operands_t)
                }
                mir::AggregateKind::Closure(_def_id, _subst) => {
                    unimplemented!();
                }
                mir::AggregateKind::Generator(_def_id, _subst, _movability) => {
                    unimplemented!();
                }
            }
        }
        mir::Rvalue::ShallowInitBox(_, _) => {
            unimplemented!();
        }
    }
}

/// Translate a statement
///
/// We return an option, because we ignore some statements (`Nop`, `StorageLive`...)
fn translate_statement<'tcx, 'ctx, 'ctx1>(
    tcx: TyCtxt<'tcx>,
    bt_ctx: &BodyTransContext<'ctx, 'ctx1>,
    statement: &Statement<'tcx>,
) -> Result<Option<ast::Statement>> {
    trace!("About to translate statement (MIR) {:?}", statement);

    use ::std::ops::Deref;

    match &statement.kind {
        StatementKind::Assign(assign) => {
            let (place, rvalue) = assign.deref();
            let t_place = translate_place(bt_ctx, place);
            let t_rvalue = translate_rvalue(tcx, bt_ctx, rvalue);

            Ok(Some(ast::Statement::Assign(t_place, t_rvalue)))
        }
        StatementKind::FakeRead(info) => {
            let (_read_cause, place) = info.deref();
            let t_place = translate_place(bt_ctx, place);

            Ok(Some(ast::Statement::FakeRead(t_place)))
        }
        StatementKind::SetDiscriminant {
            place,
            variant_index,
        } => {
            let t_place = translate_place(bt_ctx, place);
            let variant_id = translate_variant_id(*variant_index);
            Ok(Some(ast::Statement::SetDiscriminant(t_place, variant_id)))
        }
        StatementKind::StorageLive(_) => {
            // For now we ignore StorageLive
            Ok(None)
        }
        StatementKind::StorageDead(local) => {
            let var_id = bt_ctx.get_local(local).unwrap();
            Ok(Some(ast::Statement::StorageDead(var_id)))
        }
        StatementKind::CopyNonOverlapping(_) => {
            // The program should have been rejected before
            error!("Copy non overlapping");
            unreachable!();
        }
        StatementKind::Retag(_, _) => {
            // This is for the stacked borrows
            trace!("retag");
            Ok(None)
        }
        StatementKind::AscribeUserType(_, _) => {
            trace!("AscribedUserType");
            // We ignore those: they are just used by the type checker.
            // Note that this instruction is used only in certain passes
            // (it is not present in optimized MIR for instance).
            Ok(None)
        }
        StatementKind::Coverage(_) => {
            unimplemented!();
        }
        StatementKind::Nop => {
            // We ignore this statement
            Ok(None)
        }
    }
}

/// Translate a terminator
fn translate_terminator<'tcx, 'ctx, 'ctx1>(
    tcx: TyCtxt<'tcx>,
    bt_ctx: &mut BodyTransContext<'ctx, 'ctx1>,
    body: &Body<'tcx>,
    terminator: &Terminator<'tcx>,
) -> Result<ast::Terminator> {
    trace!("About to translate terminator (MIR) {:?}", terminator);

    match &terminator.kind {
        TerminatorKind::Goto { target } => {
            let target = translate_basic_block(tcx, bt_ctx, body, *target)?;
            Ok(ast::Terminator::Goto { target })
        }
        TerminatorKind::SwitchInt {
            discr,
            switch_ty,
            targets,
        } => {
            // Translate the type
            let switch_ty = translate_ety(tcx, bt_ctx, switch_ty)?;

            // Translate the operand which gives the discriminant
            let discr = translate_operand(tcx, bt_ctx, discr);

            // Translate the switch targets
            let targets = translate_switch_targets(tcx, bt_ctx, body, &switch_ty, targets)?;

            Ok(ast::Terminator::Switch { discr, targets })
        }
        TerminatorKind::Resume => {
            // This is used to correctly unwind. We shouldn't get there: if
            // we panic, the state gets stuck.
            unreachable!();
        }
        TerminatorKind::Abort => {
            // TODO: we will translate this to `ast::Terminator::Abort`,
            // but I want to see in which situations Abort appears.
            unimplemented!();
        }
        TerminatorKind::Return => Ok(ast::Terminator::Return),
        TerminatorKind::Unreachable => Ok(ast::Terminator::Unreachable),
        TerminatorKind::Drop {
            place,
            target,
            unwind: _,
        } => Ok(ast::Terminator::Drop {
            place: translate_place(bt_ctx, place),
            target: translate_basic_block(tcx, bt_ctx, body, *target)?,
        }),
        TerminatorKind::DropAndReplace {
            place: _,
            value: _,
            target: _,
            unwind: _,
        } => {
            unimplemented!();
        }
        TerminatorKind::Call {
            func,
            args,
            destination,
            cleanup: _, // Note that the state gets stuck if we need to unwind
            from_hir_call: _,
            fn_span: _,
        } => {
            trace!("Call: func: {:?}", func);
            translate_function_call(tcx, bt_ctx, body, func, args, destination)
        }
        TerminatorKind::Assert {
            cond,
            expected,
            msg: _, // We ignore the message: if we panic, the state gets stuck
            target,
            cleanup: _, // If we panic, the state gets stuck: we don't need to model cleanup
        } => {
            let cond = translate_operand(tcx, bt_ctx, cond);
            let target = translate_basic_block(tcx, bt_ctx, body, *target)?;
            Ok(ast::Terminator::Assert {
                cond,
                expected: *expected,
                target,
            })
        }
        TerminatorKind::Yield {
            value: _,
            resume: _,
            resume_arg: _,
            drop: _,
        } => {
            unimplemented!();
        }
        TerminatorKind::GeneratorDrop => {
            unimplemented!();
        }
        TerminatorKind::FalseEdge {
            real_target,
            imaginary_target,
        } => {
            trace!(
                "False edge:\n- real target ({:?}):\n{:?}\n- imaginary target ({:?}):\n{:?}",
                real_target,
                body.basic_blocks().get(*real_target).unwrap(),
                imaginary_target,
                body.basic_blocks().get(*imaginary_target).unwrap(),
            );

            // False edges are used to make the borrow checker a bit conservative.
            // We translate them as Gotos.
            // Also note that they are used in some passes, and not in some others
            // (they are present in mir_promoted, but not mir_optimized).
            let target = translate_basic_block(tcx, bt_ctx, body, *real_target)?;
            Ok(ast::Terminator::Goto { target })
        }
        TerminatorKind::FalseUnwind {
            real_target: _,
            unwind: _,
        } => {
            unimplemented!();
        }
        TerminatorKind::InlineAsm {
            template: _,
            operands: _,
            options: _,
            line_spans: _,
            destination: _,
            cleanup: _,
        } => {
            // This case should have been eliminated during the registration phase
            unreachable!();
        }
    }
}

/// Translate switch targets
fn translate_switch_targets<'tcx, 'ctx, 'ctx1>(
    tcx: TyCtxt<'tcx>,
    bt_ctx: &mut BodyTransContext<'ctx, 'ctx1>,
    body: &Body<'tcx>,
    switch_ty: &ty::ETy,
    targets: &mir::SwitchTargets,
) -> Result<ast::SwitchTargets> {
    let targets_vec: Vec<(u128, BasicBlock)> = targets.iter().map(|(v, b)| (v, b)).collect();

    match switch_ty {
        ty::Ty::Bool => {
            // This is an: `if ... then ... else ...`
            assert!(targets_vec.len() == 1);
            // It seems the block targets are inverted
            let (test_val, otherwise_block) = targets_vec[0];

            assert!(test_val == 0);

            // It seems the block targets are inverted
            let if_block = translate_basic_block(tcx, bt_ctx, body, targets.otherwise())?;
            let otherwise_block = translate_basic_block(tcx, bt_ctx, body, otherwise_block)?;

            return Ok(ast::SwitchTargets::If(if_block, otherwise_block));
        }
        ty::Ty::Integer(int_ty) => {
            // This is a: switch(int).
            // Convert all the test values to the proper values.
            let mut targets_map: LinkedHashMap<v::ScalarValue, ast::BlockId::Id> =
                LinkedHashMap::new();
            for (v, tgt) in targets_vec {
                let v = if int_ty.is_signed() {
                    v::ScalarValue::from_int(*int_ty, v as i128).unwrap()
                } else {
                    v::ScalarValue::from_uint(*int_ty, v).unwrap()
                };
                let tgt = translate_basic_block(tcx, bt_ctx, body, tgt)?;
                assert!(!targets_map.contains_key(&v));
                targets_map.insert(v, tgt);
            }
            let otherwise_block = translate_basic_block(tcx, bt_ctx, body, targets.otherwise())?;

            return Ok(ast::SwitchTargets::SwitchInt(
                *int_ty,
                targets_map,
                otherwise_block,
            ));
        }
        _ => {
            trace!("Unexpected switch_ty: {}", switch_ty.variant_name());
            unreachable!();
        }
    }
}

/// Small utility used by [`execute_function_call`](execute_function_call).
/// Return the `DefId` of the function referenced by an operand, with the
/// parameters substitution.
/// The `Operand` comes from a `TerminatorKind::Call`.
/// Only supports calls to top-level functions (which are considered as constants
/// by rustc); doesn't support closures for now.
fn get_function_from_operand<'tcx>(
    func: &Operand<'tcx>,
) -> (DefId, &'tcx rustc_middle::ty::subst::InternalSubsts<'tcx>) {
    trace!("func: {:?}", func);

    use std::ops::Deref;
    // Match on the func operand: it should be a constant as we don't support
    // closures for now.
    match func {
        mir::Operand::Constant(c) => {
            let c = c.deref();
            // I'm not sure why the literal should be a `ConstantKind::Ty`,
            // but it is the case in practice.
            match &c.literal {
                mir::ConstantKind::Ty(c) => {
                    // The type of the constant should be a FnDef, allowing
                    // us to retrieve the function's identifier and instantiation.
                    assert!(c.ty.is_fn());
                    match c.ty.kind() {
                        mir_ty::TyKind::FnDef(def_id, subst) => (*def_id, subst),
                        _ => {
                            unreachable!();
                        }
                    }
                }
                mir::ConstantKind::Val(_val, _ty) => {
                    unreachable!();
                }
            }
        }
        mir::Operand::Move(_place) | mir::Operand::Copy(_place) => {
            unimplemented!();
        }
    }
}

/// A function definition can be top-level, or can be defined in an `impl`
/// block. In this case, we might want to retrieve the type for which the
/// impl block was defined. This function returns this type's def id if
/// the function def id given as input was defined in an impl block, and
/// returns `None` otherwise.
///
/// For instance, when translating `bar` below:
/// ```
/// impl Foo {
///     fn bar(...) -> ... { ... }
/// }
/// ```
/// we might want to know that `bar` is actually defined in one of `Foo`'s impl
/// blocks (and retrieve `Foo`'s identifier).
///
/// TODO: this might gives us the same as TyCtxt::generics_of
fn get_impl_parent_type_def_id(tcx: TyCtxt, def_id: DefId) -> Option<DefId> {
    // Retrieve the definition def id
    let def_key = tcx.def_key(def_id);

    // Reconstruct the parent def id: it's the same as the function's def id,
    // at the exception of the index.
    let parent_def_id = DefId {
        index: def_key.parent.unwrap(),
        ..def_id
    };

    // Retrieve the parent's key
    let parent_def_key = tcx.def_key(parent_def_id);

    // Match on the parent key
    let parent = match parent_def_key.disambiguated_data.data {
        rustc_hir::definitions::DefPathData::Impl => {
            // Parent is an impl block! Retrieve the type definition (it
            // seems that `type_of` is the only way of getting it)
            let parent_type = tcx.type_of(parent_def_id);

            // The parent type should be ADT
            match parent_type.kind() {
                rustc_middle::ty::TyKind::Adt(adt_def, _) => Some(adt_def.did),
                _ => {
                    unreachable!();
                }
            }
        }
        _ => {
            // Not an impl block
            None
        }
    };

    // TODO: checking
    assert!(parent == tcx.generics_of(def_id).parent);

    parent
}

/// Translate a function call statement.
/// Note that `body` is the body of the function being translated, not of the
/// function referenced in the function call: we need it in order to translate
/// the blocks we go to after the function call returns.
fn translate_function_call<'tcx, 'ctx, 'ctx1>(
    tcx: TyCtxt<'tcx>,
    bt_ctx: &mut BodyTransContext<'ctx, 'ctx1>,
    body: &mir::Body<'tcx>,
    func: &Operand<'tcx>,
    args: &Vec<Operand<'tcx>>,
    destination: &Option<(Place<'tcx>, BasicBlock)>,
) -> Result<ast::Terminator> {
    trace!();

    // Translate the function operand - should be a constant: we don't
    // support closures for now
    trace!("func: {:?}", func);

    // Retrieve the function's identifier and instantiation
    let (def_id, substs) = get_function_from_operand(func);

    // Translate the name to check if is is `core::panicking::panic`
    let name = function_def_id_to_name(tcx, def_id);

    // If the call is `panic!`, then the destination is `None`.
    // I don't know in which other cases it can be `None`.
    if name.equals_ref_name(&assumed::PANIC_NAME)
        || name.equals_ref_name(&assumed::BEGIN_PANIC_NAME)
    {
        assert!(!def_id.is_local());
        assert!(destination.is_none());

        // We ignore the arguments
        Ok(ast::Terminator::Panic)
    } else {
        assert!(destination.is_some());
        let destination = destination.unwrap();

        // Translate the destination
        let (lval, next_block) = destination;
        let lval = translate_place(&bt_ctx, &lval);
        let next_block = translate_basic_block(tcx, bt_ctx, body, next_block)?;

        // There is something annoying: when going to MIR, the rust compiler
        // sometimes introduces very low-level functions, which we need to
        // catch early - in particular, before we start translating types and
        // arguments, because we won't be able to translate some of them.
        if name.equals_ref_name(&assumed::BOX_FREE_NAME) {
            assert!(!def_id.is_local());

            // This deallocates a box.
            // It should have two type parameters:
            // - the type of the boxed value
            // - the type of a global allocator (which we ignore)
            // The arguments should be of the form:
            // - `move b.0` (the allocated value)
            // - `move b.1` (the global allocated)
            // where b is of type `Box` (boxes are pairs actually)
            // We replace that with: `move b`
            assert!(substs.len() == 2);
            assert!(args.len() == 2);

            // Translate the type parameter
            let ty = substs.get(0).unwrap().expect_ty();
            let t_ty = translate_ety(tcx, bt_ctx, &ty)?;

            // Translate the first argument - note that we use a special
            // function to translate it: the operand should be of the form:
            // `move b.0`, and if it is the case it will return `move b`
            let arg = &args[0];
            let t_arg = translate_move_box_first_projector_operand(bt_ctx, arg);

            // Return
            Ok(ast::Terminator::Call {
                func: ast::FunId::Assumed(ast::AssumedFunId::BoxFree),
                region_params: vec![],
                type_params: vec![t_ty],
                args: vec![t_arg],
                dest: lval,
                target: next_block,
            })
        } else {
            // Retrieve the lists of used parameters, in case of non-local
            // definitions
            let (used_type_params, used_args) = if def_id.is_local() {
                (Option::None, Option::None)
            } else {
                match assumed::function_to_info(&name) {
                    Option::None => (Option::None, Option::None),
                    Option::Some(used) => (
                        Option::Some(used.used_type_params),
                        Option::Some(used.used_args),
                    ),
                }
            };

            // Translate the type parameters
            let (region_params, type_params) =
                translate_subst_in_body(tcx, bt_ctx, used_type_params, substs)?;

            // Translate the arguments
            let args = translate_arguments(tcx, bt_ctx, used_args, args);

            // Retrieve the function identifier
            // - this is a local function, in which case we need to retrieve the
            //   function id by doing a lookup
            // - this is a non-local function, in which case there is a special
            //   treatment: we need to check if it benefits from primitive support
            if def_id.is_local() {
                // Retrieve the def id
                let def_id = bt_ctx.ft_ctx.get_def_id_from_rid(def_id).unwrap();

                let func = ast::FunId::Local(def_id);

                Ok(ast::Terminator::Call {
                    func,
                    region_params,
                    type_params,
                    args,
                    dest: lval,
                    target: next_block,
                })
            } else {
                // Non local function.
                // Note that there are subtleties with regards to the way types parameters
                // are translated, because some functions are actually traits, where the
                // types are used for the resolution. For instance, the following:
                // `core::ops::deref::Deref::<alloc::boxed::Box<T>>::deref`
                // is translated to:
                // `box_deref<T>`
                // (the type parameter is not `Box<T>` but `T`).
                translate_non_local_function_call(
                    tcx,
                    def_id,
                    region_params,
                    type_params,
                    args,
                    lval,
                    next_block,
                )
            }
        }
    }
}

/// Translate a parameter substitution used inside a function body.
///
/// Note that the regions parameters are expected to have been erased.
fn translate_subst_in_body<'tcx, 'ctx, 'ctx1>(
    tcx: TyCtxt<'tcx>,
    bt_ctx: &BodyTransContext<'ctx, 'ctx1>,
    used_params: Option<Vec<bool>>,
    substs: &rustc_middle::ty::subst::InternalSubsts<'tcx>,
) -> Result<(Vec<ty::ErasedRegion>, Vec<ty::ETy>)> {
    let substs: Vec<rustc_middle::ty::subst::GenericArg<'tcx>> = match used_params {
        Option::None => substs.iter().collect(),
        Option::Some(used_params) => {
            assert!(substs.len() == used_params.len());
            substs
                .iter()
                .zip(used_params.into_iter())
                .filter_map(|(param, used)| if used { Some(param) } else { None })
                .collect()
        }
    };

    let mut t_params_regions = Vec::new();
    let mut t_params_tys = Vec::new();
    for param in substs.iter() {
        match param.unpack() {
            rustc_middle::ty::subst::GenericArgKind::Type(param_ty) => {
                // Simply translate the type
                let t_param_ty = translate_ety(tcx, bt_ctx, &param_ty)?;
                t_params_tys.push(t_param_ty);
            }
            rustc_middle::ty::subst::GenericArgKind::Lifetime(region) => {
                t_params_regions.push(translate_erased_region(region));
            }
            rustc_middle::ty::subst::GenericArgKind::Const(_) => {
                unimplemented!();
            }
        }
    }

    return Ok((t_params_regions, t_params_tys));
}

/// Evaluate function arguments in a context, and return the list of computed
/// values.
fn translate_arguments<'tcx, 'ctx, 'ctx1>(
    tcx: TyCtxt<'tcx>,
    bt_ctx: &BodyTransContext<'ctx, 'ctx1>,
    used_args: Option<Vec<bool>>,
    args: &Vec<Operand<'tcx>>,
) -> Vec<e::Operand> {
    let args: Vec<&Operand<'tcx>> = match used_args {
        Option::None => args.iter().collect(),
        Option::Some(used_args) => {
            assert!(args.len() == used_args.len());
            args.iter()
                .zip(used_args.into_iter())
                .filter_map(|(param, used)| if used { Some(param) } else { None })
                .collect()
        }
    };

    let mut t_args: Vec<e::Operand> = Vec::new();
    for arg in args {
        // There should only be moved arguments, or constants
        match arg {
            mir::Operand::Move(_) | mir::Operand::Constant(_) => {
                // OK
            }
            mir::Operand::Copy(_) => {
                unreachable!();
            }
        }

        // Translate
        let op = translate_operand(tcx, bt_ctx, arg);
        t_args.push(op);
    }

    return t_args;
}

/// Translate a non-local function call which is not: panic, begin_panic,
/// box_free (those have a special treatment).
fn translate_non_local_function_call<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    region_params: Vec<ty::ErasedRegion>,
    type_params: Vec<ty::ETy>,
    args: Vec<e::Operand>,
    dest: e::Place,
    target: ast::BlockId::Id,
) -> Result<ast::Terminator> {
    trace!("- def_id: {:?}", def_id,);

    // Translate the function name
    let name = function_def_id_to_name(tcx, def_id);
    trace!("name: {}", name);

    // Check if the function has primitive support, by trying to look up
    // its primitive identifier
    match assumed::get_fun_id_from_name(&name) {
        Option::Some(aid) => {
            // The function is considered primitive

            // Translate the function call
            // Note that some functions are actually traits (deref, index, etc.):
            // we assume that they are called only on a limited set of types
            // (ex.: box, vec...).
            // For those trait functions, we need a custom treatment to retrieve
            // and check the type information.
            // For instance, derefencing boxes generates MIR of the following form:
            // ```
            // _2 = <Box<u32> as Deref>::deref(move _3)
            // ```
            // We have to retrieve the type `Box<u32>` and check that it is of the
            // form `Box<T>` (and we generate `box_deref<u32>`).
            match aid {
                ast::AssumedFunId::Replace
                | ast::AssumedFunId::BoxNew
                | ast::AssumedFunId::VecNew
                | ast::AssumedFunId::VecPush
                | ast::AssumedFunId::VecInsert
                | ast::AssumedFunId::VecLen => Ok(ast::Terminator::Call {
                    func: ast::FunId::Assumed(aid),
                    region_params,
                    type_params,
                    args,
                    dest,
                    target,
                }),
                ast::AssumedFunId::BoxDeref | ast::AssumedFunId::BoxDerefMut => {
                    translate_box_deref(aid, region_params, type_params, args, dest, target)
                }
                ast::AssumedFunId::VecIndex | ast::AssumedFunId::VecIndexMut => {
                    translate_vec_index(aid, region_params, type_params, args, dest, target)
                }
                ast::AssumedFunId::BoxFree => {
                    unreachable!();
                }
            }
        }
        Option::None => {
            // The function is not considered primitive - it is an external
            // dependency
            Ok(ast::Terminator::Call {
                func: ast::FunId::External(name),
                region_params,
                type_params,
                args,
                dest,
                target,
            })
        }
    }
}

/// Translate `std::Deref::deref` or `std::DerefMut::deref_mut` applied
/// on boxes. We need a custom function because it is a trait.
fn translate_box_deref(
    aid: ast::AssumedFunId,
    region_params: Vec<ty::ErasedRegion>,
    type_params: Vec<ty::ETy>,
    args: Vec<e::Operand>,
    dest: e::Place,
    target: ast::BlockId::Id,
) -> Result<ast::Terminator> {
    // Check the arguments
    assert!(region_params.len() == 0);
    assert!(type_params.len() == 1);
    assert!(args.len() == 1);

    // For now we only support deref on boxes
    // Retrieve the boxed value
    let param_ty = type_params.get(0).unwrap(); // should be `Box<...>`
    let boxed_ty = param_ty.as_box();
    if boxed_ty.is_none() {
        panic!(
            "Deref/DerefMut trait applied with parameter {:?} while it is only supported on Box<T> values",
            param_ty
        );
    }
    let boxed_ty = boxed_ty.unwrap();
    let type_params = vec![boxed_ty.clone()];

    Ok(ast::Terminator::Call {
        func: ast::FunId::Assumed(aid),
        region_params,
        type_params,
        args,
        dest,
        target,
    })
}

/// Translate `core::ops::index::{Index,IndexMut}::{index,index_mut}`
/// applied on `Vec`. We need a custom function because it is a trait.
fn translate_vec_index(
    aid: ast::AssumedFunId,
    region_params: Vec<ty::ErasedRegion>,
    type_params: Vec<ty::ETy>,
    args: Vec<e::Operand>,
    dest: e::Place,
    target: ast::BlockId::Id,
) -> Result<ast::Terminator> {
    // Check the arguments
    assert!(region_params.len() == 0);
    assert!(type_params.len() == 1);
    assert!(args.len() == 2);

    // For now we only support index on vectors
    // Retrieve the boxed value
    let param_ty = type_params.get(0).unwrap(); // should be `Vec<...>`
    let param_ty = match param_ty.as_vec() {
        Option::Some(ty) => (ty),
        Option::None => {
            panic!(
            "Index/IndexMut trait applied with parameter {:?} while it is only supported on Vec<T> values",
            param_ty
        );
        }
    };

    let type_params = vec![param_ty.clone()];
    Ok(ast::Terminator::Call {
        func: ast::FunId::Assumed(aid),
        region_params,
        type_params,
        args,
        dest,
        target,
    })
}

/// Small utility
pub(crate) fn check_impl_item<'hir>(impl_item: &rustc_hir::Impl<'hir>) {
    // TODO: make proper error messages
    use rustc_hir::{Constness, Defaultness, ImplPolarity, Unsafety};
    assert!(impl_item.unsafety == Unsafety::Normal);
    // About polarity:
    // [https://doc.rust-lang.org/beta/unstable-book/language-features/negative-impls.html]
    // Not sure about what I should do about it. Should I do anything, actually?
    // This seems useful to enforce some discipline on the user-side, but not
    // necessary for analysis purposes.
    assert!(impl_item.polarity == ImplPolarity::Positive);
    // Note sure what this is about
    assert!(impl_item.defaultness == Defaultness::Final);
    // Note sure what this is about
    assert!(impl_item.constness == Constness::NotConst);
    assert!(impl_item.of_trait.is_none()); // We don't support traits for now
}

/// Translate a function's signature, and initialize a body translation context
/// at the same time - the function signature gives us the list of region and
/// type parameters, that we put in the translation context.
fn translate_function_signature<'tcx, 'ctx, 'ctx1>(
    tcx: TyCtxt<'tcx>,
    types_constraints: &TypesConstraintsMap,
    ft_ctx: &'ctx FunTransContext<'ctx1>,
    def_id: DefId,
) -> (BodyTransContext<'ctx, 'ctx1>, ast::FunSig) {
    // Retrieve the function signature, which includes the lifetimes
    let signature = tcx.fn_sig(def_id);

    // Instantiate the signature's bound region variables (the signature
    // is wrapped in a [`Binder`](rustc_middle::ty::Binder). This is inspired by
    // [`liberate_late_bound_regions`](TyCtx::liberate_late_bound_regions).
    // The rationale is as follows:
    // - it seems liberate_late_bound_regions is a proper way of retrieving
    //   a signature where all the bound variables have been replaced with
    //   free variables, so that we can study it easily (without having, for
    //   instance, to deal with DeBruijn indices)
    // - my understanding of why it is enough to bind late-bound regions: the
    //   early bound regions are not bound here (they are free), because
    //   they reference regions introduced by the `impl` block (if this definition
    //   is defined in an `impl` block - otherwise there are no early bound variables)
    //   while the late bound regions are introduced by the function itself.
    //   For example, in:
    //   ```
    //   impl<'a> Foo<'a> {
    //       fn bar<'b>(...) -> ... { ... }
    //   }
    //   ```
    //   `'a` is early-bound while `'b` is late-bound.
    // - we can't just use `liberate_late_bound_regions`, because we want to know
    //   in which *order* the regions were bound - it is mostly a matter of stability
    //   of the translation: we will have to generate one backward function per
    //   region, and we need to know in which order to introduce those backward
    //   functions.
    //   Actually, `liberate_late_bound_regions` returns a b-tree: maybe the
    //   order between the bound regions is such that when iterating over the
    //   keys of this tree, we iterator over the bound regions in the order in
    //   which they are bound. As we are not too sure about that, we prefer
    //   reimplementing our own function, which is quite simple.

    // We need a body translation context to keep track of all the variables
    let mut bt_ctx = BodyTransContext::new(def_id, ft_ctx);

    // **Sanity checks on the HIR**
    generics::check_function_generics(tcx, def_id);

    // Start by translating the "normal" substitution (which lists the function's
    // parameters). As written above, this substitution contains all the type
    // variables, and the early-bound regions, but not the late-bound ones.
    // TODO: we do something similar in `translate_function`
    let fun_type = tcx.type_of(def_id);
    let substs = match fun_type.kind() {
        TyKind::FnDef(_def_id, substs_ref) => substs_ref,
        _ => {
            unreachable!()
        }
    };

    for param in substs.iter() {
        match param.unpack() {
            rustc_middle::ty::subst::GenericArgKind::Type(param_ty) => {
                // This type should be a param type
                match param_ty.kind() {
                    TyKind::Param(param_ty) => {
                        bt_ctx.push_type_var(param_ty.index, param_ty.name.to_ident_string());
                    }
                    _ => {
                        unreachable!();
                    }
                }
            }
            rustc_middle::ty::subst::GenericArgKind::Lifetime(region) => {
                let name = translate_region_name(region);
                bt_ctx.push_region(*region, name);
            }
            rustc_middle::ty::subst::GenericArgKind::Const(_) => {
                unimplemented!();
            }
        }
    }

    // Instantiate the regions bound in the signature, and generate a mapping
    // while doing so (the mapping uses a linked hash map so that we remember
    // in which order we introduced the regions).
    // Note that replace_late_bound_regions` returns a map from bound regions to
    // regions, but it is unclear whether this map preserves the order in which
    // the regions were introduced (the map is a BTreeMap, so I guess it depends
    // on how the the bound variables were numbered) and it doesn't cost us
    // much to create this mapping ourselves.
    let (signature, late_bound_regions) =
        generics::replace_late_bound_regions(tcx, signature, def_id);

    // Introduce identifiers and translated regions for the late-bound regions
    for (_, region) in &late_bound_regions {
        let name = translate_region_name(region);
        bt_ctx.push_region(**region, name);
    }

    trace!(
        "# Early and late bound regions:\n{}",
        iterator_to_string(&|x: &ty::RegionVar| x.to_string(), bt_ctx.regions.iter())
    );
    trace!(
        "# Type variables:\n{}",
        iterator_to_string(&|x: &ty::TypeVar| x.to_string(), bt_ctx.type_vars.iter())
    );

    // Now that we instantiated all the binders and introduced identifiers for
    // all the variables, we can translate the function's signature.
    let inputs: v::VarId::Vector<ty::RTy> = v::VarId::Vector::from_iter(
        signature
            .inputs()
            .iter()
            .map(|ty| translate_sig_ty(tcx, &bt_ctx, ty).unwrap()),
    );
    let output = translate_sig_ty(tcx, &bt_ctx, &signature.output()).unwrap();

    trace!(
        "# Input variables types:\n{}",
        iterator_to_string(&|x| bt_ctx.format_object(x), inputs.iter())
    );
    trace!("# Output variable type:\n{}", bt_ctx.format_object(&output));

    let sig = ast::FunSig {
        region_params: bt_ctx.regions.clone(),
        num_early_bound_regions: late_bound_regions.len(),
        regions_hierarchy: rh::RegionGroups::new(), // Hierarchy not yet computed
        type_params: bt_ctx.type_vars.clone(),
        inputs,
        output,
    };

    // Analyze the signature to compute the regions hierarchy
    let regions_hierarchy = rh::compute_regions_hierarchy_for_sig(types_constraints, &sig);
    let sig = ast::FunSig {
        regions_hierarchy,
        ..sig
    };

    (bt_ctx, sig)
}

#[derive(Debug, Clone)]
struct ScopeTree<T: Clone> {
    scope: T,
    children: Vec<ScopeTree<T>>,
}

/// Compare the spans of two scopes by inspecting which one starts first.
fn compare_scope_spans(body: &Body, scope1: SourceScope, scope2: SourceScope) -> Ordering {
    // Retrieve the scope data and the spans
    let span1 = body.source_scopes.get(scope1).unwrap().span.data();
    let span2 = body.source_scopes.get(scope2).unwrap().span.data();

    // Compare the low positions - note that we should *never* have equal
    // spans: spans are disjoint.
    let BytePos(lo1) = span1.lo;
    let BytePos(lo2) = span2.lo;

    if lo1 < lo2 {
        Ordering::Less
    } else {
        assert!(lo1 > lo2);
        Ordering::Greater
    }
}

fn build_scope_node(
    body: &Body,
    scopes_to_children: &HashMap<SourceScope, Vec<SourceScope>>,
    scope: SourceScope,
) -> ScopeTree<SourceScope> {
    let children = &scopes_to_children[&scope];
    let mut children = children.clone();

    // Reorder the children, from the scope starting first to the scope starting last.
    children.sort_by(&|s1: &SourceScope, s2: &SourceScope| compare_scope_spans(body, *s1, *s2));

    // Check that the children scopes are disjoint and are included in the parent scope
    let parent_span = body.source_scopes.get(scope).unwrap().span.data();
    let BytePos(parent_lo) = parent_span.lo;
    let BytePos(parent_hi) = parent_span.hi;

    let mut prev_hi = parent_lo;
    for child in &children {
        let child_span = body.source_scopes.get(*child).unwrap().span.data();
        let BytePos(child_lo) = child_span.lo;
        let BytePos(child_hi) = child_span.hi;
        assert!(child_lo >= parent_lo);
        assert!(child_hi <= parent_hi);
        assert!(child_lo >= prev_hi);
        prev_hi = child_hi;
    }

    // Generate the children nodes
    let children = Vec::from_iter(
        children
            .iter()
            .map(|s| build_scope_node(body, scopes_to_children, *s)),
    );

    ScopeTree { scope, children }
}

/// Compute the scope tree of a function body.
///
/// Every node of a scope tree gives a scope identifier and its subscopes.
///
/// TODO: this function is currently not used, but we might use it might become
/// useful at some point, so we better maintain it.
fn build_scope_tree(body: &Body) -> ScopeTree<SourceScope> {
    // Compute the scopes tree: the function body gives us the list of variable
    // scopes, with the relation children -> parent. We use it to compute the
    // tree starting at the top scope (the scope encompassing the whole function)
    // to the children scope.
    // We compute the edges
    // parent -> children.
    // By
    let mut scopes_to_children: HashMap<SourceScope, Vec<SourceScope>> = HashMap::from_iter(
        body.source_scopes
            .indices()
            .map(|scope| (scope, Vec::new())),
    );
    for (scope, scope_data) in body.source_scopes.iter_enumerated() {
        match &scope_data.parent_scope {
            None => (),
            Some(parent_scope) => {
                scopes_to_children
                    .get_mut(parent_scope)
                    .unwrap()
                    .push(scope);
            }
        }
    }

    // Find the top scope, which encompasses the whole function - note that there
    // should be exactly one scope without parents.
    assert!(
        body.source_scopes
            .iter()
            .filter(|s| s.parent_scope.is_none())
            .count()
            == 1
    );

    // The top scope is actually always the scope of id 0, but using that fact
    // seems a bit hacky: the following code combined with the above assert
    // is a lot more general and robust.
    let top_scope = body
        .source_scopes
        .iter_enumerated()
        .find(|(_scope, source_scope)| source_scope.parent_scope.is_none())
        .unwrap();
    let (top_scope, _) = top_scope;

    // Construct the scope tree starting at the top scope
    build_scope_node(body, &scopes_to_children, top_scope)
}

/// Translate one function.
///
/// Note that we don't care whether the function is (mutually) recursive or not:
/// we translate its body to a very close representation.
fn translate_transparent_function(
    tcx: TyCtxt,
    ordered: &OrderedDecls,
    types_constraints: &TypesConstraintsMap,
    type_defs: &ty::TypeDecls,
    fun_defs: &mut ast::FunDefs,
    def_id: ast::FunDefId::Id,
) -> Result<ast::FunDef> {
    trace!("{:?}", def_id);

    let rid = *ordered.fun_id_to_rid.get(&def_id).unwrap();
    trace!("About to translate function:\n{:?}", rid);

    // Initialize the function translation context
    let ft_ctx = FunTransContext {
        ordered: ordered,
        type_defs: type_defs,
        defs: &fun_defs,
    };

    // Translate the function name
    let name = function_def_id_to_name(tcx, rid);

    // Retrieve the MIR body
    let body = crate::get_mir::get_mir_for_def_id(tcx, rid.expect_local());

    // Translate the function signature and initialize the body translation context
    // at the same time (the signature gives us the region and type parameters,
    // that we put in the translation context).
    trace!("Translating function signature");
    let (mut bt_ctx, signature) =
        translate_function_signature(tcx, types_constraints, &ft_ctx, rid);

    // Initialize the local variables
    trace!("Translating the body locals");
    translate_body_locals(tcx, &mut bt_ctx, body)?;

    // Build the scope tree
    let _scope_tree = build_scope_tree(body);

    // Translate the function body
    trace!("Translating the function body");
    translate_transparent_function_body(tcx, &mut bt_ctx, body)?;

    // Return the new function
    // We need to convert the blocks map to an index vector
    let mut blocks = ast::BlockId::Vector::new();
    for (id, block) in bt_ctx.blocks {
        use crate::id_vector::ToUsize;
        // Sanity check to make sure we don't mess with the indices
        assert!(id.to_usize() == blocks.len());
        blocks.push_back(block);
    }
    let fun_def = ast::FunDef {
        def_id,
        name,
        signature,
        arg_count: body.arg_count,
        locals: bt_ctx.vars,
        body: blocks,
    };

    Ok(fun_def)
}

/// Translate one opaque function.
///
/// Opaque functions are:
/// - external functions
/// - local functions flagged as opaque
fn translate_opaque_function(
    tcx: TyCtxt,
    ordered: &OrderedDecls,
    types_constraints: &TypesConstraintsMap,
    type_defs: &ty::TypeDecls,
    fun_defs: &mut ast::FunDefs,
    def_id: ast::FunDefId::Id,
) -> Result<ast::FunDef> {
    trace!("{}", def_id);

    let rid = *ordered.fun_id_to_rid.get(&def_id).unwrap();

    // Translate the function name
    let _name = function_def_id_to_name(tcx, rid);

    // Initialize the function translation context
    let ft_ctx = FunTransContext {
        ordered: ordered,
        type_defs: type_defs,
        defs: &fun_defs,
    };

    // Translate the function signature
    let (_, _signature) = translate_function_signature(tcx, types_constraints, &ft_ctx, rid);

    unimplemented!();
}

/// Translate one function.
///
/// Note that we don't care whether the function is (mutually) recursive or not:
/// we translate its body to a very close representation.
fn translate_function(
    tcx: TyCtxt,
    ordered: &OrderedDecls,
    types_constraints: &TypesConstraintsMap,
    type_defs: &ty::TypeDecls,
    fun_defs: &mut ast::FunDefs,
    def_id: ast::FunDefId::Id,
) -> Result<ast::FunDef> {
    // Check if the type is opaque or transparent, and delegate to the proper
    // function
    if ordered.opaque_funs.contains(&def_id) {
        translate_opaque_function(tcx, ordered, types_constraints, type_defs, fun_defs, def_id)
    } else {
        translate_transparent_function(tcx, ordered, types_constraints, type_defs, fun_defs, def_id)
    }
}

/// Translate the functions
pub fn translate_functions(
    tcx: TyCtxt,
    ordered: &OrderedDecls,
    types_constraints: &TypesConstraintsMap,
    type_defs: &ty::TypeDecls,
) -> Result<ast::FunDefs> {
    let mut fun_defs = ast::FunDefs::new();

    // Translate the bodies one at a time
    for decl in &ordered.decls {
        use crate::id_vector::ToUsize;
        match decl {
            DeclarationGroup::Fun(GDeclarationGroup::NonRec(def_id)) => {
                let fun_def = translate_function(
                    tcx,
                    ordered,
                    &types_constraints,
                    type_defs,
                    &mut fun_defs,
                    *def_id,
                )?;
                // We have to make sure we translate the definitions in the
                // proper order, otherwise we mess with the vector of ids
                assert!(def_id.to_usize() == fun_defs.len());
                fun_defs.push_back(fun_def);
            }
            DeclarationGroup::Fun(GDeclarationGroup::Rec(ids)) => {
                for def_id in ids {
                    let fun_def = translate_function(
                        tcx,
                        ordered,
                        &types_constraints,
                        type_defs,
                        &mut fun_defs,
                        *def_id,
                    )?;
                    // We have to make sure we translate the definitions in the
                    // proper order, otherwise we mess with the vector of ids
                    assert!(def_id.to_usize() == fun_defs.len());
                    fun_defs.push_back(fun_def);
                }
            }
            DeclarationGroup::Type(_) => {
                // Ignore the type declarations
                continue;
            }
        }
    }

    // Print the functions
    for def in &fun_defs {
        trace!(
            "# Signature:\n{}\n\n# Function definition:\n{}\n",
            def.signature.fmt_with_defs(type_defs),
            def.fmt_with_defs(type_defs, &fun_defs)
        );
    }

    Ok(fun_defs)
}
