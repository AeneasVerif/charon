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
use crate::get_mir::{boxes_are_desugared, get_mir_for_def_id_and_level, MirLevel};
use crate::id_vector;
use crate::meta;
use crate::meta::{FileId, FileName};
use crate::names::global_def_id_to_name;
use crate::names::{function_def_id_to_name, type_def_id_to_name};
use crate::regions_hierarchy as rh;
use crate::regions_hierarchy::TypesConstraintsMap;
use crate::rust_to_local_ids::*;
use crate::translate_constants::{
    translate_evaluated_operand_constant, translate_operand_constant,
};
use crate::translate_types;
use crate::types as ty;
use crate::types::{FieldId, VariantId};
use crate::ullbc_ast as ast;
use crate::values as v;
use crate::values::{PrimitiveValue, ScalarValue};
use core::convert::*;
use hashlink::linked_hash_map::LinkedHashMap;
use log::warn;
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::mir;
use rustc_middle::mir::{
    BasicBlock, Body, Operand, Place, PlaceElem, Statement, StatementKind, Terminator,
    TerminatorKind, START_BLOCK,
};
use rustc_middle::ty as mir_ty;
use rustc_middle::ty::adjustment::PointerCast;
use rustc_middle::ty::{ParamEnv, TyCtxt, TyKind};
use rustc_session::Session;
use rustc_span::Span;
use std::collections::HashMap;
use std::iter::FromIterator;
use translate_types::{translate_erased_region, translate_region_name, TypeTransContext};

/// Translation context for function and global definitions
/// TODO: we should put the `TyCtx` and the `Session` in there
pub struct DeclTransContext<'tcx, 'ctx> {
    /// The compiler session
    pub sess: &'ctx Session,
    ///
    pub tcx: TyCtxt<'tcx>,
    /// The ordered declarations
    pub ordered: &'ctx OrderedDecls,
    /// Type definitions
    pub type_defs: &'ctx ty::TypeDecls,
    /// The function definitions
    pub fun_defs: &'ctx ast::FunDecls,
    /// The global definitions
    pub global_defs: &'ctx ast::GlobalDecls,
    /// The level at which to extract the MIR
    pub mir_level: MirLevel,
}

/// A translation context for function and global bodies.
///
/// We use `im::OrdMap` a lot in places where we could use a
/// `std::collections::BTreeMap` (because we actually don't do context
/// duplication). For now the performance doesn't matter, and it allows
/// not to mix too many very similar data structures, but we might consider
/// using `std::collections::BTreeMap` instead.
#[derive(Clone)]
struct BodyTransContext<'tcx, 'ctx, 'ctx1> {
    /// This is used in very specific situations.
    def_id: DefId,
    /// The declarations translation context, containing the function and global definitions.
    /// Also contains the type translation context.
    ft_ctx: &'ctx DeclTransContext<'tcx, 'ctx1>,
    /// Region counter
    regions_counter: ty::RegionVarId::Generator,
    /// The regions
    regions: ty::RegionVarId::Vector<ty::RegionVar>,
    /// The map from rust region to translated region indices
    rregions_to_ids: im::OrdMap<rustc_middle::ty::RegionKind<'tcx>, ty::RegionVarId::Id>,
    /// Id counter for the type variables
    type_vars_counter: ty::TypeVarId::Generator,
    /// The type variables
    type_vars: ty::TypeVarId::Vector<ty::TypeVar>,
    /// The map from rust type variable indices to translated type variable
    /// indices.
    rtype_vars_to_ids: im::OrdMap<u32, ty::TypeVarId::Id>,
    /// Id counter for the variables
    vars_counter: v::VarId::Generator,
    /// The "regular" variables
    vars: v::VarId::Vector<ast::Var>,
    /// The map from rust variable indices to translated variables indices.
    rvars_to_ids: im::OrdMap<u32, v::VarId::Id>,
    /// Id counter for the const generic variables
    const_generic_counter: ty::ConstGenericVarId::Generator,
    /// The const generic variables
    const_generic_vars: ty::ConstGenericVarId::Vector<ty::ConstGenericVar>,
    /// Block id counter
    blocks_counter: ast::BlockId::Generator,
    /// The translated blocks. We can't use `ast::BlockId::Vector<ast::BlockData>`
    /// here because we might generate several fresh indices before actually
    /// adding the resulting blocks to the map.
    blocks: im::OrdMap<ast::BlockId::Id, ast::BlockData>,
    /// The map from rust blocks to translated blocks.
    /// Note that when translating terminators like DropAndReplace, we might have
    /// to introduce new blocks which don't appear in the original MIR.
    rblocks_to_ids: im::OrdMap<BasicBlock, ast::BlockId::Id>,
}

impl<'tcx, 'ctx> DeclTransContext<'tcx, 'ctx> {
    fn get_def_id_from_rid(&self, def_id: DefId) -> Option<ast::FunDeclId::Id> {
        self.ordered.fun_rid_to_id.get(&def_id).copied()
    }

    fn get_def_rid_from_id(&self, def_id: ast::FunDeclId::Id) -> Option<DefId> {
        self.ordered
            .decls_info
            .get(&AnyDeclId::Fun(def_id))
            .map(|i| i.rid)
    }
}

impl<'tcx, 'ctx, 'ctx1> BodyTransContext<'tcx, 'ctx, 'ctx1> {
    /// Create a new `ExecContext`.
    fn new(def_id: DefId, ft_ctx: &'ctx DeclTransContext<'tcx, 'ctx1>) -> Self {
        BodyTransContext {
            def_id,
            ft_ctx,
            regions_counter: ty::RegionVarId::Generator::new(),
            regions: ty::RegionVarId::Vector::new(),
            rregions_to_ids: im::OrdMap::new(),
            type_vars_counter: ty::TypeVarId::Generator::new(),
            type_vars: ty::TypeVarId::Vector::new(),
            rtype_vars_to_ids: im::OrdMap::new(),
            vars_counter: v::VarId::Generator::new(),
            vars: v::VarId::Vector::new(),
            rvars_to_ids: im::OrdMap::new(),
            const_generic_counter: ty::ConstGenericVarId::Generator::new(),
            const_generic_vars: ty::ConstGenericVarId::Vector::new(),
            blocks_counter: ast::BlockId::Generator::new(),
            blocks: im::OrdMap::new(),
            rblocks_to_ids: im::OrdMap::new(),
        }
    }

    fn get_local(&self, local: &mir::Local) -> Option<v::VarId::Id> {
        self.rvars_to_ids.get(&local.as_u32()).copied()
    }

    fn get_block_id_from_rid(&self, rid: BasicBlock) -> Option<ast::BlockId::Id> {
        self.rblocks_to_ids.get(&rid).copied()
    }

    fn get_var_from_id(&self, var_id: v::VarId::Id) -> Option<&ast::Var> {
        self.vars.get(var_id)
    }

    fn get_region_from_rust(
        &self,
        r: rustc_middle::ty::RegionKind<'tcx>,
    ) -> Option<ty::RegionVarId::Id> {
        self.rregions_to_ids.get(&r).copied()
    }

    fn push_region(
        &mut self,
        r: rustc_middle::ty::RegionKind<'tcx>,
        name: Option<String>,
    ) -> ty::RegionVarId::Id {
        use crate::id_vector::ToUsize;
        let rid = self.regions_counter.fresh_id();
        assert!(rid.to_usize() == self.regions.len());
        let var = ty::RegionVar { index: rid, name };
        self.regions.insert(rid, var);
        self.rregions_to_ids.insert(r, rid);
        rid
    }

    fn push_type_var(&mut self, rindex: u32, name: String) -> ty::TypeVarId::Id {
        use crate::id_vector::ToUsize;
        let var_id = self.type_vars_counter.fresh_id();
        assert!(var_id.to_usize() == self.type_vars.len());
        let var = ty::TypeVar {
            index: var_id,
            name,
        };
        self.type_vars.insert(var_id, var);
        self.rtype_vars_to_ids.insert(rindex, var_id);
        var_id
    }

    fn push_var(&mut self, rid: u32, ty: ty::ETy, name: Option<String>) {
        use crate::id_vector::ToUsize;
        let var_id = self.vars_counter.fresh_id();
        assert!(var_id.to_usize() == self.vars.len());
        let var = ast::Var {
            index: var_id,
            name,
            ty,
        };
        self.vars.insert(var_id, var);
        self.rvars_to_ids.insert(rid, var_id);
    }

    fn fresh_block_id(&mut self, rid: BasicBlock) -> ast::BlockId::Id {
        let block_id = self.blocks_counter.fresh_id();
        self.rblocks_to_ids.insert(rid, block_id);
        block_id
    }

    fn push_block(&mut self, id: ast::BlockId::Id, block: ast::BlockData) {
        self.blocks.insert(id, block);
    }

    fn get_type_defs(&self) -> &ty::TypeDecls {
        self.ft_ctx.type_defs
    }
}

impl<'tcx, 'ctx> Formatter<ty::TypeDeclId::Id> for DeclTransContext<'tcx, 'ctx> {
    fn format_object(&self, id: ty::TypeDeclId::Id) -> String {
        self.type_defs.format_object(id)
    }
}

impl<'tcx, 'ctx, 'ctx1> Formatter<ty::TypeVarId::Id> for BodyTransContext<'tcx, 'ctx, 'ctx1> {
    fn format_object(&self, id: ty::TypeVarId::Id) -> String {
        let v = self.type_vars.get(id).unwrap();
        v.to_string()
    }
}

impl<'tcx, 'ctx, 'ctx1> Formatter<v::VarId::Id> for BodyTransContext<'tcx, 'ctx, 'ctx1> {
    fn format_object(&self, id: v::VarId::Id) -> String {
        let v = self.vars.get(id).unwrap();
        v.to_string()
    }
}

impl<'tcx, 'ctx, 'ctx1> Formatter<ty::RegionVarId::Id> for BodyTransContext<'tcx, 'ctx, 'ctx1> {
    fn format_object(&self, id: ty::RegionVarId::Id) -> String {
        let v = self.regions.get(id).unwrap();
        v.to_string()
    }
}

impl<'tcx, 'ctx, 'ctx1> Formatter<&ty::Region<ty::RegionVarId::Id>>
    for BodyTransContext<'tcx, 'ctx, 'ctx1>
{
    fn format_object(&self, r: &ty::Region<ty::RegionVarId::Id>) -> String {
        r.fmt_with_ctx(self)
    }
}

impl<'tcx, 'ctx, 'ctx1> Formatter<ty::ConstGenericVarId::Id>
    for BodyTransContext<'tcx, 'ctx, 'ctx1>
{
    fn format_object(&self, id: ty::ConstGenericVarId::Id) -> String {
        let v = self.const_generic_vars.get(id).unwrap();
        v.to_string()
    }
}

impl<'tcx, 'ctx, 'ctx1> Formatter<&ty::ErasedRegion> for BodyTransContext<'tcx, 'ctx, 'ctx1> {
    fn format_object(&self, _: &ty::ErasedRegion) -> String {
        "'_".to_owned()
    }
}

impl<'tcx, 'ctx, 'ctx1> Formatter<ty::TypeDeclId::Id> for BodyTransContext<'tcx, 'ctx, 'ctx1> {
    fn format_object(&self, id: ty::TypeDeclId::Id) -> String {
        self.ft_ctx.type_defs.format_object(id)
    }
}

impl<'tcx, 'ctx, 'ctx1> Formatter<&ty::Ty<ty::Region<ty::RegionVarId::Id>>>
    for BodyTransContext<'tcx, 'ctx, 'ctx1>
{
    fn format_object(&self, ty: &ty::Ty<ty::Region<ty::RegionVarId::Id>>) -> String {
        ty.fmt_with_ctx(self)
    }
}

impl<'tcx, 'ctx, 'ctx1> Formatter<&ty::Ty<ty::ErasedRegion>>
    for BodyTransContext<'tcx, 'ctx, 'ctx1>
{
    fn format_object(&self, ty: &ty::Ty<ty::ErasedRegion>) -> String {
        ty.fmt_with_ctx(self)
    }
}

impl<'tcx, 'ctx, 'ctx1> BodyTransContext<'tcx, 'ctx, 'ctx1> {
    fn to_type_trans_context(&self) -> TypeTransContext<'tcx, 'ctx> {
        TypeTransContext::new(
            // For the def id: we use the function/global def id
            self.def_id,
            self.ft_ctx.tcx,
            self.ft_ctx.type_defs,
            self.ft_ctx.global_defs,
            self.ft_ctx.ordered,
            self.rregions_to_ids.clone(),
            self.rtype_vars_to_ids.clone(),
            self.ft_ctx.mir_level,
        )
    }
}

fn translate_ety<'tcx>(
    bt_ctx: &BodyTransContext<'tcx, '_, '_>,
    ty: &mir_ty::Ty<'tcx>,
) -> Result<ty::ETy> {
    let tt_ctx = bt_ctx.to_type_trans_context();
    translate_types::translate_ety(&tt_ctx, ty)
}

fn translate_ety_kind<'tcx>(
    bt_ctx: &BodyTransContext<'tcx, '_, '_>,
    ty: &mir_ty::TyKind<'tcx>,
) -> Result<ty::ETy> {
    let tt_ctx = bt_ctx.to_type_trans_context();
    translate_types::translate_ety_kind(&tt_ctx, ty)
}

fn translate_sig_ty<'tcx>(
    bt_ctx: &BodyTransContext<'tcx, '_, '_>,
    ty: &mir_ty::Ty<'tcx>,
) -> Result<ty::RTy> {
    let tt_ctx = bt_ctx.to_type_trans_context();
    translate_types::translate_sig_ty(&tt_ctx, ty)
}

/// Translate a function's local variables by adding them in the environment.
fn translate_body_locals<'tcx>(
    bt_ctx: &mut BodyTransContext<'tcx, '_, '_>,
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
        let name: Option<String> = span_to_var_name.get(&span).cloned();

        // Translate the type
        let ty = translate_ety(bt_ctx, &var.ty)?;

        // Add the variable to the environment
        bt_ctx.push_var(index.as_u32(), ty, name);
    }

    Ok(())
}

/// Translate an expression's body (either a function or a global).
///
/// The local variables should already have been translated and inserted in
/// the context.
fn translate_transparent_expression_body<'tcx>(
    bt_ctx: &mut BodyTransContext<'tcx, '_, '_>,
    body: &Body<'tcx>,
) -> Result<()> {
    trace!();

    let id = translate_basic_block(bt_ctx, body, START_BLOCK)?;
    assert!(id == ast::START_BLOCK_ID);

    Ok(())
}

fn translate_basic_block<'tcx>(
    bt_ctx: &mut BodyTransContext<'tcx, '_, '_>,
    body: &Body<'tcx>,
    block_id: BasicBlock,
) -> Result<ast::BlockId::Id> {
    // Check if the block has already been translated
    let id = bt_ctx.rblocks_to_ids.get(&block_id);
    if let Some(id) = id {
        return Ok(*id);
    }
    let nid = bt_ctx.fresh_block_id(block_id);

    // Retrieve the block data
    let block = body.basic_blocks.get(block_id).unwrap();

    // Translate the statements
    let mut statements = Vec::new();
    for statement in &block.statements {
        trace!("statement: {:?}", statement);

        // Some statements might be ignored, hence the optional returned value
        let opt_statement = translate_statement(bt_ctx, body, statement)?;
        if let Some(statement) = opt_statement {
            statements.push(statement)
        }
    }

    // Translate the terminator
    let terminator = block.terminator();
    let terminator = translate_terminator(bt_ctx, body, terminator)?;

    // Insert the block in the translated blocks
    let block = ast::BlockData {
        statements,
        terminator,
    };

    bt_ctx.push_block(nid, block);

    Ok(nid)
}

/// Translate a place and return its type
fn translate_place_with_type<'tcx, 'ctx>(
    bt_ctx: &'ctx BodyTransContext<'tcx, 'ctx, '_>,
    place: &Place<'tcx>,
) -> (e::Place, ty::ETy) {
    let var_id = bt_ctx.get_local(&place.local).unwrap();
    let var = bt_ctx.get_var_from_id(var_id).unwrap();
    let (projection, ty) = translate_projection(
        bt_ctx,
        bt_ctx.ft_ctx.mir_level,
        bt_ctx.ft_ctx.type_defs,
        var.ty.clone(),
        place.projection,
    );

    (e::Place { var_id, projection }, ty)
}

/// Translate a place
fn translate_place<'tcx, 'ctx>(
    bt_ctx: &'ctx BodyTransContext<'tcx, 'ctx, '_>,
    place: &Place<'tcx>,
) -> e::Place {
    translate_place_with_type(bt_ctx, place).0
}

/// Translate a projection
///
/// We use the variable type to disambiguate between different kinds of
/// projections. For instance, rust uses `Deref` both to dereference mutable/shared
/// references and to move values from inside a box. On our side, we distinguish
/// the two kinds of dereferences.
///
/// We return the translated projection, and its type.
///
/// - `mir_level`: used for sanity checks
fn translate_projection<'tcx, 'ctx>(
    bt_ctx: &'ctx BodyTransContext<'tcx, 'ctx, '_>,
    mir_level: MirLevel,
    type_defs: &ty::TypeDecls,
    var_ty: ty::ETy,
    rprojection: &rustc_middle::ty::List<PlaceElem<'_>>,
) -> (e::Projection, ty::ETy) {
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
        trace!("- pelem: {:?}\n- path_type: {:?}", pelem, path_type);
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
                    ty::Ty::Adt(ty::TypeId::Assumed(ty::AssumedTy::Box), regions, tys, cgs) => {
                        // This case only happens in some MIR levels
                        assert!(!boxes_are_desugared(mir_level));
                        assert!(regions.is_empty());
                        assert!(tys.len() == 1);
                        assert!(cgs.is_empty());
                        path_type = tys[0].clone();
                        projection.push_back(e::ProjectionElem::DerefBox);
                    }
                    ty::Ty::RawPtr(ty, _) => {
                        path_type = ty.deref().clone();
                        projection.push_back(e::ProjectionElem::DerefRawPtr);
                    }
                    _ => {
                        unreachable!("- pelem: {:?}\n- path_type: {:?}", pelem, path_type);
                    }
                }
            }
            mir::ProjectionElem::Field(field, _) => {
                let field_id = translate_field(field);
                // Update the path type and generate the proj kind at the
                // same time.
                let proj_elem = match path_type {
                    ty::Ty::Adt(ty::TypeId::Adt(type_id), _regions, tys, cgs) => {
                        let type_def = type_defs.get_type_def(type_id).unwrap();

                        // If (and only if) the ADT is an enumeration, we should
                        // have downcast information (that we need to figure out
                        // the variant, and thus know how to project).
                        assert!(type_def.kind.is_enum() == downcast_id.is_some());

                        path_type = type_def.get_erased_regions_instantiated_field_type(
                            downcast_id,
                            &tys,
                            &cgs,
                            field_id,
                        );

                        let proj_kind = e::FieldProjKind::Adt(type_id, downcast_id);
                        e::ProjectionElem::Field(proj_kind, field_id)
                    }
                    ty::Ty::Adt(ty::TypeId::Tuple, regions, tys, cgs) => {
                        assert!(regions.is_empty());
                        assert!(downcast_id.is_none());
                        assert!(cgs.is_empty());
                        path_type = tys.get(field.as_usize()).unwrap().clone();
                        let proj_kind = e::FieldProjKind::Tuple(tys.len());
                        e::ProjectionElem::Field(proj_kind, field_id)
                    }
                    ty::Ty::Adt(ty::TypeId::Assumed(ty::AssumedTy::Option), regions, tys, cgs) => {
                        assert!(regions.is_empty());
                        assert!(tys.len() == 1);
                        assert!(cgs.is_empty());
                        assert!(downcast_id.is_some());
                        assert!(field_id == ty::FieldId::ZERO);

                        path_type = tys.get(0).unwrap().clone();
                        let variant_id = downcast_id.unwrap();
                        assert!(variant_id == assumed::OPTION_SOME_VARIANT_ID);
                        let proj_kind = e::FieldProjKind::Option(variant_id);
                        e::ProjectionElem::Field(proj_kind, field_id)
                    }
                    ty::Ty::Adt(ty::TypeId::Assumed(aty), regions, tys, cgs)
                        if aty == ty::AssumedTy::Box
                            || aty == ty::AssumedTy::PtrUnique
                            || aty == ty::AssumedTy::PtrNonNull =>
                    {
                        // The Box case only happens in some MIR levels.
                        // We group the following cases here:
                        // ```
                        // (x:Box<T>).0: std::ptr::Unique<T>
                        // (x:std::ptr::Unique<T>).0: std::ptr::NonNull<T>
                        // (x:std::ptr::NonNull<T>).0: *const T // raw pointer
                        // ```
                        assert!(!aty.is_box() || boxes_are_desugared(mir_level));

                        // Some more sanity checks
                        assert!(regions.is_empty());
                        assert!(tys.len() == 1);
                        assert!(cgs.is_empty());
                        assert!(downcast_id.is_none());
                        assert!(field_id == ty::FieldId::ZERO);

                        // Retrieve the type given by `T` above
                        let type_param = tys.get(0).unwrap().clone();

                        // Find the new field type
                        let elem;
                        match aty {
                            ty::AssumedTy::Box => {
                                elem = e::ProjectionElem::DerefBox;
                                path_type = ty::Ty::Adt(
                                    ty::TypeId::Assumed(ty::AssumedTy::PtrUnique),
                                    im::vector![],
                                    im::vector![type_param],
                                    im::vector![],
                                )
                            }
                            ty::AssumedTy::PtrUnique => {
                                elem = e::ProjectionElem::DerefPtrUnique;
                                path_type = ty::Ty::Adt(
                                    ty::TypeId::Assumed(ty::AssumedTy::PtrNonNull),
                                    im::vector![],
                                    im::vector![type_param],
                                    im::vector![],
                                )
                            }
                            ty::AssumedTy::PtrNonNull => {
                                elem = e::ProjectionElem::DerefPtrNonNull;
                                path_type =
                                    ty::Ty::RawPtr(Box::new(type_param), ty::RefKind::Shared)
                            }
                            _ => unreachable!(),
                        };

                        elem
                    }
                    _ => {
                        trace!("Path type: {:?}", path_type);
                        unreachable!();
                    }
                };
                projection.push_back(proj_elem);
                downcast_id = None;
            }
            mir::ProjectionElem::Index(local) => {
                let v = bt_ctx.get_local(&local).unwrap();
                projection.push_back(e::ProjectionElem::Offset(v));
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
            mir::ProjectionElem::OpaqueCast(_) => {
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

    (projection, path_type)
}

/// Translate an operand with its type
fn translate_operand_with_type<'tcx>(
    bt_ctx: &BodyTransContext<'tcx, '_, '_>,
    operand: &mir::Operand<'tcx>,
) -> (e::Operand, ty::ETy) {
    trace!();
    match operand {
        Operand::Copy(place) => {
            let (p, ty) = translate_place_with_type(bt_ctx, place);
            (e::Operand::Copy(p), ty)
        }
        Operand::Move(place) => {
            let (p, ty) = translate_place_with_type(bt_ctx, place);
            (e::Operand::Move(p), ty)
        }
        Operand::Constant(constant) => {
            let (ty, constant) =
                translate_operand_constant(&bt_ctx.to_type_trans_context(), constant);
            (e::Operand::Const(ty.clone(), constant), ty)
        }
    }
}

/// Translate an operand
fn translate_operand<'tcx>(
    bt_ctx: &BodyTransContext<'tcx, '_, '_>,
    operand: &mir::Operand<'tcx>,
) -> e::Operand {
    trace!();
    translate_operand_with_type(bt_ctx, operand).0
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
fn translate_move_box_first_projector_operand<'tcx>(
    bt_ctx: &BodyTransContext<'tcx, '_, '_>,
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
        mir::BorrowKind::Shared => e::BorrowKind::Shared,
        mir::BorrowKind::Mut {
            allow_two_phase_borrow,
        } => {
            if allow_two_phase_borrow {
                e::BorrowKind::TwoPhaseMut
            } else {
                e::BorrowKind::Mut
            }
        }
        mir::BorrowKind::Unique => {
            unimplemented!();
        }
        mir::BorrowKind::Shallow => e::BorrowKind::Shallow,
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
fn translate_rvalue<'tcx>(
    tcx: TyCtxt<'tcx>,
    bt_ctx: &BodyTransContext<'tcx, '_, '_>,
    rvalue: &mir::Rvalue<'tcx>,
) -> e::Rvalue {
    use std::ops::Deref;
    match rvalue {
        mir::Rvalue::Use(operand) => e::Rvalue::Use(translate_operand(bt_ctx, operand)),
        mir::Rvalue::CopyForDeref(place) => {
            // According to the documentation, it seems to be an optimisation
            // for drop elaboration. We treat it as a regular copy.
            let place = translate_place(bt_ctx, place);
            e::Rvalue::Use(e::Operand::Copy(place))
        }
        mir::Rvalue::Repeat(operand, cnst) => {
            // ParamEnv is used for tracking `where` clauses; not needed for us here.
            // NOTE: more recent versions of `rustc` seem to fix this API to return a `usize`, thus
            // avoiding the `try_into()` below.
            let c = cnst.try_eval_usize(tcx, ParamEnv::empty()).unwrap();
            // We are effectively desugaring the repeat in Charon, turning it into an array literal
            // where the operand is repeated `cnst` times.
            let (operand, t) = translate_operand_with_type(bt_ctx, operand);
            let mut operands = Vec::with_capacity(c.try_into().unwrap());
            for _ in 0..c {
                operands.push(operand.clone());
            }
            // We *have* to desugar here; we don't have enough context (the destination place, the
            // lifetime variable) to translate this into a built-in function call. This is why we
            // don't have a ArrayRepeat AssumedFunId.
            let c = ty::ConstGeneric::Value(PrimitiveValue::Scalar(ScalarValue::Usize(c as usize)));
            e::Rvalue::Aggregate(e::AggregateKind::Array(t, c), operands)
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
        mir::Rvalue::Len(place) => {
            let place = translate_place(bt_ctx, place);
            e::Rvalue::Len(place)
        }
        mir::Rvalue::Cast(cast_kind, operand, tgt_ty) => {
            trace!("Rvalue::Cast: {:?}", rvalue);
            // Put aside the pointer casts (which we don't support), I think
            // casts should only be from integers/booleans to integer/booleans.

            // Translate the target type
            let tgt_ty = translate_ety(bt_ctx, tgt_ty).unwrap();

            // Translate the operand
            let (op, src_ty) = translate_operand_with_type(bt_ctx, operand);

            match (cast_kind, &src_ty, &tgt_ty) {
                (rustc_middle::mir::CastKind::IntToInt, _, _) => {
                    // We only support source and target types for integers
                    let tgt_ty = *tgt_ty.as_primitive().as_integer();
                    let src_ty = *src_ty.as_primitive().as_integer();

                    e::Rvalue::UnaryOp(e::UnOp::Cast(src_ty, tgt_ty), op)
                }
                (
                    rustc_middle::mir::CastKind::Pointer(PointerCast::Unsize),
                    ty::Ty::Ref(_, t1, _),
                    ty::Ty::Ref(_, t2, _),
                ) => {
                    // In MIR terminology, we go from &[T; l] to &[T] which means we
                    // effectively "unsize" the type, as `l` no longer appears in the
                    // destination type. At runtime, the converse happens: the length
                    // materializes into the fat pointer.
                    match (&**t1, &**t2) {
                        (
                            ty::Ty::Adt(ty::TypeId::Assumed(ty::AssumedTy::Array), _, tys, cgs),
                            ty::Ty::Adt(ty::TypeId::Assumed(ty::AssumedTy::Slice), _, tys1, _),
                        ) => {
                            assert!(tys.len() == 1 && cgs.len() == 1);
                            assert!(tys[0] == tys1[0]);
                            e::Rvalue::UnaryOp(
                                e::UnOp::ArrayToSlice(tys[0].clone(), cgs[0].clone()),
                                op,
                            )
                        }
                        _ => {
                            panic!(
                                "Unsupported cast: {:?}, src={:?}, dst={:?}",
                                rvalue, src_ty, tgt_ty
                            )
                        }
                    }
                }
                _ => {
                    panic!(
                        "Unsupported cast: {:?}, src={:?}, dst={:?}",
                        rvalue, src_ty, tgt_ty
                    )
                }
            }
        }
        mir::Rvalue::BinaryOp(binop, operands) | mir::Rvalue::CheckedBinaryOp(binop, operands) => {
            // We merge checked and unchecked binary operations
            let (left, right) = operands.deref();
            e::Rvalue::BinaryOp(
                translate_binaryop_kind(*binop),
                translate_operand(bt_ctx, left),
                translate_operand(bt_ctx, right),
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
            translate_operand(bt_ctx, operand),
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
                .map(|op| translate_operand(bt_ctx, op))
                .collect();

            match aggregate_kind.deref() {
                mir::AggregateKind::Array(ty) => {
                    let t_ty = translate_ety(bt_ctx, &ty).unwrap();
                    let cg = ty::ConstGeneric::Value(PrimitiveValue::Scalar(ScalarValue::Usize(
                        operands_t.len(),
                    )));
                    e::Rvalue::Aggregate(e::AggregateKind::Array(t_ty, cg), operands_t)
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

                    // Not sure what those two parameters are used for, so
                    // panicking if they are not none (to catch a use case).
                    // I'm not even sure that "field_index" is a proper name:
                    // the documentation seems outdated (it says the 4th parameter
                    // is a field index, while it makes more sense for it to be
                    // the 5th, and I don't know how I should use it anyway).
                    assert!(user_annotation.is_none());
                    assert!(field_index.is_none());

                    // Translate the substitution
                    let (region_params, mut type_params, cg_params) =
                        translate_subst_generic_args_in_body(bt_ctx, None, substs).unwrap();

                    if adt_id.is_local() {
                        // Local ADT: retrieve the definition
                        let id_t = *bt_ctx.ft_ctx.ordered.type_rid_to_id.get(adt_id).unwrap();
                        let def = bt_ctx.get_type_defs().get_type_def(id_t).unwrap();

                        assert!(region_params.len() == def.region_params.len());
                        assert!(type_params.len() == def.type_params.len());

                        let variant_id = match &def.kind {
                            ty::TypeDeclKind::Enum(variants) => {
                                let variant_id = translate_variant_id(*variant_idx);
                                assert!(
                                    operands_t.len()
                                        == variants.get(variant_id).unwrap().fields.len()
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

                        let akind = e::AggregateKind::Adt(
                            id_t,
                            variant_id,
                            region_params,
                            type_params,
                            cg_params,
                        );

                        e::Rvalue::Aggregate(akind, operands_t)
                    } else {
                        // External ADT.
                        // Can be `Option`
                        // TODO: treat all external ADTs in a consistant manner.
                        // For instance, we can access the variants of any external
                        // enumeration marked as `public`.
                        let name = type_def_id_to_name(tcx, *adt_id);
                        if name.equals_ref_name(&assumed::OPTION_NAME) {
                            // Sanity checks
                            assert!(region_params.is_empty());
                            assert!(type_params.len() == 1);

                            // Find the variant
                            let variant_id = translate_variant_id(*variant_idx);
                            if variant_id == assumed::OPTION_NONE_VARIANT_ID {
                                assert!(operands_t.is_empty());
                            } else if variant_id == assumed::OPTION_SOME_VARIANT_ID {
                                assert!(operands_t.len() == 1);
                            } else {
                                unreachable!();
                            }

                            let akind =
                                e::AggregateKind::Option(variant_id, type_params.pop().unwrap());

                            e::Rvalue::Aggregate(akind, operands_t)
                        } else if name.equals_ref_name(&assumed::RANGE_NAME) {
                            // Sanity checks
                            assert!(region_params.is_empty());
                            // Ranges are parametric over the type of indices
                            assert!(type_params.len() == 1);
                            e::Rvalue::Aggregate(
                                e::AggregateKind::Range(type_params.pop().unwrap()),
                                operands_t,
                            )
                        } else {
                            panic!("Unsupported ADT: {}", name);
                        }
                    }
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
fn translate_statement<'tcx>(
    bt_ctx: &BodyTransContext<'tcx, '_, '_>,
    body: &Body<'tcx>,
    statement: &Statement<'tcx>,
) -> Result<Option<ast::Statement>> {
    trace!("About to translate statement (MIR) {:?}", statement);

    use std::ops::Deref;

    let sess = bt_ctx.ft_ctx.sess;
    let tcx = bt_ctx.ft_ctx.tcx;

    let t_statement: Option<ast::RawStatement> = match &statement.kind {
        StatementKind::Assign(assign) => {
            let (place, rvalue) = assign.deref();
            let t_place = translate_place(bt_ctx, place);
            let t_rvalue = translate_rvalue(tcx, bt_ctx, rvalue);

            Some(ast::RawStatement::Assign(t_place, t_rvalue))
        }
        StatementKind::FakeRead(info) => {
            let (_read_cause, place) = info.deref();
            let t_place = translate_place(bt_ctx, place);

            Some(ast::RawStatement::FakeRead(t_place))
        }
        StatementKind::SetDiscriminant {
            place,
            variant_index,
        } => {
            let t_place = translate_place(bt_ctx, place);
            let variant_id = translate_variant_id(*variant_index);
            Some(ast::RawStatement::SetDiscriminant(t_place, variant_id))
        }
        StatementKind::StorageLive(_) => {
            // We ignore StorageLive
            None
        }
        StatementKind::StorageDead(local) => {
            let var_id = bt_ctx.get_local(local).unwrap();
            Some(ast::RawStatement::StorageDead(var_id))
        }
        StatementKind::Retag(_, _) => {
            // This is for the stacked borrows
            trace!("retag");
            None
        }
        StatementKind::AscribeUserType(_, _) => {
            trace!("AscribedUserType");
            // We ignore those: they are just used by the type checker.
            // Note that this instruction is used only in certain passes
            // (it is not present in optimized MIR for instance).
            None
        }
        StatementKind::Coverage(_) => {
            unimplemented!();
        }
        StatementKind::Nop => {
            // We ignore this statement
            None
        }
        StatementKind::Deinit(place) => {
            let t_place = translate_place(bt_ctx, place);
            Some(ast::RawStatement::Deinit(t_place))
        }
        StatementKind::Intrinsic(_) => {
            unimplemented!();
        }
    };

    // Add the meta information
    match t_statement {
        None => Ok(None),
        Some(t_statement) => {
            let meta = meta::get_meta_from_source_info(
                sess,
                &bt_ctx.ft_ctx.ordered.file_to_id,
                &body.source_scopes,
                statement.source_info,
            );

            Ok(Some(ast::Statement::new(meta, t_statement)))
        }
    }
}

/// Translate a terminator
fn translate_terminator<'tcx>(
    bt_ctx: &mut BodyTransContext<'tcx, '_, '_>,
    body: &Body<'tcx>,
    terminator: &Terminator<'tcx>,
) -> Result<ast::Terminator> {
    trace!("About to translate terminator (MIR) {:?}", terminator);

    let sess = bt_ctx.ft_ctx.sess;

    // Compute the meta information beforehand (we might need it to introduce
    // intermediate statements - we desugar some terminators)
    let meta = meta::get_meta_from_source_info(
        sess,
        &bt_ctx.ft_ctx.ordered.file_to_id,
        &body.source_scopes,
        terminator.source_info,
    );

    // Translate the terminator
    let t_terminator: ast::RawTerminator = match &terminator.kind {
        TerminatorKind::Goto { target } => {
            let target = translate_basic_block(bt_ctx, body, *target)?;
            ast::RawTerminator::Goto { target }
        }
        TerminatorKind::SwitchInt { discr, targets } => {
            // Translate the operand which gives the discriminant
            let (discr, discr_ty) = translate_operand_with_type(bt_ctx, discr);

            // Translate the switch targets
            let targets = translate_switch_targets(bt_ctx, body, &discr_ty, targets)?;

            ast::RawTerminator::Switch { discr, targets }
        }
        TerminatorKind::Resume => {
            // This is used to correctly unwind. We shouldn't get there: if
            // we panic, the state gets stuck.
            unreachable!();
        }
        TerminatorKind::Abort => {
            // TODO: we will translate this to `ast::RawTerminator::Abort`,
            // but I want to see in which situations Abort appears.
            unimplemented!();
        }
        TerminatorKind::Return => ast::RawTerminator::Return,
        TerminatorKind::Unreachable => ast::RawTerminator::Unreachable,
        TerminatorKind::Drop {
            place,
            target,
            unwind: _,
        } => ast::RawTerminator::Drop {
            place: translate_place(bt_ctx, place),
            target: translate_basic_block(bt_ctx, body, *target)?,
        },
        TerminatorKind::DropAndReplace {
            place,
            value,
            target,
            unwind: _,
        } => {
            // We desugar this to `drop(place); place := value;

            // Translate the next block
            let target = translate_basic_block(bt_ctx, body, *target)?;

            // Translate the assignment
            let place = translate_place(bt_ctx, place);
            let rv = e::Rvalue::Use(translate_operand(bt_ctx, value));
            let assign = ast::Statement::new(meta, ast::RawStatement::Assign(place.clone(), rv));

            // Generate a goto
            let goto = ast::Terminator::new(meta, ast::RawTerminator::Goto { target });

            // This introduces a new block, which doesn't appear in the original MIR
            let assign_id = bt_ctx.blocks_counter.fresh_id();
            let assign_block = ast::BlockData {
                statements: vec![assign],
                terminator: goto,
            };
            bt_ctx.push_block(assign_id, assign_block);

            // Translate the drop
            ast::RawTerminator::Drop {
                place,
                target: assign_id,
            }
        }
        TerminatorKind::Call {
            func,
            args,
            destination,
            target,
            cleanup: _, // Note that the state gets stuck if we need to unwind
            from_hir_call: _,
            fn_span: _,
        } => {
            trace!("Call: func: {:?}", func);
            translate_function_call(bt_ctx, body, func, args, destination, target)?
        }
        TerminatorKind::Assert {
            cond,
            expected,
            msg: _, // We ignore the message: if we panic, the state gets stuck
            target,
            cleanup: _, // If we panic, the state gets stuck: we don't need to model cleanup
        } => {
            let cond = translate_operand(bt_ctx, cond);
            let target = translate_basic_block(bt_ctx, body, *target)?;
            ast::RawTerminator::Assert {
                cond,
                expected: *expected,
                target,
            }
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
                body.basic_blocks.get(*real_target).unwrap(),
                imaginary_target,
                body.basic_blocks.get(*imaginary_target).unwrap(),
            );

            // False edges are used to make the borrow checker a bit conservative.
            // We translate them as Gotos.
            // Also note that they are used in some passes, and not in some others
            // (they are present in mir_promoted, but not mir_optimized).
            let target = translate_basic_block(bt_ctx, body, *real_target)?;
            ast::RawTerminator::Goto { target }
        }
        TerminatorKind::FalseUnwind {
            real_target,
            unwind: _,
        } => {
            // We consider this to be a goto
            let target = translate_basic_block(bt_ctx, body, *real_target)?;
            ast::RawTerminator::Goto { target }
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
    };

    // Add the meta information
    Ok(ast::Terminator::new(meta, t_terminator))
}

/// Translate switch targets
fn translate_switch_targets<'tcx>(
    bt_ctx: &mut BodyTransContext<'tcx, '_, '_>,
    body: &Body<'tcx>,
    switch_ty: &ty::ETy,
    targets: &mir::SwitchTargets,
) -> Result<ast::SwitchTargets> {
    trace!("targets: {:?}", targets);
    let targets_vec: Vec<(u128, BasicBlock)> = targets.iter().map(|(v, b)| (v, b)).collect();

    match switch_ty {
        ty::Ty::Primitive(ty::PrimitiveValueTy::Bool) => {
            // This is an: `if ... then ... else ...`
            assert!(targets_vec.len() == 1);
            // It seems the block targets are inverted
            let (test_val, otherwise_block) = targets_vec[0];

            assert!(test_val == 0);

            // It seems the block targets are inverted
            let if_block = translate_basic_block(bt_ctx, body, targets.otherwise())?;
            let otherwise_block = translate_basic_block(bt_ctx, body, otherwise_block)?;

            Ok(ast::SwitchTargets::If(if_block, otherwise_block))
        }
        ty::Ty::Primitive(ty::PrimitiveValueTy::Integer(int_ty)) => {
            // This is a: switch(int).
            // Convert all the test values to the proper values.
            let mut targets_map: LinkedHashMap<v::ScalarValue, ast::BlockId::Id> =
                LinkedHashMap::new();
            for (v, tgt) in targets_vec {
                // We need to reinterpret the bytes (`v as i128` is not correct)
                let raw: [u8; 16] = v.to_le_bytes();
                let v = v::ScalarValue::from_le_bytes(*int_ty, raw);
                let tgt = translate_basic_block(bt_ctx, body, tgt)?;
                assert!(!targets_map.contains_key(&v));
                targets_map.insert(v, tgt);
            }
            let otherwise_block = translate_basic_block(bt_ctx, body, targets.otherwise())?;

            Ok(ast::SwitchTargets::SwitchInt(
                *int_ty,
                targets_map,
                otherwise_block,
            ))
        }
        _ => {
            trace!("Unexpected switch_ty: {}", switch_ty.variant_name());
            unreachable!();
        }
    }
}

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
            trace!("Operand::Constant: {:?}", c);
            let c = c.deref();
            match &c.literal {
                mir::ConstantKind::Ty(c) => {
                    // The type of the constant should be a FnDef, allowing
                    // us to retrieve the function's identifier and instantiation.
                    let c_ty = c.ty();
                    assert!(c_ty.is_fn());
                    match c_ty.kind() {
                        mir_ty::TyKind::FnDef(def_id, subst) => (*def_id, subst),
                        _ => {
                            unreachable!();
                        }
                    }
                }
                mir::ConstantKind::Val(cv, c_ty) => {
                    trace!("cv: {:?}, ty: {:?}", cv, c_ty);
                    // Same as for the `Ty` case above
                    assert!(c_ty.is_fn());
                    match c_ty.kind() {
                        mir_ty::TyKind::FnDef(def_id, subst) => (*def_id, subst),
                        _ => {
                            unreachable!();
                        }
                    }
                }
                mir::ConstantKind::Unevaluated(_, _) => {
                    unimplemented!();
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
/// ```text
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
                rustc_middle::ty::TyKind::Adt(adt_def, _) => Some(adt_def.did()),
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
fn translate_function_call<'tcx>(
    bt_ctx: &mut BodyTransContext<'tcx, '_, '_>,
    body: &mir::Body<'tcx>,
    func: &Operand<'tcx>,
    args: &Vec<Operand<'tcx>>,
    destination: &Place<'tcx>,
    target: &Option<BasicBlock>,
) -> Result<ast::RawTerminator> {
    trace!();

    // Translate the function operand - should be a constant: we don't
    // support closures for now
    trace!("func: {:?}", func);

    let tcx = bt_ctx.ft_ctx.tcx;

    // Retrieve the function's identifier and instantiation
    let (def_id, substs) = get_function_from_operand(func);

    // Translate the name to check if is is `core::panicking::panic`
    let name = function_def_id_to_name(tcx, def_id);

    // If the call is `panic!`, then the target is `None`.
    // I don't know in which other cases it can be `None`.
    if name.equals_ref_name(&assumed::PANIC_NAME)
        || name.equals_ref_name(&assumed::BEGIN_PANIC_NAME)
    {
        assert!(!def_id.is_local());
        assert!(target.is_none());

        // We ignore the arguments
        Ok(ast::RawTerminator::Panic)
    } else {
        assert!(target.is_some());
        let next_block = target.unwrap();

        // Translate the target
        let lval = translate_place(bt_ctx, destination);
        let next_block = translate_basic_block(bt_ctx, body, next_block)?;

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
            let t_ty = translate_ety(bt_ctx, &ty)?;

            // Translate the first argument - note that we use a special
            // function to translate it: the operand should be of the form:
            // `move b.0`, and if it is the case it will return `move b`
            let arg = &args[0];
            let t_arg = translate_move_box_first_projector_operand(bt_ctx, arg);

            // Return
            let call = ast::Call {
                func: ast::FunId::Assumed(ast::AssumedFunId::BoxFree),
                region_args: vec![],
                type_args: vec![t_ty],
                const_generic_args: vec![],
                args: vec![t_arg],
                dest: lval,
            };
            Ok(ast::RawTerminator::Call {
                call,
                target: next_block,
            })
        } else {
            // Retrieve the lists of used parameters, in case of non-local
            // definitions
            let (used_type_args, used_args) = if def_id.is_local() {
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
            let (region_args, type_args, const_generic_args) =
                translate_subst_generic_args_in_body(bt_ctx, used_type_args, substs)?;

            // Translate the arguments
            let args = translate_arguments(bt_ctx, used_args, args);

            // Check if the function is considered primitive: primitive
            // functions benefit from special treatment.
            let name = function_def_id_to_name(tcx, def_id);
            let is_prim = if def_id.is_local() {
                false
            } else {
                assumed::get_fun_id_from_name(&name, &type_args).is_some()
            };

            if !is_prim {
                // Retrieve the def id
                let def_id = bt_ctx.ft_ctx.get_def_id_from_rid(def_id).unwrap();

                let func = ast::FunId::Regular(def_id);
                let call = ast::Call {
                    func,
                    region_args,
                    type_args,
                    const_generic_args,
                    args,
                    dest: lval,
                };

                Ok(ast::RawTerminator::Call {
                    call,
                    target: next_block,
                })
            } else {
                // Primitive function.
                //
                // Note that there are subtleties with regards to the way types parameters
                // are translated, because some functions are actually traits, where the
                // types are used for the resolution. For instance, the following:
                // `core::ops::deref::Deref::<alloc::boxed::Box<T>>::deref`
                // is translated to:
                // `box_deref<T>`
                // (the type parameter is not `Box<T>` but `T`).
                translate_primitive_function_call(
                    tcx,
                    def_id,
                    region_args,
                    type_args,
                    const_generic_args,
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
fn translate_subst_generic_args_in_body<'tcx, 'ctx, 'ctx1>(
    bt_ctx: &BodyTransContext<'tcx, 'ctx, 'ctx1>,
    used_args: Option<Vec<bool>>,
    substs: &rustc_middle::ty::subst::InternalSubsts<'tcx>,
) -> Result<(Vec<ty::ErasedRegion>, Vec<ty::ETy>, Vec<ty::ConstGeneric>)> {
    let substs: Vec<rustc_middle::ty::subst::GenericArg<'tcx>> = match used_args {
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

    let mut t_args_regions = Vec::new();
    let mut t_args_tys = Vec::new();
    let t_args_cgs = Vec::new();
    for param in substs.iter() {
        match param.unpack() {
            rustc_middle::ty::subst::GenericArgKind::Type(param_ty) => {
                // Simply translate the type
                let t_param_ty = translate_ety(bt_ctx, &param_ty)?;
                t_args_tys.push(t_param_ty);
            }
            rustc_middle::ty::subst::GenericArgKind::Lifetime(region) => {
                t_args_regions.push(translate_erased_region(region.kind()));
            }
            rustc_middle::ty::subst::GenericArgKind::Const(_) => {
                // TODO:
                unimplemented!();
            }
        }
    }

    Ok((t_args_regions, t_args_tys, t_args_cgs))
}

/// Translate a parameter substitution used inside a function body.
///
/// Note that the regions parameters are expected to have been erased.
fn translate_subst_in_body<'tcx>(
    bt_ctx: &BodyTransContext<'tcx, '_, '_>,
    substs: &rustc_middle::ty::List<rustc_middle::ty::Ty<'tcx>>,
) -> Result<Vec<ty::ETy>> {
    let mut t_args_tys = Vec::new();

    for param in substs.iter() {
        t_args_tys.push(translate_ety(bt_ctx, &param)?);
    }
    Ok(t_args_tys)
}

/// Evaluate function arguments in a context, and return the list of computed
/// values.
fn translate_arguments<'tcx, 'ctx, 'ctx1>(
    bt_ctx: &BodyTransContext<'tcx, 'ctx, 'ctx1>,
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
        let op = translate_operand(bt_ctx, arg);
        t_args.push(op);
    }

    t_args
}

/// Translate a call to a function considered primitive and which is not:
/// panic, begin_panic, box_free (those have a *very* special treatment).
fn translate_primitive_function_call(
    tcx: TyCtxt<'_>,
    def_id: DefId,
    region_args: Vec<ty::ErasedRegion>,
    type_args: Vec<ty::ETy>,
    const_generic_args: Vec<ty::ConstGeneric>,
    args: Vec<e::Operand>,
    dest: e::Place,
    target: ast::BlockId::Id,
) -> Result<ast::RawTerminator> {
    trace!("- def_id: {:?}", def_id,);

    // Translate the function name
    let name = function_def_id_to_name(tcx, def_id);
    trace!("name: {}", name);

    // We assume the function has primitive support, and look up
    // its primitive identifier
    let aid = assumed::get_fun_id_from_name(&name, &type_args).unwrap();

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
        | ast::AssumedFunId::VecLen => {
            let call = ast::Call {
                func: ast::FunId::Assumed(aid),
                region_args,
                type_args,
                const_generic_args,
                args,
                dest,
            };
            Ok(ast::RawTerminator::Call { call, target })
        }
        ast::AssumedFunId::BoxDeref | ast::AssumedFunId::BoxDerefMut => translate_box_deref(
            aid,
            region_args,
            type_args,
            const_generic_args,
            args,
            dest,
            target,
        ),
        ast::AssumedFunId::VecIndex | ast::AssumedFunId::VecIndexMut => translate_vec_index(
            aid,
            region_args,
            type_args,
            const_generic_args,
            args,
            dest,
            target,
        ),
        ast::AssumedFunId::ArraySlice
        | ast::AssumedFunId::ArrayMutSlice
        | ast::AssumedFunId::SliceSlice
        | ast::AssumedFunId::SliceMutSlice => {
            // Take a slice from an array/slice.
            // Note that this isn't any different from a regular function call. Ideally,
            // we'd have a generic assumed function mechanism.
            assert!(type_args.len() == 1);
            assert!(args.len() == 2);

            let call = ast::Call {
                func: ast::FunId::Assumed(aid),
                region_args,
                type_args,
                const_generic_args,
                args,
                dest,
            };

            Ok(ast::RawTerminator::Call { call, target })
        }
        ast::AssumedFunId::BoxFree => {
            // Special case handled elsewhere
            unreachable!();
        }
        ast::AssumedFunId::ArrayIndex
        | ast::AssumedFunId::ArrayMutIndex
        | ast::AssumedFunId::ArrayToSlice => {
            // Those cases are introduced later, in micro-passes, by desugaring
            // projections (for ArrayIndex and ArrayMutIndex) and operations
            // (for ArrayToSlice) to function calls.
            unreachable!()
        }
    }
}

/// Translate `std::Deref::deref` or `std::DerefMut::deref_mut` applied
/// on boxes. We need a custom function because it is a trait.
fn translate_box_deref(
    aid: ast::AssumedFunId,
    region_args: Vec<ty::ErasedRegion>,
    type_args: Vec<ty::ETy>,
    const_generic_args: Vec<ty::ConstGeneric>,
    args: Vec<e::Operand>,
    dest: e::Place,
    target: ast::BlockId::Id,
) -> Result<ast::RawTerminator> {
    // Check the arguments
    assert!(region_args.is_empty());
    assert!(type_args.len() == 1);
    assert!(args.len() == 1);

    // For now we only support deref on boxes
    // Retrieve the boxed value
    let arg_ty = type_args.get(0).unwrap(); // should be `Box<...>`
    let boxed_ty = arg_ty.as_box();
    if boxed_ty.is_none() {
        panic!(
            "Deref/DerefMut trait applied with parameter {:?} while it is only supported on Box<T> values",
            arg_ty
        );
    }
    let boxed_ty = boxed_ty.unwrap();
    let type_args = vec![boxed_ty.clone()];

    let call = ast::Call {
        func: ast::FunId::Assumed(aid),
        region_args,
        type_args,
        const_generic_args,
        args,
        dest,
    };
    Ok(ast::RawTerminator::Call { call, target })
}

/// Translate `core::ops::index::{Index,IndexMut}::{index,index_mut}`
/// applied on `Vec`. We need a custom function because it is a trait.
fn translate_vec_index(
    aid: ast::AssumedFunId,
    region_args: Vec<ty::ErasedRegion>,
    type_args: Vec<ty::ETy>,
    const_generic_args: Vec<ty::ConstGeneric>,
    args: Vec<e::Operand>,
    dest: e::Place,
    target: ast::BlockId::Id,
) -> Result<ast::RawTerminator> {
    // Check the arguments
    assert!(region_args.is_empty());
    assert!(type_args.len() == 1);
    assert!(args.len() == 2);

    // For now we only support index on vectors
    // Retrieve the boxed value
    let arg_ty = type_args.get(0).unwrap(); // should be `Vec<...>`
    let arg_ty = match arg_ty.as_vec() {
        Option::Some(ty) => ty,
        Option::None => {
            panic!(
            "Index/IndexMut trait applied with parameter {:?} while it is only supported on Vec<T> values",
            arg_ty
        );
        }
    };

    let type_args = vec![arg_ty.clone()];
    let call = ast::Call {
        func: ast::FunId::Assumed(aid),
        region_args,
        type_args,
        const_generic_args,
        args,
        dest,
    };
    Ok(ast::RawTerminator::Call { call, target })
}

/// Small utility
pub(crate) fn check_impl_item(impl_item: &rustc_hir::Impl<'_>) {
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
    types_constraints: &TypesConstraintsMap,
    decl_ctx: &'ctx DeclTransContext<'tcx, 'ctx1>,
    def_id: DefId,
) -> (BodyTransContext<'tcx, 'ctx, 'ctx1>, ast::FunSig) {
    let tcx = decl_ctx.tcx;

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
    let mut bt_ctx = BodyTransContext::new(def_id, decl_ctx);

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
                let name = translate_region_name(&region);
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
    let inputs: Vec<ty::RTy> = Vec::from_iter(
        signature
            .inputs()
            .iter()
            .map(|ty| translate_sig_ty(&bt_ctx, ty).unwrap()),
    );
    let output = translate_sig_ty(&bt_ctx, &signature.output()).unwrap();

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
        const_generic_params: ty::ConstGenericVarId::Vector::new(), // TODO
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

fn translate_body(
    mut bt_ctx: BodyTransContext<'_, '_, '_>,
    local_id: LocalDefId,
    arg_count: usize,
) -> Result<ast::ExprBody> {
    let sess = bt_ctx.ft_ctx.sess;
    let tcx = bt_ctx.ft_ctx.tcx;

    let body = get_mir_for_def_id_and_level(tcx, local_id, bt_ctx.ft_ctx.mir_level);

    // Compute the meta information
    let meta = meta::get_meta_from_rspan(sess, &bt_ctx.ft_ctx.ordered.file_to_id, body.span);

    // Initialize the local variables
    trace!("Translating the body locals");
    translate_body_locals(&mut bt_ctx, body)?;

    // Translate the expression body
    trace!("Translating the expression body");
    translate_transparent_expression_body(&mut bt_ctx, body)?;

    // We need to convert the blocks map to an index vector
    let mut blocks = ast::BlockId::Vector::new();
    for (id, block) in bt_ctx.blocks {
        use crate::id_vector::ToUsize;
        // Sanity check to make sure we don't mess with the indices
        assert!(id.to_usize() == blocks.len());
        blocks.push_back(block);
    }

    // Create the body
    Ok(ast::ExprBody {
        meta,
        arg_count,
        locals: bt_ctx.vars,
        body: blocks,
    })
}

/// Translate one function.
fn translate_function(
    sess: &Session,
    tcx: TyCtxt,
    ordered: &OrderedDecls,
    types_constraints: &TypesConstraintsMap,
    type_defs: &ty::TypeDecls,
    fun_defs: &ast::FunDecls,
    global_defs: &ast::GlobalDecls,
    mir_level: MirLevel,
    def_id: ast::FunDeclId::Id,
) -> Result<ast::FunDecl> {
    trace!("{:?}", def_id);

    let info = ordered.decls_info.get(&AnyDeclId::Fun(def_id)).unwrap();
    trace!("About to translate function:\n{:?}", info.rid);

    // Compute the meta information
    let meta = meta::get_meta_from_rid(sess, tcx, &ordered.file_to_id, info.rid);

    // Initialize the function translation context
    let ft_ctx = DeclTransContext {
        sess,
        tcx,
        ordered,
        type_defs,
        fun_defs,
        global_defs,
        mir_level,
    };

    // Translate the function name
    let name = function_def_id_to_name(tcx, info.rid);

    // Translate the function signature and initialize the body translation context
    // at the same time (the signature gives us the region and type parameters,
    // that we put in the translation context).
    trace!("Translating function signature");
    let (bt_ctx, signature) = translate_function_signature(types_constraints, &ft_ctx, info.rid);

    // Check if the type is opaque or transparent
    let body = if !info.is_transparent || !info.is_local() {
        Option::None
    } else {
        Option::Some(translate_body(
            bt_ctx,
            info.rid.expect_local(),
            signature.inputs.len(),
        )?)
    };

    // Return the new function
    Ok(ast::FunDecl {
        meta,
        def_id,
        name,
        signature,
        body,
    })
}

/// Build an uninterpreted constant from a MIR constant identifier.
fn rid_as_unevaluated_constant<'tcx>(id: DefId) -> rustc_middle::mir::UnevaluatedConst<'tcx> {
    let p = mir_ty::List::empty();
    let did = mir_ty::WithOptConstParam::unknown(id);
    rustc_middle::mir::UnevaluatedConst::new(did, p)
}

/// Generate an expression body from a typed constant value.
fn global_generate_assignment_body(
    sess: &Session,
    tcx: TyCtxt,
    filename_to_id: &HashMap<FileName, FileId::Id>,
    ty: ty::ETy,
    def_rid: DefId,
    val: e::OperandConstantValue,
) -> ast::ExprBody {
    // Compute the meta information (we use the same everywhere)
    let meta = meta::get_meta_from_rid(sess, tcx, filename_to_id, def_rid);

    // # Variables
    // ret : ty
    let var = ast::Var {
        index: v::VarId::ZERO,
        name: None,
        ty: ty.clone(),
    };
    // # Instructions
    // ret := const (ty, val)
    // return
    let block = ast::BlockData {
        statements: vec![ast::Statement::new(
            meta,
            ast::RawStatement::Assign(
                e::Place::new(var.index),
                e::Rvalue::Use(e::Operand::Const(ty, val)),
            ),
        )],
        terminator: ast::Terminator::new(meta, ast::RawTerminator::Return),
    };
    ast::ExprBody {
        meta,
        arg_count: 0,
        locals: id_vector::Vector::from(vec![var]),
        body: id_vector::Vector::from(vec![block]),
    }
}

/// Translate one global.
fn translate_global(
    sess: &Session,
    tcx: TyCtxt,
    ordered: &OrderedDecls,
    _types_constraints: &TypesConstraintsMap,
    type_defs: &ty::TypeDecls,
    fun_defs: &ast::FunDecls,
    global_defs: &ast::GlobalDecls,
    mir_level: MirLevel,
    def_id: ast::GlobalDeclId::Id,
) -> Result<ast::GlobalDecl> {
    trace!("{:?}", def_id);

    let info = ordered.decls_info.get(&AnyDeclId::Global(def_id)).unwrap();
    trace!("About to translate global:\n{:?}", info.rid);

    // Compute the meta information
    let meta = meta::get_meta_from_rid(sess, tcx, &ordered.file_to_id, info.rid);

    // Initialize the global translation context
    let ft_ctx = DeclTransContext {
        sess,
        tcx,
        ordered,
        type_defs,
        fun_defs,
        global_defs,
        mir_level,
    };

    // Translate the global name
    let name = global_def_id_to_name(tcx, info.rid);

    trace!("Translating global type");
    let mir_ty = tcx.type_of(info.rid);

    let type_ = {
        let tt_ctx = TypeTransContext::new(
            info.rid,
            tcx,
            type_defs,
            global_defs,
            ordered,
            im::OrdMap::new(),
            im::OrdMap::new(),
            mir_level,
        );
        translate_types::translate_ety(&tt_ctx, &mir_ty)?
    };

    let bt_ctx = BodyTransContext::new(info.rid, &ft_ctx);
    let body = match (info.is_local(), info.is_transparent) {
        // It's a local and opaque global: we do not give it a body.
        (true, false) => Option::None,

        // It's a local and transparent global: we extract its body as for functions.
        (true, true) => Option::Some(translate_body(bt_ctx, info.rid.expect_local(), 0)?),

        // It's an external global.
        // The fact that it is listed among the declarations to extract means that
        // some local declaration depends on it.
        // Consequently, we try to evaluate its value.
        // If the evaluation succeeds, we generate a body.
        // If the evaluation fails, we warn about the failure and generate an
        // empty body.
        // TODO: Perhaps the policy should depend on `static` (accept) VS
        // `const` (reject) global ?  Or force a successful translation, but
        // translate only if it's transparent ?
        (false, _) => {
            let unev = rid_as_unevaluated_constant(info.rid);
            match tcx.const_eval_resolve(mir_ty::ParamEnv::empty(), unev, Option::None) {
                std::result::Result::Ok(c) => {
                    // Evaluate the constant
                    // We need a param_env: we use the expression def id as a dummy id...

                    let (ty, val) = translate_evaluated_operand_constant(
                        &bt_ctx.to_type_trans_context(),
                        &mir_ty,
                        &c,
                    );
                    Option::Some(global_generate_assignment_body(
                        sess,
                        tcx,
                        &ordered.file_to_id,
                        ty,
                        info.rid,
                        val,
                    ))
                }
                std::result::Result::Err(e) => {
                    warn!("Did not evaluate {:?}: {:?}", info.rid, e);
                    Option::None
                }
            }
        }
    };

    // Return the new global
    Ok(ast::GlobalDecl {
        def_id,
        meta,
        name,
        ty: type_,
        body,
    })
}

/// Translate the functions
pub fn translate_functions(
    sess: &Session,
    tcx: TyCtxt,
    ordered: &OrderedDecls,
    types_constraints: &TypesConstraintsMap,
    type_defs: &ty::TypeDecls,
    mir_level: MirLevel,
) -> Result<(ast::FunDecls, ast::GlobalDecls)> {
    let mut fun_defs = ast::FunDecls::new();
    let mut const_defs = ast::GlobalDecls::new();

    // Translate the bodies one at a time
    for decl in &ordered.decls {
        use crate::id_vector::ToUsize;
        match decl {
            DeclarationGroup::Fun(GDeclarationGroup::NonRec(def_id)) => {
                let fun_def = translate_function(
                    sess,
                    tcx,
                    ordered,
                    types_constraints,
                    type_defs,
                    &fun_defs,
                    &const_defs,
                    mir_level,
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
                        sess,
                        tcx,
                        ordered,
                        types_constraints,
                        type_defs,
                        &fun_defs,
                        &const_defs,
                        mir_level,
                        *def_id,
                    )?;
                    // We have to make sure we translate the definitions in the
                    // proper order, otherwise we mess with the vector of ids
                    assert!(def_id.to_usize() == fun_defs.len());
                    fun_defs.push_back(fun_def);
                }
            }
            DeclarationGroup::Global(GDeclarationGroup::NonRec(def_id)) => {
                let const_def = translate_global(
                    sess,
                    tcx,
                    ordered,
                    types_constraints,
                    type_defs,
                    &fun_defs,
                    &const_defs,
                    mir_level,
                    *def_id,
                )?;
                // We have to make sure we translate the definitions in the
                // proper order, otherwise we mess with the vector of ids
                assert!(def_id.to_usize() == const_defs.len());
                const_defs.push_back(const_def);
            }
            DeclarationGroup::Global(GDeclarationGroup::Rec(ids)) => {
                for def_id in ids {
                    let const_def = translate_global(
                        sess,
                        tcx,
                        ordered,
                        types_constraints,
                        type_defs,
                        &fun_defs,
                        &const_defs,
                        mir_level,
                        *def_id,
                    )?;
                    // We have to make sure we translate the definitions in the
                    // proper order, otherwise we mess with the vector of ids
                    assert!(def_id.to_usize() == const_defs.len());
                    const_defs.push_back(const_def);
                }
            }
            DeclarationGroup::Type(_) => {
                // Ignore the type declarations
                continue;
            }
        }
    }

    // Print the functions and constants
    for def in &fun_defs {
        trace!(
            "# Signature:\n{}\n\n# Function definition:\n{}\n",
            def.signature.fmt_with_decls(type_defs),
            def.fmt_with_decls(type_defs, &fun_defs, &const_defs)
        );
    }
    for def in &const_defs {
        trace!(
            "# Constant definition:\n{}\n",
            def.fmt_with_decls(type_defs, &fun_defs, &const_defs)
        );
    }

    Ok((fun_defs, const_defs))
}
