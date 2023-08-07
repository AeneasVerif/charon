//! The translation contexts.

#![allow(dead_code)]
use crate::formatter::Formatter;
use crate::get_mir::MirLevel;
use crate::rust_to_local_ids::*;
use crate::types as ty;
use crate::types::{LiteralTy, TypeDeclId};
use crate::ullbc_ast as ast;
use crate::values as v;
use rustc_hir::def_id::DefId;
use rustc_middle::mir;
use rustc_middle::mir::BasicBlock;
use rustc_middle::ty::TyCtxt;
use rustc_session::Session;

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
pub(crate) struct BodyTransContext<'tcx, 'ctx, 'ctx1> {
    /// This is used in very specific situations.
    pub def_id: DefId,
    /// The declarations translation context, containing the function and global definitions.
    /// Also contains the type translation context.
    pub ft_ctx: &'ctx DeclTransContext<'tcx, 'ctx1>,
    /// Region counter
    pub regions_counter: ty::RegionVarId::Generator,
    /// The regions
    pub regions: ty::RegionVarId::Vector<ty::RegionVar>,
    /// The map from rust region to translated region indices
    pub rregions_to_ids: im::OrdMap<rustc_middle::ty::RegionKind<'tcx>, ty::RegionVarId::Id>,
    /// Id counter for the type variables
    pub type_vars_counter: ty::TypeVarId::Generator,
    /// The type variables
    pub type_vars: ty::TypeVarId::Vector<ty::TypeVar>,
    /// The map from rust type variable indices to translated type variable
    /// indices.
    pub rtype_vars_to_ids: im::OrdMap<u32, ty::TypeVarId::Id>,
    /// Id counter for the variables
    pub vars_counter: v::VarId::Generator,
    /// The "regular" variables
    pub vars: v::VarId::Vector<ast::Var>,
    /// The map from rust variable indices to translated variables indices.
    pub rvars_to_ids: im::OrdMap<u32, v::VarId::Id>,
    /// Id counter for the const generic variables
    pub const_generic_counter: ty::ConstGenericVarId::Generator,
    /// The const generic variables
    pub const_generic_vars: ty::ConstGenericVarId::Vector<ty::ConstGenericVar>,
    /// The map from rust const generic variables to translate const generic
    /// variable indices.
    pub rconst_generic_vars_to_ids: im::OrdMap<u32, ty::ConstGenericVarId::Id>,
    /// Block id counter
    pub blocks_counter: ast::BlockId::Generator,
    /// The translated blocks. We can't use `ast::BlockId::Vector<ast::BlockData>`
    /// here because we might generate several fresh indices before actually
    /// adding the resulting blocks to the map.
    pub blocks: im::OrdMap<ast::BlockId::Id, ast::BlockData>,
    /// The map from rust blocks to translated blocks.
    /// Note that when translating terminators like DropAndReplace, we might have
    /// to introduce new blocks which don't appear in the original MIR.
    pub rblocks_to_ids: im::OrdMap<BasicBlock, ast::BlockId::Id>,
}

impl<'tcx, 'ctx> DeclTransContext<'tcx, 'ctx> {
    pub(crate) fn get_def_id_from_rid(&self, def_id: DefId) -> Option<ast::FunDeclId::Id> {
        self.ordered.fun_rid_to_id.get(&def_id).copied()
    }

    pub(crate) fn get_def_rid_from_id(&self, def_id: ast::FunDeclId::Id) -> Option<DefId> {
        self.ordered
            .decls_info
            .get(&AnyDeclId::Fun(def_id))
            .map(|i| i.rid)
    }
}

impl<'tcx, 'ctx, 'ctx1> BodyTransContext<'tcx, 'ctx, 'ctx1> {
    /// Create a new `ExecContext`.
    pub(crate) fn new(def_id: DefId, ft_ctx: &'ctx DeclTransContext<'tcx, 'ctx1>) -> Self {
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
            rconst_generic_vars_to_ids: im::OrdMap::new(),
            blocks_counter: ast::BlockId::Generator::new(),
            blocks: im::OrdMap::new(),
            rblocks_to_ids: im::OrdMap::new(),
        }
    }

    pub(crate) fn get_local(&self, local: &mir::Local) -> Option<v::VarId::Id> {
        self.rvars_to_ids.get(&local.as_u32()).copied()
    }

    pub(crate) fn get_block_id_from_rid(&self, rid: BasicBlock) -> Option<ast::BlockId::Id> {
        self.rblocks_to_ids.get(&rid).copied()
    }

    pub(crate) fn get_var_from_id(&self, var_id: v::VarId::Id) -> Option<&ast::Var> {
        self.vars.get(var_id)
    }

    pub(crate) fn get_region_from_rust(
        &self,
        r: rustc_middle::ty::RegionKind<'tcx>,
    ) -> Option<ty::RegionVarId::Id> {
        self.rregions_to_ids.get(&r).copied()
    }

    pub(crate) fn push_region(
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

    pub(crate) fn push_type_var(&mut self, rindex: u32, name: String) -> ty::TypeVarId::Id {
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

    pub(crate) fn push_var(&mut self, rid: u32, ty: ty::ETy, name: Option<String>) {
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

    pub(crate) fn push_const_generic_var(&mut self, rid: u32, ty: LiteralTy, name: String) {
        use crate::id_vector::ToUsize;
        let var_id = self.const_generic_counter.fresh_id();
        assert!(var_id.to_usize() == self.vars.len());
        let var = ty::ConstGenericVar {
            index: var_id,
            name,
            ty,
        };
        self.const_generic_vars.insert(var_id, var);
        self.rconst_generic_vars_to_ids.insert(rid, var_id);
    }

    pub(crate) fn fresh_block_id(&mut self, rid: BasicBlock) -> ast::BlockId::Id {
        let block_id = self.blocks_counter.fresh_id();
        self.rblocks_to_ids.insert(rid, block_id);
        block_id
    }

    pub(crate) fn push_block(&mut self, id: ast::BlockId::Id, block: ast::BlockData) {
        self.blocks.insert(id, block);
    }

    pub(crate) fn get_type_defs(&self) -> &ty::TypeDecls {
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

impl<'tcx, 'ctx, 'ctx1> Formatter<ty::GlobalDeclId::Id> for BodyTransContext<'tcx, 'ctx, 'ctx1> {
    fn format_object(&self, id: ty::GlobalDeclId::Id) -> String {
        self.ft_ctx.global_defs.format_object(id)
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
    pub(crate) fn to_type_trans_context(&self) -> TypeTransContext<'tcx, 'ctx> {
        TypeTransContext::new(
            // For the def id: we use the function/global def id
            self.def_id,
            self.ft_ctx.tcx,
            self.ft_ctx.type_defs,
            self.ft_ctx.global_defs,
            self.ft_ctx.ordered,
            self.rregions_to_ids.clone(),
            self.rtype_vars_to_ids.clone(),
            self.rconst_generic_vars_to_ids.clone(),
            self.ft_ctx.mir_level,
        )
    }
}

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
    /// The map from Rust const generic var identifiers to LLBC const generic vars
    pub const_generic_params_map: im::OrdMap<u32, ty::ConstGenericVarId::Id>,
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
        const_generic_params_map: im::OrdMap<u32, ty::ConstGenericVarId::Id>,
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
            const_generic_params_map,
            mir_level,
        }
    }

    pub fn get_id(&self, rid: DefId) -> TypeDeclId::Id {
        *self.ordered.type_rid_to_id.get(&rid).unwrap()
    }
}

/// Auxiliary definition used to format definitions.
pub(crate) struct TypeDeclFormatter<'a> {
    pub type_defs: &'a ty::TypeDecls,
    pub global_defs: &'a ast::GlobalDecls,
    /// The region parameters of the definition we are printing (needed to
    /// correctly pretty print region var ids)
    pub region_params: &'a ty::RegionVarId::Vector<ty::RegionVar>,
    /// The type parameters of the definition we are printing (needed to
    /// correctly pretty print type var ids)
    pub type_params: &'a ty::TypeVarId::Vector<ty::TypeVar>,
    /// The const generic parameters of the definition we are printing (needed to
    /// correctly pretty print type var ids)
    pub const_generic_params: &'a ty::ConstGenericVarId::Vector<ty::ConstGenericVar>,
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

impl<'a> Formatter<ty::GlobalDeclId::Id> for TypeDeclFormatter<'a> {
    fn format_object(&self, id: ty::GlobalDeclId::Id) -> String {
        self.global_defs.format_object(id)
    }
}

impl<'tcx, 'ctx> Formatter<&ty::TypeDecl> for TypeTransContext<'tcx, 'ctx> {
    fn format_object(&self, def: &ty::TypeDecl) -> String {
        // Create a type def formatter (which will take care of the
        // type parameters)
        let formatter = TypeDeclFormatter {
            type_defs: self.type_defs,
            global_defs: self.global_defs,
            region_params: &def.region_params,
            type_params: &def.type_params,
            const_generic_params: &def.const_generic_params,
        };
        formatter.format_object(def)
    }
}
