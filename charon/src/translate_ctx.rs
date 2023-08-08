//! The translation contexts.

#![allow(dead_code)]
use crate::formatter::Formatter;
use crate::get_mir::MirLevel;
use crate::meta::{get_meta_from_rid, get_meta_from_rspan, FileId, FileName, Meta};
use crate::names::Name;
use crate::reorder_decls::{AnyRustId, AnyTransId};
use crate::types as ty;
use crate::types::LiteralTy;
use crate::ullbc_ast as ast;
use crate::values as v;
use linked_hash_set::LinkedHashSet;
use rustc_hir::def_id::DefId;
use rustc_middle::mir;
use rustc_middle::mir::BasicBlock;
use rustc_middle::ty::TyCtxt;
use rustc_session::Session;
use std::collections::{HashMap, HashSet};

pub struct CrateInfo {
    pub crate_name: String,
    pub opaque_mods: HashSet<String>,
}

impl CrateInfo {
    pub(crate) fn is_opaque_decl(&self, name: &Name) -> bool {
        name.is_in_modules(&self.crate_name, &self.opaque_mods)
    }

    fn is_transparent_decl(&self, name: &Name) -> bool {
        !self.is_opaque_decl(name)
    }
}

/// Translation context containing the top-level definitions.
pub struct TransCtx<'tcx, 'ctx> {
    /// The compiler session
    pub sess: &'ctx Session,
    ///
    pub tcx: TyCtxt<'tcx>,
    /// The level at which to extract the MIR
    pub mir_level: MirLevel,
    ///
    pub crate_info: CrateInfo,
    /// All the ids
    pub all_ids: LinkedHashSet<AnyTransId>,
    /// The declarations we came accross and which we haven't translated yet
    pub stack: LinkedHashSet<AnyRustId>,
    /// File names to ids and vice-versa
    pub file_to_id: HashMap<FileName, FileId::Id>,
    pub id_to_file: HashMap<FileId::Id, FileName>,
    /// The map from Rust type ids to translated type ids
    pub type_id_map: ty::TypeDeclId::MapGenerator<DefId>,
    /// The translated type definitions
    pub type_defs: ty::TypeDecls,
    /// The map from Rust function ids to translated function ids
    pub fun_id_map: ast::FunDeclId::MapGenerator<DefId>,
    /// The translated function definitions
    pub fun_defs: ast::FunDecls,
    /// The map from Rust global ids to translated global ids
    pub global_id_map: ast::GlobalDeclId::MapGenerator<DefId>,
    /// The translated global definitions
    pub global_defs: ast::GlobalDecls,
}

/// A translation context for type/global/function bodies.
/// Simply augments the [TransCtx] with local variables.
///
/// TODO: use other collections than `im::OrdMap`? (we don't need a O(1) clone
/// operation).
/// TODO: remove the borrow for the TransCtx, or make it a mutable borrow.
pub(crate) struct BodyTransCtx<'tcx, 'ctx, 'ctx1> {
    /// This is used in very specific situations.
    pub def_id: DefId,
    /// The translation context containing the top-level definitions/ids.
    pub t_ctx: &'ctx mut TransCtx<'tcx, 'ctx1>,
    /// Region counter
    pub regions_counter: ty::RegionVarId::Generator,
    /// The regions - TODO: rename to region_vars
    pub region_vars: ty::RegionVarId::Vector<ty::RegionVar>,
    // TODO: use the MapGenerator types
    /// The map from rust region to translated region indices
    pub region_vars_map: im::OrdMap<rustc_middle::ty::RegionKind<'tcx>, ty::RegionVarId::Id>,
    /// Id counter for the type variables
    pub type_vars_counter: ty::TypeVarId::Generator,
    /// The type variables
    pub type_vars: ty::TypeVarId::Vector<ty::TypeVar>,
    /// The map from rust type variable indices to translated type variable
    /// indices.
    pub type_vars_map: im::OrdMap<u32, ty::TypeVarId::Id>,
    /// Id counter for the variables
    pub vars_counter: v::VarId::Generator,
    /// The "regular" variables
    pub vars: v::VarId::Vector<ast::Var>,
    /// The map from rust variable indices to translated variables indices.
    pub vars_map: im::OrdMap<u32, v::VarId::Id>,
    /// Id counter for the const generic variables
    pub const_generic_counter: ty::ConstGenericVarId::Generator,
    /// The const generic variables
    pub const_generic_vars: ty::ConstGenericVarId::Vector<ty::ConstGenericVar>,
    /// The map from rust const generic variables to translate const generic
    /// variable indices.
    pub const_generic_vars_map: im::OrdMap<u32, ty::ConstGenericVarId::Id>,
    /// Block id counter
    pub blocks_counter: ast::BlockId::Generator,
    /// The translated blocks. We can't use `ast::BlockId::Vector<ast::BlockData>`
    /// here because we might generate several fresh indices before actually
    /// adding the resulting blocks to the map.
    pub blocks: im::OrdMap<ast::BlockId::Id, ast::BlockData>,
    /// The map from rust blocks to translated blocks.
    /// Note that when translating terminators like DropAndReplace, we might have
    /// to introduce new blocks which don't appear in the original MIR.
    pub blocks_map: im::OrdMap<BasicBlock, ast::BlockId::Id>,
}

impl<'tcx, 'ctx> TransCtx<'tcx, 'ctx> {
    pub(crate) fn get_meta_from_rid(&self, def_id: DefId) -> Meta {
        get_meta_from_rid(&self.sess, self.tcx, &self.file_to_id, def_id)
    }

    pub(crate) fn get_meta_from_rspan(&self, rspan: rustc_span::Span) -> Meta {
        get_meta_from_rspan(&self.sess, &self.file_to_id, rspan)
    }

    pub(crate) fn id_is_opaque(&self, id: DefId) -> bool {
        let name = crate::names_utils::item_def_id_to_name(self.tcx, id);
        self.crate_info.is_opaque_decl(&name)
    }

    pub(crate) fn id_is_transparent(&self, id: DefId) -> bool {
        !self.id_is_opaque(id)
    }

    pub(crate) fn push_id(&mut self, _rust_id: DefId, id: AnyRustId, trans_id: AnyTransId) {
        // Add the id to the stack of declarations to translate
        self.stack.insert(id);
        self.all_ids.insert(trans_id);
    }

    pub(crate) fn register_type_decl_id(&mut self, id: DefId) -> ty::TypeDeclId::Id {
        match self.type_id_map.get(id) {
            Option::Some(id) => id,
            Option::None => {
                let rid = AnyRustId::Type(id);
                let trans_id = self.type_id_map.insert(id);
                self.push_id(id, rid, AnyTransId::Type(trans_id));
                trans_id
            }
        }
    }

    pub(crate) fn translate_type_decl_id(&mut self, id: DefId) -> ty::TypeDeclId::Id {
        self.register_type_decl_id(id)
    }

    pub(crate) fn register_fun_decl_id(&mut self, id: DefId) -> ast::FunDeclId::Id {
        match self.fun_id_map.get(id) {
            Option::Some(id) => id,
            Option::None => {
                let rid = AnyRustId::Fun(id);
                let trans_id = self.fun_id_map.insert(id);
                self.push_id(id, rid, AnyTransId::Fun(trans_id));
                trans_id
            }
        }
    }

    pub(crate) fn translate_fun_decl_id(&mut self, id: DefId) -> ast::FunDeclId::Id {
        self.register_fun_decl_id(id)
    }

    pub(crate) fn register_global_decl_id(&mut self, id: DefId) -> ty::GlobalDeclId::Id {
        match self.global_id_map.get(id) {
            Option::Some(id) => id,
            Option::None => {
                let rid = AnyRustId::Global(id);
                let trans_id = self.global_id_map.insert(id);
                self.push_id(id, rid, AnyTransId::Global(trans_id));
                trans_id
            }
        }
    }

    pub(crate) fn translate_global_decl_id(&mut self, id: DefId) -> ast::GlobalDeclId::Id {
        self.register_global_decl_id(id)
    }
}

impl<'tcx, 'ctx, 'ctx1> BodyTransCtx<'tcx, 'ctx, 'ctx1> {
    /// Create a new `ExecContext`.
    pub(crate) fn new(def_id: DefId, t_ctx: &'ctx mut TransCtx<'tcx, 'ctx1>) -> Self {
        BodyTransCtx {
            def_id,
            t_ctx,
            regions_counter: ty::RegionVarId::Generator::new(),
            region_vars: ty::RegionVarId::Vector::new(),
            region_vars_map: im::OrdMap::new(),
            type_vars_counter: ty::TypeVarId::Generator::new(),
            type_vars: ty::TypeVarId::Vector::new(),
            type_vars_map: im::OrdMap::new(),
            vars_counter: v::VarId::Generator::new(),
            vars: v::VarId::Vector::new(),
            vars_map: im::OrdMap::new(),
            const_generic_counter: ty::ConstGenericVarId::Generator::new(),
            const_generic_vars: ty::ConstGenericVarId::Vector::new(),
            const_generic_vars_map: im::OrdMap::new(),
            blocks_counter: ast::BlockId::Generator::new(),
            blocks: im::OrdMap::new(),
            blocks_map: im::OrdMap::new(),
        }
    }

    pub(crate) fn get_meta_from_rid(&self, def_id: DefId) -> Meta {
        self.t_ctx.get_meta_from_rid(def_id)
    }

    pub(crate) fn get_meta_from_rspan(&self, rspan: rustc_span::Span) -> Meta {
        self.t_ctx.get_meta_from_rspan(rspan)
    }

    pub(crate) fn get_local(&self, local: &mir::Local) -> Option<v::VarId::Id> {
        self.vars_map.get(&local.as_u32()).copied()
    }

    pub(crate) fn get_block_id_from_rid(&self, rid: BasicBlock) -> Option<ast::BlockId::Id> {
        self.blocks_map.get(&rid).copied()
    }

    pub(crate) fn get_var_from_id(&self, var_id: v::VarId::Id) -> Option<&ast::Var> {
        self.vars.get(var_id)
    }

    pub(crate) fn register_type_decl_id(&mut self, id: DefId) -> ty::TypeDeclId::Id {
        self.t_ctx.register_type_decl_id(id)
    }

    pub(crate) fn translate_type_decl_id(&mut self, id: DefId) -> ty::TypeDeclId::Id {
        self.t_ctx.translate_type_decl_id(id)
    }

    pub(crate) fn register_fun_decl_id(&mut self, id: DefId) -> ast::FunDeclId::Id {
        self.t_ctx.register_fun_decl_id(id)
    }

    pub(crate) fn translate_fun_decl_id(&mut self, id: DefId) -> ast::FunDeclId::Id {
        self.t_ctx.translate_fun_decl_id(id)
    }

    pub(crate) fn register_global_decl_id(&mut self, id: DefId) -> ty::GlobalDeclId::Id {
        self.t_ctx.register_global_decl_id(id)
    }

    pub(crate) fn translate_global_decl_id(&mut self, id: DefId) -> ast::GlobalDeclId::Id {
        self.t_ctx.translate_global_decl_id(id)
    }

    pub(crate) fn get_region_from_rust(
        &self,
        r: rustc_middle::ty::RegionKind<'tcx>,
    ) -> Option<ty::RegionVarId::Id> {
        self.region_vars_map.get(&r).copied()
    }

    pub(crate) fn push_region(
        &mut self,
        r: rustc_middle::ty::RegionKind<'tcx>,
        name: Option<String>,
    ) -> ty::RegionVarId::Id {
        use crate::id_vector::ToUsize;
        let rid = self.regions_counter.fresh_id();
        assert!(rid.to_usize() == self.region_vars.len());
        let var = ty::RegionVar { index: rid, name };
        self.region_vars.insert(rid, var);
        self.region_vars_map.insert(r, rid);
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
        self.type_vars_map.insert(rindex, var_id);
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
        self.vars_map.insert(rid, var_id);
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
        self.const_generic_vars_map.insert(rid, var_id);
    }

    pub(crate) fn fresh_block_id(&mut self, rid: BasicBlock) -> ast::BlockId::Id {
        let block_id = self.blocks_counter.fresh_id();
        self.blocks_map.insert(rid, block_id);
        block_id
    }

    pub(crate) fn push_block(&mut self, id: ast::BlockId::Id, block: ast::BlockData) {
        self.blocks.insert(id, block);
    }

    pub(crate) fn get_type_defs(&self) -> &ty::TypeDecls {
        &self.t_ctx.type_defs
    }
}

impl<'tcx, 'ctx> Formatter<ty::TypeDeclId::Id> for TransCtx<'tcx, 'ctx> {
    fn format_object(&self, id: ty::TypeDeclId::Id) -> String {
        self.type_defs.format_object(id)
    }
}

impl<'tcx, 'ctx, 'ctx1> Formatter<ty::TypeVarId::Id> for BodyTransCtx<'tcx, 'ctx, 'ctx1> {
    fn format_object(&self, id: ty::TypeVarId::Id) -> String {
        let v = self.type_vars.get(id).unwrap();
        v.to_string()
    }
}

impl<'tcx, 'ctx, 'ctx1> Formatter<v::VarId::Id> for BodyTransCtx<'tcx, 'ctx, 'ctx1> {
    fn format_object(&self, id: v::VarId::Id) -> String {
        let v = self.vars.get(id).unwrap();
        v.to_string()
    }
}

impl<'tcx, 'ctx, 'ctx1> Formatter<ty::RegionVarId::Id> for BodyTransCtx<'tcx, 'ctx, 'ctx1> {
    fn format_object(&self, id: ty::RegionVarId::Id) -> String {
        let v = self.region_vars.get(id).unwrap();
        v.to_string()
    }
}

impl<'tcx, 'ctx, 'ctx1> Formatter<&ty::Region<ty::RegionVarId::Id>>
    for BodyTransCtx<'tcx, 'ctx, 'ctx1>
{
    fn format_object(&self, r: &ty::Region<ty::RegionVarId::Id>) -> String {
        r.fmt_with_ctx(self)
    }
}

impl<'tcx, 'ctx, 'ctx1> Formatter<ty::ConstGenericVarId::Id> for BodyTransCtx<'tcx, 'ctx, 'ctx1> {
    fn format_object(&self, id: ty::ConstGenericVarId::Id) -> String {
        let v = self.const_generic_vars.get(id).unwrap();
        v.to_string()
    }
}

impl<'tcx, 'ctx, 'ctx1> Formatter<&ty::ErasedRegion> for BodyTransCtx<'tcx, 'ctx, 'ctx1> {
    fn format_object(&self, _: &ty::ErasedRegion) -> String {
        "'_".to_owned()
    }
}

impl<'tcx, 'ctx, 'ctx1> Formatter<ty::TypeDeclId::Id> for BodyTransCtx<'tcx, 'ctx, 'ctx1> {
    fn format_object(&self, id: ty::TypeDeclId::Id) -> String {
        self.t_ctx.type_defs.format_object(id)
    }
}

impl<'tcx, 'ctx, 'ctx1> Formatter<ty::GlobalDeclId::Id> for BodyTransCtx<'tcx, 'ctx, 'ctx1> {
    fn format_object(&self, id: ty::GlobalDeclId::Id) -> String {
        self.t_ctx.global_defs.format_object(id)
    }
}

impl<'tcx, 'ctx, 'ctx1> Formatter<&ty::Ty<ty::Region<ty::RegionVarId::Id>>>
    for BodyTransCtx<'tcx, 'ctx, 'ctx1>
{
    fn format_object(&self, ty: &ty::Ty<ty::Region<ty::RegionVarId::Id>>) -> String {
        ty.fmt_with_ctx(self)
    }
}

impl<'tcx, 'ctx, 'ctx1> Formatter<&ty::Ty<ty::ErasedRegion>> for BodyTransCtx<'tcx, 'ctx, 'ctx1> {
    fn format_object(&self, ty: &ty::Ty<ty::ErasedRegion>) -> String {
        ty.fmt_with_ctx(self)
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

impl<'tcx, 'ctx, 'ctx1> Formatter<&ty::TypeDecl> for BodyTransCtx<'tcx, 'ctx, 'ctx1> {
    fn format_object(&self, def: &ty::TypeDecl) -> String {
        // Create a type def formatter (which will take care of the
        // type parameters)
        let formatter = TypeDeclFormatter {
            type_defs: &self.t_ctx.type_defs,
            global_defs: &self.t_ctx.global_defs,
            region_params: &def.region_params,
            type_params: &def.type_params,
            const_generic_params: &def.const_generic_params,
        };
        formatter.format_object(def)
    }
}
