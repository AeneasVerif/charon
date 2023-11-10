//! The translation contexts.

#![allow(dead_code)]
use crate::common::TAB_INCR;
use crate::formatter::Formatter;
use crate::gast;
use crate::get_mir::MirLevel;
use crate::llbc_ast;
use crate::meta;
use crate::meta::{FileId, FileName, LocalFileId, Meta, VirtualFileId};
use crate::names::Name;
use crate::reorder_decls::AnyTransId;
use crate::translate_predicates::NonLocalTraitClause;
use crate::types::*;
use crate::ullbc_ast;
use crate::ullbc_ast as ast;
use crate::values::*;
use hax_frontend_exporter as hax;
use hax_frontend_exporter::SInto;
use im::OrdMap;
use linked_hash_set::LinkedHashSet;
use macros::VariantIndexArity;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use rustc_session::Session;
use std::cmp::{Ord, Ordering, PartialOrd};
use std::collections::{BTreeSet, HashMap, HashSet};
use std::fmt;

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

/// We use a special type to store the Rust identifiers in the stack, to
/// make sure we translate them in a specific order (top-level constants
/// before constant functions before functions...). This allows us to
/// avoid stealing issues when looking up the MIR bodies.
#[derive(Clone, Copy, Debug, Eq, PartialEq, VariantIndexArity)]
pub enum OrdRustId {
    Global(DefId),
    ConstFun(DefId),
    TraitDecl(DefId),
    TraitImpl(DefId),
    Fun(DefId),
    Type(DefId),
}

impl OrdRustId {
    fn get_id(&self) -> DefId {
        match self {
            OrdRustId::Global(id)
            | OrdRustId::ConstFun(id)
            | OrdRustId::TraitDecl(id)
            | OrdRustId::TraitImpl(id)
            | OrdRustId::Fun(id)
            | OrdRustId::Type(id) => *id,
        }
    }
}

impl PartialOrd for OrdRustId {
    fn partial_cmp(&self, other: &OrdRustId) -> Option<Ordering> {
        let (vid0, _) = self.variant_index_arity();
        let (vid1, _) = other.variant_index_arity();
        if vid0 != vid1 {
            Option::Some(vid0.cmp(&vid1))
        } else {
            let id0 = self.get_id();
            let id1 = other.get_id();
            Option::Some(id0.cmp(&id1))
        }
    }
}

impl Ord for OrdRustId {
    fn cmp(&self, other: &OrdRustId) -> Ordering {
        self.partial_cmp(other).unwrap()
    }
}

/// Translation context containing the top-level definitions.
pub struct TransCtx<'tcx, 'ctx> {
    /// The compiler session
    pub sess: &'ctx Session,
    /// The Rust compiler type context
    pub tcx: TyCtxt<'tcx>,
    /// The Hax context
    pub hax_state: hax::State<hax::Base<'tcx>, (), (), ()>,
    /// The level at which to extract the MIR
    pub mir_level: MirLevel,
    ///
    pub crate_info: CrateInfo,
    /// Do not abort on failure and attempt to extract as much as possible.
    pub continue_on_failure: bool,
    /// Error out if some code ends up being duplicated by the control-flow
    /// reconstruction (note that because several patterns in a match may lead
    /// to the same branch, it is node always possible not to duplicate code).
    pub no_code_duplication: bool,
    /// All the ids, in the order in which we encountered them
    pub all_ids: LinkedHashSet<AnyTransId>,
    /// The declarations we came accross and which we haven't translated yet.
    /// We use an ordered set to make sure we translate them in a specific
    /// order (this avoids stealing issues when querying the MIR bodies).
    pub stack: BTreeSet<OrdRustId>,
    /// File names to ids and vice-versa
    pub file_to_id: HashMap<FileName, FileId::Id>,
    pub id_to_file: HashMap<FileId::Id, FileName>,
    pub real_file_counter: LocalFileId::Generator,
    pub virtual_file_counter: VirtualFileId::Generator,
    /// The map from Rust type ids to translated type ids
    pub type_id_map: TypeDeclId::MapGenerator<DefId>,
    /// The translated type definitions
    pub type_defs: TypeDecls,
    /// The map from Rust function ids to translated function ids
    pub fun_id_map: ast::FunDeclId::MapGenerator<DefId>,
    /// The translated function definitions
    pub fun_defs: ast::FunDecls,
    /// The map from Rust global ids to translated global ids
    pub global_id_map: ast::GlobalDeclId::MapGenerator<DefId>,
    /// The translated global definitions
    pub global_defs: ast::GlobalDecls,
    /// The map from Rust trait decl ids to translated trait decl ids
    pub trait_decl_id_map: ast::TraitDeclId::MapGenerator<DefId>,
    /// The translated trait declarations
    pub trait_decls: ast::TraitDecls,
    /// The map from Rust trait impls ids to translated trait impls ids
    pub trait_impl_id_map: ast::TraitImplId::MapGenerator<DefId>,
    pub trait_impl_id_to_def_id: HashMap<ast::TraitImplId::Id, DefId>,
    /// The translated trait declarations
    pub trait_impls: ast::TraitImpls,
}

/// A translation context for type/global/function bodies.
/// Simply augments the [TransCtx] with local variables.
///
/// Remark: for now we don't really need to use collections from the [im] crate,
/// because we don't need the O(1) clone operation, but we may need it once we
/// implement support for universally quantified traits, where we might need
/// to be able to dive in/out of universal quantifiers. Also, it doesn't cost
/// us to use those collections.
pub(crate) struct BodyTransCtx<'tcx, 'ctx, 'ctx1> {
    /// This is used in very specific situations. TODO: remove?
    pub def_id: DefId,
    /// The translation context containing the top-level definitions/ids.
    pub t_ctx: &'ctx mut TransCtx<'tcx, 'ctx1>,
    /// A hax state with an owner id
    pub hax_state: hax::State<hax::Base<'tcx>, (), (), rustc_hir::def_id::DefId>,
    /// The regions
    pub region_vars: RegionVarId::Vector<RegionVar>,
    /// The map from rust region to translated region indices
    pub region_vars_map: RegionVarId::MapGenerator<hax::Region>,
    /// The type variables
    pub type_vars: TypeVarId::Vector<TypeVar>,
    /// The map from rust type variable indices to translated type variable
    /// indices.
    pub type_vars_map: TypeVarId::MapGenerator<u32>,
    /// The "regular" variables
    pub vars: VarId::Vector<ast::Var>,
    /// The map from rust variable indices to translated variables indices.
    pub vars_map: VarId::MapGenerator<usize>,
    /// The const generic variables
    pub const_generic_vars: ConstGenericVarId::Vector<ConstGenericVar>,
    /// The map from rust const generic variables to translate const generic
    /// variable indices.
    pub const_generic_vars_map: ConstGenericVarId::MapGenerator<u32>,
    /// A generator for trait instance ids.
    /// We initialize it so that it generates ids for local clauses.
    pub trait_instance_id_gen: Box<dyn FnMut() -> TraitInstanceId>,
    /// All the trait clauses accessible from the current environment
    pub trait_clauses: OrdMap<TraitInstanceId, NonLocalTraitClause>,
    /// If [true] it means we are currently registering trait clauses in the
    /// local context. As a consequence, we allow not solving all the trait
    /// obligations, because the obligations for some clauses may be solved
    /// by other clauses which have not been registered yet.
    /// For this reason, we do the resolution in several passes.
    pub registering_trait_clauses: bool,
    ///
    pub types_outlive: Vec<TypeOutlives>,
    ///
    pub regions_outlive: Vec<RegionOutlives>,
    ///
    pub trait_type_constraints: Vec<RTraitTypeConstraint>,
    /// The translated blocks. We can't use `ast::BlockId::Vector<ast::BlockData>`
    /// here because we might generate several fresh indices before actually
    /// adding the resulting blocks to the map.
    pub blocks: im::OrdMap<ast::BlockId::Id, ast::BlockData>,
    /// The map from rust blocks to translated blocks.
    /// Note that when translating terminators like DropAndReplace, we might have
    /// to introduce new blocks which don't appear in the original MIR.
    pub blocks_map: ast::BlockId::MapGenerator<hax::BasicBlock>,
    ///
    /// The stack of late-bound parameters (can only be lifetimes for now), which
    /// use DeBruijn indices (the other parameters use free variables).
    /// For explanations about what early-bound and late-bound parameters are, see:
    /// https://smallcultfollowing.com/babysteps/blog/2013/10/29/intermingled-parameter-lists/
    /// https://smallcultfollowing.com/babysteps/blog/2013/11/04/intermingled-parameter-lists/
    ///
    /// Remark: even though performance is not critical, the use of [im::Vec] allows
    /// us to push/pop and access indexed elements with very good performance.
    ///
    /// **Important**:
    /// ==============
    /// The Rust compiler uses De Bruijn indices to identify the *group* of
    /// universally quantified variables, and variable identifiers to identity
    /// the variables inside the group.
    ///
    /// For instance, we have the following:
    /// ```text
    ///                     we compute the De Bruijn indices from here
    ///                            VVVVVVVVVVVVVVVVVVVVVVV
    /// fn f<'a, 'b>(x: for<'c> fn(&'a u8, &'b u16, &'c u32) -> u64) {}
    ///      ^^^^^^         ^^       ^       ^        ^
    ///        |      De Bruijn: 0   |       |        |
    ///  De Bruijn: 1                |       |        |
    ///                        De Bruijn: 1  |    De Bruijn: 0
    ///                           Var id: 0  |       Var id: 0
    ///                                      |
    ///                                De Bruijn: 1
    ///                                   Var id: 1
    /// ```
    ///
    /// For this reason, we use a stack of vectors to store the bound variables.
    pub bound_vars: im::Vector<im::Vector<RegionVarId::Id>>,
}

/// A formatting context for type/global/function bodies.
/// Simply augments the [TransCtx] with local variables.
///
/// We can directly use the [TransCtx] and the [BodyTransCtx] for formatting.
/// However, sometimes we only have a [TransCtx] at our disposal when formatting
/// a definition. We could transform it into a [BodyTransCtx] by adding the
/// proper information, but this requires a mutable access to the [TransCtx].
/// Instead, we can create a [BodyFormatCtx].
pub(crate) struct BodyFormatCtx<'tcx, 'ctx, 'ctx1> {
    /// The translation context containing the top-level definitions/ids.
    pub t_ctx: &'ctx TransCtx<'tcx, 'ctx1>,
    pub generics: &'ctx GenericParams,
    /// The "regular" variables
    pub vars: &'ctx VarId::Vector<ast::Var>,
    ///
    pub trait_clauses: &'ctx TraitClauseId::Vector<TraitClause>,
}

impl<'tcx, 'ctx> TransCtx<'tcx, 'ctx> {
    /// Register a file if it is a "real" file and was not already registered
    fn register_file(&mut self, filename: FileName) -> FileId::Id {
        // Lookup the file if it was already registered
        match self.file_to_id.get(&filename) {
            Option::Some(id) => *id,
            Option::None => {
                // Generate the fresh id
                let id = match &filename {
                    FileName::Local(_) => FileId::Id::LocalId(self.real_file_counter.fresh_id()),
                    FileName::Virtual(_) => {
                        FileId::Id::VirtualId(self.virtual_file_counter.fresh_id())
                    }
                    FileName::NotReal(_) => unimplemented!(),
                };
                self.file_to_id.insert(filename.clone(), id);
                self.id_to_file.insert(id, filename);
                id
            }
        }
    }

    /// Compute the meta information for a Rust definition identified by its id.
    pub(crate) fn translate_meta_from_rid(&mut self, def_id: DefId) -> Meta {
        // Retrieve the span from the def id
        let rspan = meta::get_rspan_from_def_id(self.tcx, def_id);
        let rspan = rspan.sinto(&self.hax_state);
        self.translate_meta_from_rspan(rspan)
    }

    pub fn translate_span(&mut self, rspan: hax::Span) -> meta::Span {
        let filename = meta::convert_filename(&rspan.filename);
        let file_id = match &filename {
            FileName::NotReal(_) => {
                // For now we forbid not real filenames
                unimplemented!();
            }
            FileName::Virtual(_) | FileName::Local(_) => self.register_file(filename),
        };

        let beg = meta::convert_loc(rspan.lo);
        let end = meta::convert_loc(rspan.hi);

        // Put together
        meta::Span { file_id, beg, end }
    }

    /// Compute meta data from a Rust source scope
    pub fn translate_meta_from_source_info(
        &mut self,
        source_scopes: &hax::IndexVec<hax::SourceScope, hax::SourceScopeData>,
        source_info: &hax::SourceInfo,
    ) -> Meta {
        // Translate the span
        let mut scope_data = source_scopes.get(source_info.scope).unwrap();
        let span = self.translate_span(scope_data.span.clone());

        // Lookup the top-most inlined parent scope.
        if scope_data.inlined_parent_scope.is_some() {
            while scope_data.inlined_parent_scope.is_some() {
                let parent_scope = scope_data.inlined_parent_scope.unwrap();
                scope_data = source_scopes.get(parent_scope).unwrap();
            }

            let parent_span = self.translate_span(scope_data.span.clone());

            Meta {
                span: parent_span,
                generated_from_span: Some(span),
            }
        } else {
            Meta {
                span,
                generated_from_span: None,
            }
        }
    }

    // TODO: rename
    pub(crate) fn translate_meta_from_rspan(&mut self, rspan: hax::Span) -> Meta {
        // Translate the span
        let span = self.translate_span(rspan);

        Meta {
            span,
            generated_from_span: None,
        }
    }

    pub(crate) fn id_is_opaque(&self, id: DefId) -> bool {
        let name = crate::names_utils::item_def_id_to_name(self.tcx, id);
        self.crate_info.is_opaque_decl(&name)
    }

    pub(crate) fn id_is_transparent(&self, id: DefId) -> bool {
        !self.id_is_opaque(id)
    }

    pub(crate) fn push_id(&mut self, _rust_id: DefId, id: OrdRustId, trans_id: AnyTransId) {
        // Add the id to the stack of declarations to translate
        self.stack.insert(id);
        self.all_ids.insert(trans_id);
    }

    pub(crate) fn register_type_decl_id(&mut self, id: DefId) -> TypeDeclId::Id {
        match self.type_id_map.get(&id) {
            Option::Some(id) => id,
            Option::None => {
                let rid = OrdRustId::Type(id);
                let trans_id = self.type_id_map.insert(id);
                self.push_id(id, rid, AnyTransId::Type(trans_id));
                trans_id
            }
        }
    }

    pub(crate) fn translate_type_decl_id(&mut self, id: DefId) -> TypeDeclId::Id {
        self.register_type_decl_id(id)
    }

    // TODO: factor out all the "register_..." functions
    pub(crate) fn register_fun_decl_id(&mut self, id: DefId) -> ast::FunDeclId::Id {
        match self.fun_id_map.get(&id) {
            Option::Some(id) => id,
            Option::None => {
                let rid = if self.tcx.is_const_fn_raw(id) {
                    OrdRustId::ConstFun(id)
                } else {
                    OrdRustId::Fun(id)
                };
                let trans_id = self.fun_id_map.insert(id);
                self.push_id(id, rid, AnyTransId::Fun(trans_id));
                trans_id
            }
        }
    }

    /// Returns an [Option] because we may ignore some builtin or auto traits
    /// like [core::marker::Sized] or [core::marker::Sync].
    pub(crate) fn register_trait_decl_id(&mut self, id: DefId) -> Option<ast::TraitDeclId::Id> {
        use crate::assumed;
        if assumed::IGNORE_BUILTIN_MARKER_TRAITS {
            let name = crate::names::item_def_id_to_name(self.tcx, id);
            if assumed::is_marker_trait(&name) {
                return None;
            }
        }

        match self.trait_decl_id_map.get(&id) {
            Option::Some(id) => Some(id),
            Option::None => {
                let rid = OrdRustId::TraitDecl(id);
                let trans_id = self.trait_decl_id_map.insert(id);
                self.push_id(id, rid, AnyTransId::TraitDecl(trans_id));
                Some(trans_id)
            }
        }
    }

    /// Returns an [Option] because we may ignore some builtin or auto traits
    /// like [core::marker::Sized] or [core::marker::Sync].
    pub(crate) fn register_trait_impl_id(
        &mut self,
        rust_id: DefId,
    ) -> Option<ast::TraitImplId::Id> {
        // Check if we need to filter
        {
            // Retrieve the id of the implemented trait decl
            let id = self.tcx.trait_id_of_impl(rust_id).unwrap();
            if self.register_trait_decl_id(id).is_none() {
                return None;
            }
        }

        match self.trait_impl_id_map.get(&rust_id) {
            Option::Some(id) => Some(id),
            Option::None => {
                let rid = OrdRustId::TraitImpl(rust_id);
                let trans_id = self.trait_impl_id_map.insert(rust_id);
                self.trait_impl_id_to_def_id.insert(trans_id, rust_id);
                self.push_id(rust_id, rid, AnyTransId::TraitImpl(trans_id));
                Some(trans_id)
            }
        }
    }

    pub(crate) fn translate_fun_decl_id(&mut self, id: DefId) -> ast::FunDeclId::Id {
        self.register_fun_decl_id(id)
    }

    /// Returns an [Option] because we may ignore some builtin or auto traits
    /// like [core::marker::Sized] or [core::marker::Sync].
    pub(crate) fn translate_trait_decl_id(&mut self, id: DefId) -> Option<ast::TraitDeclId::Id> {
        self.register_trait_decl_id(id)
    }

    /// Returns an [Option] because we may ignore some builtin or auto traits
    /// like [core::marker::Sized] or [core::marker::Sync].
    pub(crate) fn translate_trait_impl_id(&mut self, id: DefId) -> Option<ast::TraitImplId::Id> {
        self.register_trait_impl_id(id)
    }

    pub(crate) fn register_global_decl_id(&mut self, id: DefId) -> GlobalDeclId::Id {
        match self.global_id_map.get(&id) {
            Option::Some(id) => id,
            Option::None => {
                let rid = OrdRustId::Global(id);
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
        let hax_state = crate::names_utils::make_hax_state_with_id(t_ctx.tcx, def_id);
        let mut trait_clauses_counter = TraitClauseId::Generator::new();
        let trait_instance_id_gen = Box::new(move || {
            let id = trait_clauses_counter.fresh_id();
            TraitInstanceId::Clause(id)
        });
        BodyTransCtx {
            def_id,
            t_ctx,
            hax_state,
            region_vars: RegionVarId::Vector::new(),
            region_vars_map: RegionVarId::MapGenerator::new(),
            type_vars: TypeVarId::Vector::new(),
            type_vars_map: TypeVarId::MapGenerator::new(),
            vars: VarId::Vector::new(),
            vars_map: VarId::MapGenerator::new(),
            const_generic_vars: ConstGenericVarId::Vector::new(),
            const_generic_vars_map: ConstGenericVarId::MapGenerator::new(),
            trait_instance_id_gen,
            trait_clauses: OrdMap::new(),
            registering_trait_clauses: false,
            regions_outlive: Vec::new(),
            types_outlive: Vec::new(),
            trait_type_constraints: Vec::new(),
            blocks: im::OrdMap::new(),
            blocks_map: ast::BlockId::MapGenerator::new(),
            bound_vars: im::Vector::new(),
        }
    }

    pub(crate) fn translate_meta_from_rid(&mut self, def_id: DefId) -> Meta {
        self.t_ctx.translate_meta_from_rid(def_id)
    }

    pub(crate) fn translate_meta_from_rspan(&mut self, rspan: hax::Span) -> Meta {
        self.t_ctx.translate_meta_from_rspan(rspan)
    }

    pub(crate) fn get_local(&self, local: &hax::Local) -> Option<VarId::Id> {
        use rustc_index::Idx;
        self.vars_map.get(&local.index())
    }

    pub(crate) fn get_block_id_from_rid(&self, rid: hax::BasicBlock) -> Option<ast::BlockId::Id> {
        self.blocks_map.get(&rid)
    }

    pub(crate) fn get_var_from_id(&self, var_id: VarId::Id) -> Option<&ast::Var> {
        self.vars.get(var_id)
    }

    pub(crate) fn register_type_decl_id(&mut self, id: DefId) -> TypeDeclId::Id {
        self.t_ctx.register_type_decl_id(id)
    }

    pub(crate) fn translate_type_decl_id(&mut self, id: DefId) -> TypeDeclId::Id {
        self.t_ctx.translate_type_decl_id(id)
    }

    pub(crate) fn register_fun_decl_id(&mut self, id: DefId) -> ast::FunDeclId::Id {
        self.t_ctx.register_fun_decl_id(id)
    }

    pub(crate) fn translate_fun_decl_id(&mut self, id: DefId) -> ast::FunDeclId::Id {
        self.t_ctx.translate_fun_decl_id(id)
    }

    pub(crate) fn register_global_decl_id(&mut self, id: DefId) -> GlobalDeclId::Id {
        self.t_ctx.register_global_decl_id(id)
    }

    pub(crate) fn translate_global_decl_id(&mut self, id: DefId) -> ast::GlobalDeclId::Id {
        self.t_ctx.translate_global_decl_id(id)
    }

    /// Returns an [Option] because we may ignore some builtin or auto traits
    /// like [core::marker::Sized] or [core::marker::Sync].
    pub(crate) fn translate_trait_decl_id(&mut self, id: DefId) -> Option<ast::TraitDeclId::Id> {
        self.t_ctx.translate_trait_decl_id(id)
    }

    /// Returns an [Option] because we may ignore some builtin or auto traits
    /// like [core::marker::Sized] or [core::marker::Sync].
    pub(crate) fn translate_trait_impl_id(&mut self, id: DefId) -> Option<ast::TraitImplId::Id> {
        self.t_ctx.translate_trait_impl_id(id)
    }

    pub(crate) fn get_region_from_rust(&self, r: hax::Region) -> Option<RegionVarId::Id> {
        self.region_vars_map.get(&r)
    }

    pub(crate) fn push_region(&mut self, r: hax::Region, name: Option<String>) -> RegionVarId::Id {
        use crate::id_vector::ToUsize;
        let rid = self.region_vars_map.insert(r);
        assert!(rid.to_usize() == self.region_vars.len());
        let var = RegionVar { index: rid, name };
        self.region_vars.insert(rid, var);
        rid
    }

    /// Push a group of bound regions
    pub(crate) fn push_bound_regions_group(&mut self, names: Vec<Option<String>>) {
        use crate::id_vector::ToUsize;

        // Register the variables
        let var_ids: im::Vector<RegionVarId::Id> = names
            .into_iter()
            .map(|name| {
                // Note that we don't insert a binding in the region_vars_map
                let rid = self.region_vars_map.fresh_id();
                assert!(rid.to_usize() == self.region_vars.len());
                let var = RegionVar { index: rid, name };
                self.region_vars.insert(rid, var);
                rid
            })
            .collect();

        // Push the group
        self.bound_vars.push_front(var_ids);
    }

    pub(crate) fn push_type_var(&mut self, rindex: u32, name: String) -> TypeVarId::Id {
        use crate::id_vector::ToUsize;
        let var_id = self.type_vars_map.insert(rindex);
        assert!(var_id.to_usize() == self.type_vars.len());
        let var = TypeVar {
            index: var_id,
            name,
        };
        self.type_vars.insert(var_id, var);
        var_id
    }

    pub(crate) fn push_var(&mut self, rid: usize, ty: ETy, name: Option<String>) {
        use crate::id_vector::ToUsize;
        let var_id = self.vars_map.insert(rid);
        assert!(var_id.to_usize() == self.vars.len());
        let var = ast::Var {
            index: var_id,
            name,
            ty,
        };
        self.vars.insert(var_id, var);
    }

    pub(crate) fn push_const_generic_var(&mut self, rid: u32, ty: LiteralTy, name: String) {
        use crate::id_vector::ToUsize;
        let var_id = self.const_generic_vars_map.insert(rid);
        assert!(var_id.to_usize() == self.vars.len());
        let var = ConstGenericVar {
            index: var_id,
            name,
            ty,
        };
        self.const_generic_vars.insert(var_id, var);
    }

    pub(crate) fn fresh_block_id(&mut self, rid: hax::BasicBlock) -> ast::BlockId::Id {
        self.blocks_map.insert(rid)
    }

    pub(crate) fn push_block(&mut self, id: ast::BlockId::Id, block: ast::BlockData) {
        self.blocks.insert(id, block);
    }

    pub(crate) fn get_type_defs(&self) -> &TypeDecls {
        &self.t_ctx.type_defs
    }

    pub(crate) fn fresh_trait_instance_id(&mut self) -> TraitInstanceId {
        (*self.trait_instance_id_gen)()
    }

    pub(crate) fn get_generics(&self) -> GenericParams {
        GenericParams {
            regions: self.region_vars.clone(),
            types: self.type_vars.clone(),
            const_generics: self.const_generic_vars.clone(),
            trait_clauses: self.get_local_trait_clauses(),
        }
    }

    /// Retrieve the *local* trait clauses available in the current environment
    /// (we filter the parent of those clauses, etc.).
    pub(crate) fn get_local_trait_clauses(&self) -> TraitClauseId::Vector<TraitClause> {
        let clauses: TraitClauseId::Vector<TraitClause> = self
            .trait_clauses
            .iter()
            .filter_map(|(_, x)| x.to_local_trait_clause())
            .collect();
        // Sanity check
        assert!(clauses.iter_indexed_values().all(|(i, c)| c.clause_id == i));
        clauses
    }

    pub(crate) fn get_parent_trait_clauses(&self) -> TraitClauseId::Vector<TraitClause> {
        let clauses: TraitClauseId::Vector<TraitClause> = self
            .trait_clauses
            .iter()
            .filter_map(|(_, x)| {
                x.to_trait_clause_with_id(&|id| match id {
                    TraitInstanceId::ParentClause(box TraitInstanceId::SelfId, _, id) => Some(*id),
                    _ => None,
                })
            })
            .collect();
        // Sanity check
        assert!(clauses.iter_indexed_values().all(|(i, c)| c.clause_id == i));
        clauses
    }

    pub(crate) fn get_predicates(&self) -> Predicates {
        Predicates {
            regions_outlive: self.regions_outlive.clone(),
            types_outlive: self.types_outlive.clone(),
            trait_type_constraints: self.trait_type_constraints.clone(),
        }
    }

    /// We use this when exploring the clauses of a predicate, to introduce
    /// its parent clauses, etc. in the context. We temporarily replace the
    /// trait instance id generator so that the continuation registers the
    ///
    pub(crate) fn with_local_trait_clauses<T>(
        &mut self,
        new_trait_instance_id_gen: Box<dyn FnMut() -> TraitInstanceId>,
        f: &mut dyn FnMut(&mut Self) -> T,
    ) -> T {
        use std::mem::replace;

        // Save the trait instance id generator
        let old_trait_instance_id_gen =
            replace(&mut self.trait_instance_id_gen, new_trait_instance_id_gen);

        // Apply the continuation
        let out = f(self);

        // Restore
        self.trait_instance_id_gen = old_trait_instance_id_gen;

        // Return
        out
    }

    /// Set [registering_trait_clauses] to [true], call the continuation, and
    /// reset it to [false]
    pub(crate) fn while_registering_trait_clauses<T>(
        &mut self,
        f: &mut dyn FnMut(&mut Self) -> T,
    ) -> T {
        assert!(!self.registering_trait_clauses);
        self.registering_trait_clauses = true;
        let out = f(self);
        self.registering_trait_clauses = false;
        out
    }
}

impl<'tcx, 'ctx> Formatter<TypeDeclId::Id> for TransCtx<'tcx, 'ctx> {
    fn format_object(&self, id: TypeDeclId::Id) -> String {
        self.type_defs.format_object(id)
    }
}

impl<'tcx, 'ctx> Formatter<GlobalDeclId::Id> for TransCtx<'tcx, 'ctx> {
    fn format_object(&self, id: GlobalDeclId::Id) -> String {
        self.global_defs.format_object(id)
    }
}

impl<'tcx, 'ctx> Formatter<RegionVarId::Id> for TransCtx<'tcx, 'ctx> {
    fn format_object(&self, id: RegionVarId::Id) -> String {
        id.to_pretty_string()
    }
}

impl<'tcx, 'ctx> Formatter<TypeVarId::Id> for TransCtx<'tcx, 'ctx> {
    fn format_object(&self, id: TypeVarId::Id) -> String {
        id.to_pretty_string()
    }
}

impl<'tcx, 'ctx> Formatter<&Region<RegionVarId::Id>> for TransCtx<'tcx, 'ctx> {
    fn format_object(&self, r: &Region<RegionVarId::Id>) -> String {
        r.fmt_with_ctx(self)
    }
}

impl<'tcx, 'ctx> Formatter<ConstGenericVarId::Id> for TransCtx<'tcx, 'ctx> {
    fn format_object(&self, id: ConstGenericVarId::Id) -> String {
        id.to_pretty_string()
    }
}

impl<'tcx, 'ctx> Formatter<ast::FunDeclId::Id> for TransCtx<'tcx, 'ctx> {
    fn format_object(&self, id: ast::FunDeclId::Id) -> String {
        match self.fun_defs.get(id) {
            None => id.to_pretty_string(),
            Some(d) => d.name.to_string(),
        }
    }
}

impl<'tcx, 'ctx> Formatter<ast::TraitClauseId::Id> for TransCtx<'tcx, 'ctx> {
    fn format_object(&self, id: ast::TraitClauseId::Id) -> String {
        id.to_pretty_string()
    }
}

impl<'tcx, 'ctx> Formatter<ast::TraitDeclId::Id> for TransCtx<'tcx, 'ctx> {
    fn format_object(&self, id: ast::TraitDeclId::Id) -> String {
        match self.trait_decls.get(id) {
            None => id.to_pretty_string(),
            Some(d) => d.name.to_string(),
        }
    }
}

impl<'tcx, 'ctx> Formatter<ast::TraitImplId::Id> for TransCtx<'tcx, 'ctx> {
    fn format_object(&self, id: ast::TraitImplId::Id) -> String {
        match self.trait_impls.get(id) {
            None => id.to_pretty_string(),
            Some(d) => d.name.to_string(),
        }
    }
}

/// For enum values: `List::Cons`
impl<'tcx, 'ctx> Formatter<(TypeDeclId::Id, VariantId::Id)> for TransCtx<'tcx, 'ctx> {
    fn format_object(&self, id: (TypeDeclId::Id, VariantId::Id)) -> String {
        let (def_id, variant_id) = id;
        // The definition may not be available yet, especially if we print-debug
        // while translating the crate
        match self.type_defs.get(def_id) {
            Option::None => format!(
                "{}::{}",
                def_id.to_pretty_string(),
                variant_id.to_pretty_string()
            ),
            Option::Some(def) => {
                let variants = def.kind.as_enum();
                let mut name = def.name.to_string();
                let variant_name = &variants.get(variant_id).unwrap().name;
                name.push_str("::");
                name.push_str(variant_name);
                name
            }
        }
    }
}

/// For struct/enum values: retrieve a field name
impl<'tcx, 'ctx> Formatter<(TypeDeclId::Id, Option<VariantId::Id>, FieldId::Id)>
    for TransCtx<'tcx, 'ctx>
{
    fn format_object(&self, id: (TypeDeclId::Id, Option<VariantId::Id>, FieldId::Id)) -> String {
        let (def_id, opt_variant_id, field_id) = id;
        // The definition may not be available yet, especially if we print-debug
        // while translating the crate
        match self.type_defs.get(def_id) {
            Option::None => match opt_variant_id {
                Option::None => format!(
                    "{}::{}",
                    def_id.to_pretty_string(),
                    field_id.to_pretty_string()
                ),
                Option::Some(variant_id) => format!(
                    "{}::{}::{}",
                    def_id.to_pretty_string(),
                    variant_id.to_pretty_string(),
                    field_id.to_pretty_string()
                ),
            },
            Option::Some(gen_def) => match (&gen_def.kind, opt_variant_id) {
                (TypeDeclKind::Enum(variants), Some(variant_id)) => {
                    let field = variants
                        .get(variant_id)
                        .unwrap()
                        .fields
                        .get(field_id)
                        .unwrap();
                    match &field.name {
                        Option::Some(name) => name.clone(),
                        Option::None => field_id.to_string(),
                    }
                }
                (TypeDeclKind::Struct(fields), None) => {
                    let field = fields.get(field_id).unwrap();
                    match &field.name {
                        Option::Some(name) => name.clone(),
                        Option::None => field_id.to_string(),
                    }
                }
                _ => unreachable!(),
            },
        }
    }
}

impl<'tcx, 'ctx> Formatter<VarId::Id> for TransCtx<'tcx, 'ctx> {
    fn format_object(&self, v: VarId::Id) -> String {
        v.to_pretty_string()
    }
}

impl<'tcx, 'ctx> Formatter<&ErasedRegion> for TransCtx<'tcx, 'ctx> {
    fn format_object(&self, _: &ErasedRegion) -> String {
        "'_".to_owned()
    }
}

impl<'tcx, 'ctx, 'ctx1> Formatter<TypeVarId::Id> for BodyTransCtx<'tcx, 'ctx, 'ctx1> {
    fn format_object(&self, id: TypeVarId::Id) -> String {
        let v = self.type_vars.get(id).unwrap();
        v.to_string()
    }
}

impl<'tcx, 'ctx, 'ctx1> Formatter<ConstGenericVarId::Id> for BodyTransCtx<'tcx, 'ctx, 'ctx1> {
    fn format_object(&self, id: ConstGenericVarId::Id) -> String {
        let v = self.const_generic_vars.get(id).unwrap();
        v.to_string()
    }
}

impl<'tcx, 'ctx, 'ctx1> Formatter<VarId::Id> for BodyTransCtx<'tcx, 'ctx, 'ctx1> {
    fn format_object(&self, id: VarId::Id) -> String {
        let v = self.vars.get(id).unwrap();
        v.to_string()
    }
}

impl<'tcx, 'ctx, 'ctx1> Formatter<RegionVarId::Id> for BodyTransCtx<'tcx, 'ctx, 'ctx1> {
    fn format_object(&self, id: RegionVarId::Id) -> String {
        let v = self.region_vars.get(id).unwrap();
        v.to_string()
    }
}

impl<'tcx, 'ctx, 'ctx1> Formatter<&Region<RegionVarId::Id>> for BodyTransCtx<'tcx, 'ctx, 'ctx1> {
    fn format_object(&self, r: &Region<RegionVarId::Id>) -> String {
        r.fmt_with_ctx(self)
    }
}

impl<'tcx, 'ctx, 'ctx1> Formatter<&ErasedRegion> for BodyTransCtx<'tcx, 'ctx, 'ctx1> {
    fn format_object(&self, _: &ErasedRegion) -> String {
        "'_".to_owned()
    }
}

impl<'tcx, 'ctx, 'ctx1> Formatter<TypeDeclId::Id> for BodyTransCtx<'tcx, 'ctx, 'ctx1> {
    fn format_object(&self, id: TypeDeclId::Id) -> String {
        self.t_ctx.type_defs.format_object(id)
    }
}

impl<'tcx, 'ctx, 'ctx1> Formatter<GlobalDeclId::Id> for BodyTransCtx<'tcx, 'ctx, 'ctx1> {
    fn format_object(&self, id: GlobalDeclId::Id) -> String {
        self.t_ctx.global_defs.format_object(id)
    }
}

impl<'tcx, 'ctx, 'ctx1> Formatter<&Ty<Region<RegionVarId::Id>>>
    for BodyTransCtx<'tcx, 'ctx, 'ctx1>
{
    fn format_object(&self, ty: &Ty<Region<RegionVarId::Id>>) -> String {
        ty.fmt_with_ctx(self)
    }
}

impl<'tcx, 'ctx, 'ctx1> Formatter<&Ty<ErasedRegion>> for BodyTransCtx<'tcx, 'ctx, 'ctx1> {
    fn format_object(&self, ty: &Ty<ErasedRegion>) -> String {
        ty.fmt_with_ctx(self)
    }
}

impl<'tcx, 'ctx, 'ctx1> Formatter<ast::TraitClauseId::Id> for BodyTransCtx<'tcx, 'ctx, 'ctx1> {
    fn format_object(&self, id: ast::TraitClauseId::Id) -> String {
        id.to_pretty_string()
    }
}

impl<'tcx, 'ctx, 'ctx1> Formatter<ast::TraitDeclId::Id> for BodyTransCtx<'tcx, 'ctx, 'ctx1> {
    fn format_object(&self, id: ast::TraitDeclId::Id) -> String {
        self.t_ctx.format_object(id)
    }
}

impl<'tcx, 'ctx, 'ctx1> Formatter<ast::TraitImplId::Id> for BodyTransCtx<'tcx, 'ctx, 'ctx1> {
    fn format_object(&self, id: ast::TraitImplId::Id) -> String {
        self.t_ctx.format_object(id)
    }
}

impl<'tcx, 'ctx, 'ctx1> Formatter<ast::FunDeclId::Id> for BodyTransCtx<'tcx, 'ctx, 'ctx1> {
    fn format_object(&self, id: ast::FunDeclId::Id) -> String {
        self.t_ctx.format_object(id)
    }
}

impl<'tcx, 'ctx, 'ctx1> Formatter<TypeVarId::Id> for BodyFormatCtx<'tcx, 'ctx, 'ctx1> {
    fn format_object(&self, id: TypeVarId::Id) -> String {
        match self.generics.types.get(id) {
            None => id.to_pretty_string(),
            Some(v) => v.to_string(),
        }
    }
}

impl<'tcx, 'ctx, 'ctx1> Formatter<ConstGenericVarId::Id> for BodyFormatCtx<'tcx, 'ctx, 'ctx1> {
    fn format_object(&self, id: ConstGenericVarId::Id) -> String {
        match self.generics.const_generics.get(id) {
            None => id.to_pretty_string(),
            Some(v) => v.to_string(),
        }
    }
}

impl<'tcx, 'ctx, 'ctx1> Formatter<VarId::Id> for BodyFormatCtx<'tcx, 'ctx, 'ctx1> {
    fn format_object(&self, id: VarId::Id) -> String {
        match self.vars.get(id) {
            None => id.to_pretty_string(),
            Some(v) => v.to_string(),
        }
    }
}

impl<'tcx, 'ctx, 'ctx1> Formatter<RegionVarId::Id> for BodyFormatCtx<'tcx, 'ctx, 'ctx1> {
    fn format_object(&self, id: RegionVarId::Id) -> String {
        match self.generics.regions.get(id) {
            None => id.to_pretty_string(),
            Some(v) => v.to_string(),
        }
    }
}

impl<'tcx, 'ctx, 'ctx1> Formatter<&Region<RegionVarId::Id>> for BodyFormatCtx<'tcx, 'ctx, 'ctx1> {
    fn format_object(&self, r: &Region<RegionVarId::Id>) -> String {
        r.fmt_with_ctx(self)
    }
}

impl<'tcx, 'ctx, 'ctx1> Formatter<&ErasedRegion> for BodyFormatCtx<'tcx, 'ctx, 'ctx1> {
    fn format_object(&self, _: &ErasedRegion) -> String {
        "'_".to_owned()
    }
}

impl<'tcx, 'ctx, 'ctx1> Formatter<TypeDeclId::Id> for BodyFormatCtx<'tcx, 'ctx, 'ctx1> {
    fn format_object(&self, id: TypeDeclId::Id) -> String {
        self.t_ctx.type_defs.format_object(id)
    }
}

impl<'tcx, 'ctx, 'ctx1> Formatter<GlobalDeclId::Id> for BodyFormatCtx<'tcx, 'ctx, 'ctx1> {
    fn format_object(&self, id: GlobalDeclId::Id) -> String {
        self.t_ctx.global_defs.format_object(id)
    }
}

impl<'tcx, 'ctx, 'ctx1> Formatter<&Ty<Region<RegionVarId::Id>>>
    for BodyFormatCtx<'tcx, 'ctx, 'ctx1>
{
    fn format_object(&self, ty: &Ty<Region<RegionVarId::Id>>) -> String {
        ty.fmt_with_ctx(self)
    }
}

impl<'tcx, 'ctx, 'ctx1> Formatter<&Ty<ErasedRegion>> for BodyFormatCtx<'tcx, 'ctx, 'ctx1> {
    fn format_object(&self, ty: &Ty<ErasedRegion>) -> String {
        ty.fmt_with_ctx(self)
    }
}

impl<'tcx, 'ctx, 'ctx1> Formatter<ast::TraitClauseId::Id> for BodyFormatCtx<'tcx, 'ctx, 'ctx1> {
    fn format_object(&self, id: ast::TraitClauseId::Id) -> String {
        id.to_pretty_string()
    }
}

impl<'tcx, 'ctx, 'ctx1> Formatter<ast::TraitDeclId::Id> for BodyFormatCtx<'tcx, 'ctx, 'ctx1> {
    fn format_object(&self, id: ast::TraitDeclId::Id) -> String {
        self.t_ctx.format_object(id)
    }
}

impl<'tcx, 'ctx, 'ctx1> Formatter<ast::TraitImplId::Id> for BodyFormatCtx<'tcx, 'ctx, 'ctx1> {
    fn format_object(&self, id: ast::TraitImplId::Id) -> String {
        self.t_ctx.format_object(id)
    }
}

impl<'tcx, 'ctx, 'ctx1> Formatter<ast::FunDeclId::Id> for BodyFormatCtx<'tcx, 'ctx, 'ctx1> {
    fn format_object(&self, id: ast::FunDeclId::Id) -> String {
        self.t_ctx.format_object(id)
    }
}

impl<'tcx, 'ctx, 'ctx1> Formatter<&TypeDecl> for BodyFormatCtx<'tcx, 'ctx, 'ctx1> {
    fn format_object(&self, def: &TypeDecl) -> String {
        def.fmt_with_ctx(self)
    }
}

impl<'tcx, 'ctx, 'ctx1> Formatter<(TypeDeclId::Id, VariantId::Id)>
    for BodyTransCtx<'tcx, 'ctx, 'ctx1>
{
    fn format_object(&self, id: (TypeDeclId::Id, VariantId::Id)) -> String {
        self.t_ctx.format_object(id)
    }
}

impl<'tcx, 'ctx, 'ctx1> Formatter<(TypeDeclId::Id, Option<VariantId::Id>, FieldId::Id)>
    for BodyTransCtx<'tcx, 'ctx, 'ctx1>
{
    fn format_object(&self, id: (TypeDeclId::Id, Option<VariantId::Id>, FieldId::Id)) -> String {
        self.t_ctx.format_object(id)
    }
}

impl<'tcx, 'ctx, 'ctx1> Formatter<(TypeDeclId::Id, VariantId::Id)>
    for BodyFormatCtx<'tcx, 'ctx, 'ctx1>
{
    fn format_object(&self, id: (TypeDeclId::Id, VariantId::Id)) -> String {
        self.t_ctx.format_object(id)
    }
}

impl<'tcx, 'ctx, 'ctx1> Formatter<(TypeDeclId::Id, Option<VariantId::Id>, FieldId::Id)>
    for BodyFormatCtx<'tcx, 'ctx, 'ctx1>
{
    fn format_object(&self, id: (TypeDeclId::Id, Option<VariantId::Id>, FieldId::Id)) -> String {
        self.t_ctx.format_object(id)
    }
}

impl<'tcx, 'ctx> Formatter<&TypeDecl> for TransCtx<'tcx, 'ctx> {
    fn format_object(&self, def: &TypeDecl) -> String {
        // Create a body format context
        let formatter = BodyFormatCtx {
            t_ctx: self,
            generics: &def.generics,
            vars: &VarId::Vector::new(),
            trait_clauses: &TraitClauseId::Vector::new(),
        };
        def.fmt_with_ctx(&formatter)
    }
}

impl<'tcx, 'ctx, 'ctx1> Formatter<&llbc_ast::Statement> for BodyFormatCtx<'tcx, 'ctx, 'ctx1> {
    fn format_object(&self, x: &llbc_ast::Statement) -> String {
        x.fmt_with_ctx(TAB_INCR, self)
    }
}

impl<'tcx, 'ctx, 'ctx1> Formatter<&ullbc_ast::BlockId::Vector<ullbc_ast::BlockData>>
    for BodyFormatCtx<'tcx, 'ctx, 'ctx1>
{
    fn format_object(&self, x: &ullbc_ast::BlockId::Vector<ullbc_ast::BlockData>) -> String {
        ullbc_ast::fmt_body_blocks_with_ctx(x, TAB_INCR, self)
    }
}

impl<'tcx, 'ctx, 'ctx1> Formatter<&TypeDecl> for BodyTransCtx<'tcx, 'ctx, 'ctx1> {
    fn format_object(&self, def: &TypeDecl) -> String {
        self.t_ctx.format_object(def)
    }
}

impl<'tcx, 'ctx> Formatter<&ullbc_ast::ExprBody> for TransCtx<'tcx, 'ctx> {
    fn format_object(&self, body: &ullbc_ast::ExprBody) -> String {
        // Create a body format context
        let formatter = BodyFormatCtx {
            t_ctx: self,
            generics: &GenericParams::empty(),
            vars: &body.locals,
            trait_clauses: &TraitClauseId::Vector::new(),
        };
        body.fmt_with_ctx(TAB_INCR, &formatter)
    }
}

impl<'tcx, 'ctx, 'ctx1> Formatter<&ullbc_ast::ExprBody> for BodyTransCtx<'tcx, 'ctx, 'ctx1> {
    fn format_object(&self, body: &ullbc_ast::ExprBody) -> String {
        self.t_ctx.format_object(body)
    }
}

impl<'tcx, 'ctx> Formatter<&llbc_ast::ExprBody> for TransCtx<'tcx, 'ctx> {
    fn format_object(&self, body: &llbc_ast::ExprBody) -> String {
        // Create a body format context
        let formatter = BodyFormatCtx {
            t_ctx: self,
            generics: &GenericParams::empty(),
            vars: &body.locals,
            trait_clauses: &TraitClauseId::Vector::new(),
        };
        body.fmt_with_ctx(TAB_INCR, &formatter)
    }
}

impl<'tcx, 'ctx, 'ctx1> Formatter<&llbc_ast::ExprBody> for BodyTransCtx<'tcx, 'ctx, 'ctx1> {
    fn format_object(&self, body: &llbc_ast::ExprBody) -> String {
        self.t_ctx.format_object(body)
    }
}

impl<'tcx, 'ctx> Formatter<&ullbc_ast::GlobalDecl> for TransCtx<'tcx, 'ctx> {
    fn format_object(&self, def: &ullbc_ast::GlobalDecl) -> String {
        // Create a body format context
        let empty_vars = VarId::Vector::new();
        let vars = match &def.body {
            None => &empty_vars,
            Some(body) => &body.locals,
        };
        let formatter = BodyFormatCtx {
            t_ctx: self,
            generics: &GenericParams::empty(),
            vars,
            trait_clauses: &TraitClauseId::Vector::new(),
        };
        def.fmt_with_ctx(&formatter)
    }
}

impl<'tcx, 'ctx, 'ctx1> Formatter<&ullbc_ast::GlobalDecl> for BodyTransCtx<'tcx, 'ctx, 'ctx1> {
    fn format_object(&self, def: &ullbc_ast::GlobalDecl) -> String {
        self.t_ctx.format_object(def)
    }
}

impl<'tcx, 'ctx> Formatter<&llbc_ast::GlobalDecl> for TransCtx<'tcx, 'ctx> {
    fn format_object(&self, def: &llbc_ast::GlobalDecl) -> String {
        // Create a body format context
        let empty_vars = VarId::Vector::new();
        let vars = match &def.body {
            None => &empty_vars,
            Some(body) => &body.locals,
        };
        let formatter = BodyFormatCtx {
            t_ctx: self,
            generics: &GenericParams::empty(),
            vars,
            trait_clauses: &TraitClauseId::Vector::new(),
        };
        def.fmt_with_ctx(&formatter)
    }
}

impl<'tcx, 'ctx, 'ctx1> Formatter<&llbc_ast::GlobalDecl> for BodyTransCtx<'tcx, 'ctx, 'ctx1> {
    fn format_object(&self, def: &llbc_ast::GlobalDecl) -> String {
        self.t_ctx.format_object(def)
    }
}

impl<'tcx, 'ctx> Formatter<&FunSig> for TransCtx<'tcx, 'ctx> {
    fn format_object(&self, sig: &FunSig) -> String {
        // Create a body format context
        let formatter = BodyFormatCtx {
            t_ctx: self,
            generics: &sig.generics,
            vars: &VarId::Vector::new(),
            trait_clauses: &TraitClauseId::Vector::new(),
        };
        sig.fmt_with_ctx(&formatter)
    }
}

impl<'tcx, 'ctx, 'ctx1> Formatter<&FunSig> for BodyTransCtx<'tcx, 'ctx, 'ctx1> {
    fn format_object(&self, sig: &FunSig) -> String {
        self.t_ctx.format_object(sig)
    }
}

impl<'tcx, 'ctx> Formatter<&ETy> for TransCtx<'tcx, 'ctx> {
    fn format_object(&self, x: &ETy) -> String {
        x.fmt_with_ctx(self)
    }
}

impl<'tcx, 'ctx> Formatter<&RTy> for TransCtx<'tcx, 'ctx> {
    fn format_object(&self, x: &RTy) -> String {
        x.fmt_with_ctx(self)
    }
}

impl<'tcx, 'ctx> Formatter<&ullbc_ast::FunDecl> for TransCtx<'tcx, 'ctx> {
    fn format_object(&self, def: &ullbc_ast::FunDecl) -> String {
        // Create a body format context
        let empty_vars = VarId::Vector::new();
        let vars = match &def.body {
            None => &empty_vars,
            Some(body) => &body.locals,
        };
        let sig = &def.signature;
        let formatter = BodyFormatCtx {
            t_ctx: self,
            generics: &sig.generics,
            vars,
            trait_clauses: &TraitClauseId::Vector::new(),
        };
        def.fmt_with_ctx(&formatter)
    }
}

impl<'tcx, 'ctx, 'ctx1> Formatter<&ullbc_ast::FunDecl> for BodyTransCtx<'tcx, 'ctx, 'ctx1> {
    fn format_object(&self, def: &ullbc_ast::FunDecl) -> String {
        self.t_ctx.format_object(def)
    }
}

impl<'tcx, 'ctx> Formatter<&llbc_ast::FunDecl> for TransCtx<'tcx, 'ctx> {
    fn format_object(&self, def: &llbc_ast::FunDecl) -> String {
        // Create a body format context
        let empty_vars = VarId::Vector::new();
        let vars = match &def.body {
            None => &empty_vars,
            Some(body) => &body.locals,
        };
        let sig = &def.signature;
        let formatter = BodyFormatCtx {
            t_ctx: self,
            generics: &sig.generics,
            vars,
            trait_clauses: &TraitClauseId::Vector::new(),
        };
        def.fmt_with_ctx(&formatter)
    }
}

impl<'tcx, 'ctx, 'ctx1> Formatter<&llbc_ast::FunDecl> for BodyTransCtx<'tcx, 'ctx, 'ctx1> {
    fn format_object(&self, def: &llbc_ast::FunDecl) -> String {
        self.t_ctx.format_object(def)
    }
}

impl<'tcx, 'ctx, 'ctx1> Formatter<&gast::TraitDecl> for BodyFormatCtx<'tcx, 'ctx, 'ctx1> {
    fn format_object(&self, def: &gast::TraitDecl) -> String {
        def.fmt_with_ctx(self)
    }
}

impl<'tcx, 'ctx> Formatter<&gast::TraitDecl> for TransCtx<'tcx, 'ctx> {
    fn format_object(&self, def: &gast::TraitDecl) -> String {
        let formatter = BodyFormatCtx {
            t_ctx: self,
            generics: &def.generics,
            vars: &VarId::Vector::new(),
            trait_clauses: &TraitClauseId::Vector::new(),
        };
        def.fmt_with_ctx(&formatter)
    }
}

impl<'tcx, 'ctx, 'ctx1> Formatter<&gast::TraitDecl> for BodyTransCtx<'tcx, 'ctx, 'ctx1> {
    fn format_object(&self, def: &gast::TraitDecl) -> String {
        self.t_ctx.format_object(def)
    }
}

impl<'tcx, 'ctx, 'ctx1> Formatter<&gast::TraitImpl> for BodyFormatCtx<'tcx, 'ctx, 'ctx1> {
    fn format_object(&self, def: &gast::TraitImpl) -> String {
        def.fmt_with_ctx(self)
    }
}

impl<'tcx, 'ctx> Formatter<&gast::TraitImpl> for TransCtx<'tcx, 'ctx> {
    fn format_object(&self, def: &gast::TraitImpl) -> String {
        let formatter = BodyFormatCtx {
            t_ctx: self,
            generics: &def.generics,
            vars: &VarId::Vector::new(),
            trait_clauses: &TraitClauseId::Vector::new(),
        };
        def.fmt_with_ctx(&formatter)
    }
}

impl<'tcx, 'ctx, 'ctx1> Formatter<&gast::TraitImpl> for BodyTransCtx<'tcx, 'ctx, 'ctx1> {
    fn format_object(&self, def: &gast::TraitImpl) -> String {
        self.t_ctx.format_object(def)
    }
}

impl<'tcx, 'ctx> fmt::Display for TransCtx<'tcx, 'ctx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // We do simple: types, globals, traits, functions
        for (_, d) in &self.type_defs {
            writeln!(f, "{}\n", self.format_object(d))?
        }

        for (_, d) in &self.global_defs {
            writeln!(f, "{}\n", self.format_object(d))?
        }

        for (_, d) in &self.trait_decls {
            writeln!(f, "{}\n", self.format_object(d))?
        }

        for (_, d) in &self.trait_impls {
            writeln!(f, "{}\n", self.format_object(d))?
        }

        for (_, d) in &self.fun_defs {
            writeln!(f, "{}\n", self.format_object(d))?
        }

        fmt::Result::Ok(())
    }
}

impl<'tcx, 'ctx> TransCtx<'tcx, 'ctx> {
    fn fmt_with_llbc_defs(
        &self,
        f: &mut fmt::Formatter,
        llbc_globals: &llbc_ast::GlobalDecls,
        llbc_funs: &llbc_ast::FunDecls,
    ) -> fmt::Result {
        // We do simple: types, globals, traits, functions
        for (_, d) in &self.type_defs {
            writeln!(f, "{}\n", self.format_object(d))?
        }

        for (_, d) in llbc_globals {
            writeln!(f, "{}\n", self.format_object(d))?
        }

        for (_, d) in &self.trait_decls {
            writeln!(f, "{}\n", self.format_object(d))?
        }

        for (_, d) in &self.trait_impls {
            writeln!(f, "{}\n", self.format_object(d))?
        }

        for (_, d) in llbc_funs {
            writeln!(f, "{}\n", self.format_object(d))?
        }

        fmt::Result::Ok(())
    }
}

pub(crate) struct LlbcTransCtx<'a, 'tcx, 'ctx> {
    pub ctx: &'a TransCtx<'tcx, 'ctx>,
    pub llbc_globals: &'a llbc_ast::GlobalDecls,
    pub llbc_funs: &'a llbc_ast::FunDecls,
}

impl<'a, 'tcx, 'ctx> fmt::Display for LlbcTransCtx<'a, 'tcx, 'ctx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.ctx
            .fmt_with_llbc_defs(f, self.llbc_globals, self.llbc_funs)
    }
}
