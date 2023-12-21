//! The translation contexts.
use crate::common::*;
use crate::formatter::{DeclFormatter, FmtCtx, Formatter, IntoFormatter};
use crate::gast::*;
use crate::get_mir::MirLevel;
use crate::llbc_ast;
use crate::meta;
use crate::meta::{FileId, FileName, LocalFileId, Meta, VirtualFileId};
use crate::names::Name;
use crate::reorder_decls::{AnyTransId, DeclarationGroup, DeclarationsGroups, GDeclarationGroup};
use crate::translate_predicates::NonLocalTraitClause;
use crate::types::*;
use crate::ullbc_ast as ast;
use crate::values::*;
use hax_frontend_exporter as hax;
use hax_frontend_exporter::SInto;
use im::OrdMap;
use linked_hash_set::LinkedHashSet;
use macros::VariantIndexArity;
use rustc_error_messages::MultiSpan;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use rustc_session::Session;
use std::cmp::{Ord, Ordering, PartialOrd};
use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};
use std::fmt;

/// Macro to either panic or return on error, depending on the CLI options
macro_rules! error_or_panic {
    ($ctx:expr, $span: expr, $msg: expr) => {{
        $ctx.span_err($span, &$msg);
        if $ctx.continue_on_failure() {
            let e = crate::common::Error {
                span: $span,
                msg: $msg.to_string(),
            };
            return (Err(e));
        } else {
            panic!("{}", $msg);
        }
    }};
}
pub(crate) use error_or_panic;

/// Custom assert to either panic or return an error
macro_rules! error_assert {
    ($ctx:expr, $span: expr, $b: expr) => {
        if !$b {
            let msg = format!("assertion failure: {:?}", stringify!($b));
            $ctx.span_err($span, &msg);
            if $ctx.continue_on_failure() {
                let e = crate::common::Error { span: $span, msg };
                return (Err(e));
            } else {
                panic!("{}", msg);
            }
        }
    };
    ($ctx:expr, $span: expr, $b: expr, $msg: expr) => {
        if !$b {
            $ctx.span_err($span, &$msg);
            if $ctx.continue_on_failure() {
                let e = crate::common::Error {
                    span: $span,
                    msg: $msg.to_string(),
                };
                return (Err(e));
            } else {
                panic!("{}", $msg);
            }
        }
    };
}
pub(crate) use error_assert;

/// Custom assert to either panic or return an error
macro_rules! error_assert_then {
    ($ctx:expr, $span: expr, $b: expr, $then: expr) => {
        if !$b {
            let msg = format!("assertion failure: {:?}", stringify!($b));
            $ctx.span_err($span, &msg);
            if $ctx.continue_on_failure() {
                {
                    $then
                }
            } else {
                panic!("{}", msg);
            }
        }
    };
    ($ctx:expr, $span: expr, $b: expr, $then: expr, $msg:expr) => {
        if !$b {
            $ctx.span_err($span, &$msg);
            if $ctx.continue_on_failure() {
                {
                    $then
                }
            } else {
                panic!("{}", $msg);
            }
        }
    };
}
pub(crate) use error_assert_then;

macro_rules! register_error_or_panic {
    ($ctx:expr, $span: expr, $msg: expr) => {{
        $ctx.span_err($span, &$msg);
        if $ctx.continue_on_failure() {
            // Nothing to do
            ();
        } else {
            panic!("{}", $msg);
        }
    }};
}
pub(crate) use register_error_or_panic;

/// We use this to save the origin of an id. This is useful for the external
/// dependencies, especially if some external dependencies don't extract:
/// we use this information to tell the user what is the code which
/// (transitively) lead to the extraction of those problematic dependencies.
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct DepSource {
    pub src_id: DefId,
    pub span: rustc_span::Span,
}

impl DepSource {
    pub(crate) fn make(src_id: DefId, span: rustc_span::Span) -> Option<Self> {
        Some(DepSource { src_id, span })
    }
}

pub struct CrateInfo {
    pub crate_name: String,
    pub opaque_mods: HashSet<String>,
}

impl CrateInfo {
    pub(crate) fn is_opaque_decl(&self, name: &Name) -> bool {
        name.is_in_modules(&self.crate_name, &self.opaque_mods)
    }

    #[allow(dead_code)]
    pub(crate) fn is_transparent_decl(&self, name: &Name) -> bool {
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
    pub session: &'ctx Session,
    /// The Rust compiler type context
    pub tcx: TyCtxt<'tcx>,
    /// The Hax context
    pub hax_state: hax::State<hax::Base<'tcx>, (), (), ()>,
    /// The level at which to extract the MIR
    pub mir_level: MirLevel,
    ///
    pub crate_info: CrateInfo,
    /// Do not abort on the first error and attempt to extract as much as possible.
    pub continue_on_failure: bool,
    /// Print the errors as warnings, and do not
    pub errors_as_warnings: bool,
    /// The number of errors encountered so far.
    pub error_count: usize,
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
    /// The id of the definition we are exploring
    pub def_id: Option<DefId>,
    /// File names to ids and vice-versa
    pub file_to_id: HashMap<FileName, FileId::Id>,
    pub id_to_file: HashMap<FileId::Id, FileName>,
    pub real_file_counter: LocalFileId::Generator,
    pub virtual_file_counter: VirtualFileId::Generator,
    /// The map from Rust type ids to translated type ids
    pub type_id_map: TypeDeclId::MapGenerator<DefId>,
    /// The translated type definitions
    pub type_decls: TypeDecls,
    /// Dependency graph with sources. We use this for error reporting.
    /// See [DepSource].
    pub dep_sources: HashMap<DefId, HashSet<DepSource>>,
    /// The ids of the declarations for which extraction we encountered errors.
    pub decls_with_errors: HashSet<DefId>,
    /// The ids of the declarations we completely failed to extract
    /// and had to ignore.
    pub ignored_failed_decls: HashSet<DefId>,
    /// The map from Rust function ids to translated function ids
    pub fun_id_map: ast::FunDeclId::MapGenerator<DefId>,
    /// The translated function definitions
    pub fun_decls: ast::FunDecls,
    /// The map from Rust global ids to translated global ids
    pub global_id_map: ast::GlobalDeclId::MapGenerator<DefId>,
    /// The translated global definitions
    pub global_decls: ast::GlobalDecls,
    /// The map from Rust trait decl ids to translated trait decl ids
    pub trait_decl_id_map: ast::TraitDeclId::MapGenerator<DefId>,
    /// The translated trait declarations
    pub trait_decls: ast::TraitDecls,
    /// The map from Rust trait impls ids to translated trait impls ids
    pub trait_impl_id_map: ast::TraitImplId::MapGenerator<DefId>,
    pub trait_impl_id_to_def_id: HashMap<ast::TraitImplId::Id, DefId>,
    /// The translated trait declarations
    pub trait_impls: ast::TraitImpls,
    /// The re-ordered groups of declarations, initialized as empty.
    pub ordered_decls: Option<DeclarationsGroups>,
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
    /// The definition we are currently extracting.
    /// TODO: this duplicates the field of [TransCtx]
    pub def_id: DefId,
    /// The translation context containing the top-level definitions/ids.
    pub t_ctx: &'ctx mut TransCtx<'tcx, 'ctx1>,
    /// A hax state with an owner id
    pub hax_state: hax::State<hax::Base<'tcx>, (), (), rustc_hir::def_id::DefId>,
    /// The regions.
    /// We use DeBruijn indices, so we have a stack of regions.
    /// See the comments for [Region::BVar].
    pub region_vars: im::Vector<RegionId::Vector<RegionVar>>,
    /// The map from rust (free) regions to translated region indices.
    /// This contains the early bound regions.
    ///
    /// Important:
    /// ==========
    /// Rust makes the distinction between the early bound regions, which
    /// are free, and the late-bound regions, which are bound (and use
    /// DeBruijn indices).
    /// We do not make this distinction, and use bound regions everywhere.
    /// This means that we consider the free regions as belonging to the first
    /// group of bound regions.
    ///
    /// The [bound_region_vars] field below takes care of the regions which
    /// are bound in the Rustc representation.
    pub free_region_vars: std::collections::BTreeMap<hax::Region, RegionId::Id>,
    /// The generator for bound region indices
    pub bound_region_var_id_generator: RegionId::Generator,
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
    /// We use DeBruijn indices. See the comments for [Region::Var].
    pub bound_region_vars: im::Vector<im::Vector<RegionId::Id>>,
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
    pub trait_type_constraints: Vec<TraitTypeConstraint>,
    /// The translated blocks. We can't use `ast::BlockId::Vector<ast::BlockData>`
    /// here because we might generate several fresh indices before actually
    /// adding the resulting blocks to the map.
    pub blocks: im::OrdMap<ast::BlockId::Id, ast::BlockData>,
    /// The map from rust blocks to translated blocks.
    /// Note that when translating terminators like DropAndReplace, we might have
    /// to introduce new blocks which don't appear in the original MIR.
    pub blocks_map: ast::BlockId::MapGenerator<hax::BasicBlock>,
    /// We register the blocks to translate in a stack, so as to avoid
    /// writing the translation functions as recursive functions. We do
    /// so because we had stack overflows in the past.
    pub blocks_stack: VecDeque<hax::BasicBlock>,
}

impl<'tcx, 'ctx> TransCtx<'tcx, 'ctx> {
    pub fn continue_on_failure(&self) -> bool {
        self.continue_on_failure
    }

    pub fn span_err_no_register<S: Into<MultiSpan>>(&self, span: S, msg: &str) {
        let msg = msg.to_string();
        if self.errors_as_warnings {
            self.session.span_warn(span, msg);
        } else {
            self.session.span_err(span, msg);
        }
    }

    /// Span an error and register the error.
    pub fn span_err<S: Into<MultiSpan>>(&mut self, span: S, msg: &str) {
        self.span_err_no_register(span, msg);
        self.increment_error_count();
        if let Some(id) = self.def_id {
            let _ = self.decls_with_errors.insert(id);
        }
    }

    fn increment_error_count(&mut self) {
        self.error_count += 1;
    }

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
        meta::Span {
            file_id,
            beg,
            end,
            rust_span: rspan.rust_span,
        }
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

    pub(crate) fn id_is_opaque(&mut self, id: DefId) -> Result<bool, Error> {
        let name = self.def_id_to_name(id);
        Ok(self.crate_info.is_opaque_decl(&name))
    }

    pub(crate) fn id_is_transparent(&mut self, id: DefId) -> Result<bool, Error> {
        Ok(!(self.id_is_opaque(id)?))
    }

    pub(crate) fn push_id(&mut self, _rust_id: DefId, id: OrdRustId, trans_id: AnyTransId) {
        // Add the id to the stack of declarations to translate
        self.stack.insert(id);
        self.all_ids.insert(trans_id);
    }

    /// Register the fact that `id` is a dependency of `src` (if `src` is not `None`).
    pub(crate) fn register_dep_source(&mut self, src: &Option<DepSource>, id: DefId) {
        if let Some(src) = src {
            if src.src_id != id {
                match self.dep_sources.get_mut(&id) {
                    None => {
                        let _ = self.dep_sources.insert(id, HashSet::from([*src]));
                    }
                    Some(srcs) => {
                        let _ = srcs.insert(*src);
                    }
                }
            }
        }
    }

    pub(crate) fn register_type_decl_id(
        &mut self,
        src: &Option<DepSource>,
        id: DefId,
    ) -> TypeDeclId::Id {
        self.register_dep_source(src, id);
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

    pub(crate) fn translate_type_decl_id(
        &mut self,
        src: &Option<DepSource>,
        id: DefId,
    ) -> TypeDeclId::Id {
        self.register_type_decl_id(src, id)
    }

    // TODO: factor out all the "register_..." functions
    pub(crate) fn register_fun_decl_id(
        &mut self,
        src: &Option<DepSource>,
        id: DefId,
    ) -> ast::FunDeclId::Id {
        self.register_dep_source(src, id);
        match self.fun_id_map.get(&id) {
            Option::Some(tid) => tid,
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
    pub(crate) fn register_trait_decl_id(
        &mut self,
        src: &Option<DepSource>,
        id: DefId,
    ) -> Result<Option<ast::TraitDeclId::Id>, Error> {
        use crate::assumed;
        if assumed::IGNORE_BUILTIN_MARKER_TRAITS {
            let name = self.def_id_to_name(id)?;
            if assumed::is_marker_trait(&name) {
                return Ok(None);
            }
        }

        self.register_dep_source(src, id);
        match self.trait_decl_id_map.get(&id) {
            Option::Some(id) => Ok(Some(id)),
            Option::None => {
                let rid = OrdRustId::TraitDecl(id);
                let trans_id = self.trait_decl_id_map.insert(id);
                self.push_id(id, rid, AnyTransId::TraitDecl(trans_id));
                Ok(Some(trans_id))
            }
        }
    }

    /// Returns an [Option] because we may ignore some builtin or auto traits
    /// like [core::marker::Sized] or [core::marker::Sync].
    pub(crate) fn register_trait_impl_id(
        &mut self,
        src: &Option<DepSource>,
        rust_id: DefId,
    ) -> Result<Option<ast::TraitImplId::Id>, Error> {
        // Check if we need to filter
        {
            // Retrieve the id of the implemented trait decl
            let id = self.tcx.trait_id_of_impl(rust_id).unwrap();
            let _ = self.register_trait_decl_id(src, id)?;
        }

        self.register_dep_source(src, rust_id);
        let id = match self.trait_impl_id_map.get(&rust_id) {
            Option::Some(id) => Some(id),
            Option::None => {
                let rid = OrdRustId::TraitImpl(rust_id);
                let trans_id = self.trait_impl_id_map.insert(rust_id);
                self.trait_impl_id_to_def_id.insert(trans_id, rust_id);
                self.push_id(rust_id, rid, AnyTransId::TraitImpl(trans_id));
                Some(trans_id)
            }
        };
        Ok(id)
    }

    pub(crate) fn translate_fun_decl_id(
        &mut self,
        src: &Option<DepSource>,
        id: DefId,
    ) -> ast::FunDeclId::Id {
        self.register_fun_decl_id(src, id)
    }

    /// Returns an [Option] because we may ignore some builtin or auto traits
    /// like [core::marker::Sized] or [core::marker::Sync].
    pub(crate) fn translate_trait_decl_id(
        &mut self,
        src: &Option<DepSource>,
        id: DefId,
    ) -> Result<Option<ast::TraitDeclId::Id>, Error> {
        self.register_trait_decl_id(src, id)
    }

    /// Returns an [Option] because we may ignore some builtin or auto traits
    /// like [core::marker::Sized] or [core::marker::Sync].
    pub(crate) fn translate_trait_impl_id(
        &mut self,
        src: &Option<DepSource>,
        id: DefId,
    ) -> Result<Option<ast::TraitImplId::Id>, Error> {
        self.register_trait_impl_id(src, id)
    }

    pub(crate) fn register_global_decl_id(
        &mut self,
        src: &Option<DepSource>,
        id: DefId,
    ) -> GlobalDeclId::Id {
        self.register_dep_source(src, id);
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

    pub(crate) fn translate_global_decl_id(
        &mut self,
        src: &Option<DepSource>,
        id: DefId,
    ) -> ast::GlobalDeclId::Id {
        self.register_global_decl_id(src, id)
    }

    pub(crate) fn with_def_id<F, T>(&mut self, def_id: DefId, f: F) -> T
    where
        F: FnOnce(&mut Self) -> T,
    {
        let current_def_id = self.def_id;
        self.def_id = Some(def_id);
        let ret = f(self);
        self.def_id = current_def_id;
        ret
    }

    pub(crate) fn iter_bodies<F, B>(
        &mut self,
        funs: &mut FunDeclId::Map<GFunDecl<B>>,
        globals: &mut GlobalDeclId::Map<GGlobalDecl<B>>,
        f: F,
    ) where
        F: Fn(&mut Self, &Name, &mut GExprBody<B>),
    {
        for (id, name, b) in iter_function_bodies(funs).chain(iter_global_bodies(globals)) {
            self.with_def_id(id, |ctx| f(ctx, name, b))
        }
    }
}

impl<'tcx, 'ctx, 'ctx1> BodyTransCtx<'tcx, 'ctx, 'ctx1> {
    /// Create a new `ExecContext`.
    pub(crate) fn new(def_id: DefId, t_ctx: &'ctx mut TransCtx<'tcx, 'ctx1>) -> Self {
        let hax_state = t_ctx.make_hax_state_with_id(def_id);
        let mut trait_clauses_counter = TraitClauseId::Generator::new();
        let trait_instance_id_gen = Box::new(move || {
            let id = trait_clauses_counter.fresh_id();
            TraitInstanceId::Clause(id)
        });
        BodyTransCtx {
            def_id,
            t_ctx,
            hax_state,
            region_vars: im::vector![RegionId::Vector::new()],
            free_region_vars: std::collections::BTreeMap::new(),
            bound_region_var_id_generator: RegionId::Generator::new(),
            bound_region_vars: im::Vector::new(),
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
            blocks_stack: VecDeque::new(),
        }
    }

    pub fn continue_on_failure(&self) -> bool {
        self.t_ctx.continue_on_failure()
    }

    pub fn span_err(&mut self, span: rustc_span::Span, msg: &str) {
        self.t_ctx.span_err(span, msg)
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

    #[allow(dead_code)]
    pub(crate) fn get_block_id_from_rid(&self, rid: hax::BasicBlock) -> Option<ast::BlockId::Id> {
        self.blocks_map.get(&rid)
    }

    pub(crate) fn get_var_from_id(&self, var_id: VarId::Id) -> Option<&ast::Var> {
        self.vars.get(var_id)
    }

    pub(crate) fn translate_type_decl_id(
        &mut self,
        span: rustc_span::Span,
        id: DefId,
    ) -> TypeDeclId::Id {
        let src = self.make_dep_source(span);
        self.t_ctx.translate_type_decl_id(&src, id)
    }

    pub(crate) fn translate_fun_decl_id(
        &mut self,
        span: rustc_span::Span,
        id: DefId,
    ) -> ast::FunDeclId::Id {
        let src = self.make_dep_source(span);
        self.t_ctx.translate_fun_decl_id(&src, id)
    }

    pub(crate) fn translate_global_decl_id(
        &mut self,
        span: rustc_span::Span,
        id: DefId,
    ) -> ast::GlobalDeclId::Id {
        let src = self.make_dep_source(span);
        self.t_ctx.translate_global_decl_id(&src, id)
    }

    /// Returns an [Option] because we may ignore some builtin or auto traits
    /// like [core::marker::Sized] or [core::marker::Sync].
    pub(crate) fn translate_trait_decl_id(
        &mut self,
        span: rustc_span::Span,
        id: DefId,
    ) -> Result<Option<ast::TraitDeclId::Id>, Error> {
        let src = self.make_dep_source(span);
        self.t_ctx.translate_trait_decl_id(&src, id)
    }

    /// Returns an [Option] because we may ignore some builtin or auto traits
    /// like [core::marker::Sized] or [core::marker::Sync].
    pub(crate) fn translate_trait_impl_id(
        &mut self,
        span: rustc_span::Span,
        id: DefId,
    ) -> Result<Option<ast::TraitImplId::Id>, Error> {
        let src = self.make_dep_source(span);
        self.t_ctx.translate_trait_impl_id(&src, id)
    }

    /// Push a free region.
    ///
    /// Important: we must push *all* the free regions (which are early-bound
    /// regions) before pushing any (late-)bound region.
    pub(crate) fn push_free_region(
        &mut self,
        r: hax::Region,
        name: Option<String>,
    ) -> RegionId::Id {
        use crate::id_vector::ToUsize;
        // Check that there are no late-bound regions
        assert!(self.bound_region_vars.is_empty());
        let rid = self.bound_region_var_id_generator.fresh_id();
        self.free_region_vars.insert(r, rid);
        assert!(rid.to_usize() == self.region_vars[0].len());
        let var = RegionVar { index: rid, name };
        self.region_vars[0].insert(rid, var);
        rid
    }

    /// Set the first bound regions group
    pub(crate) fn set_first_bound_regions_group(&mut self, names: Vec<Option<String>>) {
        use crate::id_vector::ToUsize;
        assert!(self.bound_region_vars.is_empty());

        // Register the variables
        let var_ids: im::Vector<RegionId::Id> = names
            .into_iter()
            .map(|name| {
                let rid = self.bound_region_var_id_generator.fresh_id();
                assert!(rid.to_usize() == self.region_vars[0].len());
                let var = RegionVar { index: rid, name };
                self.region_vars[0].insert(rid, var);
                rid
            })
            .collect();

        // Push the group
        self.bound_region_vars.push_front(var_ids);
        // Reinitialize the counter
        self.bound_region_var_id_generator = RegionId::Generator::new();
    }

    /// Push a group of bound regions and call the continuation.
    /// We use this when diving into a `for<'a>`, or inside an arrow type (because
    /// it contains universally quantified regions).
    pub(crate) fn with_locally_bound_regions_group<F, T>(
        &mut self,
        names: Vec<Option<String>>,
        f: F,
    ) -> T
    where
        F: FnOnce(&mut Self) -> T,
    {
        use crate::id_vector::ToUsize;
        assert!(!self.region_vars.is_empty());
        self.region_vars.push_front(RegionId::Vector::new());
        // Reinitialize the counter
        let old_gen = std::mem::replace(
            &mut self.bound_region_var_id_generator,
            RegionId::Generator::new(),
        );

        // Register the variables
        let var_ids: im::Vector<RegionId::Id> = names
            .into_iter()
            .map(|name| {
                let rid = self.bound_region_var_id_generator.fresh_id();
                assert!(rid.to_usize() == self.region_vars[0].len());
                let var = RegionVar { index: rid, name };
                self.region_vars[0].insert(rid, var);
                rid
            })
            .collect();

        // Push the group
        self.bound_region_vars.push_front(var_ids);

        // Call the continuation
        let res = f(self);

        // Reset
        self.bound_region_var_id_generator = old_gen;
        self.bound_region_vars.pop_front();
        self.region_vars.pop_front();

        // Return
        res
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

    pub(crate) fn push_var(&mut self, rid: usize, ty: Ty, name: Option<String>) {
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
        assert!(var_id.to_usize() == self.const_generic_vars.len());
        let var = ConstGenericVar {
            index: var_id,
            name,
            ty,
        };
        self.const_generic_vars.insert(var_id, var);
    }

    pub(crate) fn fresh_block_id(&mut self, rid: hax::BasicBlock) -> ast::BlockId::Id {
        // Push to the stack of blocks awaiting translation
        self.blocks_stack.push_back(rid);
        // Insert in the map
        self.blocks_map.insert(rid)
    }

    pub(crate) fn push_block(&mut self, id: ast::BlockId::Id, block: ast::BlockData) {
        self.blocks.insert(id, block);
    }

    pub(crate) fn get_generics(&self) -> GenericParams {
        assert!(self.region_vars.len() == 1);
        GenericParams {
            regions: self.region_vars[0].clone(),
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
    pub(crate) fn with_local_trait_clauses<F, T>(
        &mut self,
        new_trait_instance_id_gen: Box<dyn FnMut() -> TraitInstanceId>,
        f: F,
    ) -> T
    where
        F: FnOnce(&mut Self) -> T,
    {
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
    pub(crate) fn while_registering_trait_clauses<F, T>(&mut self, f: F) -> T
    where
        F: FnOnce(&mut Self) -> T,
    {
        assert!(!self.registering_trait_clauses);
        self.registering_trait_clauses = true;
        let out = f(self);
        self.registering_trait_clauses = false;
        out
    }

    pub(crate) fn make_dep_source(&self, span: rustc_span::Span) -> Option<DepSource> {
        DepSource::make(self.def_id, span)
    }
}

impl<'tcx, 'ctx, 'a> IntoFormatter for &'a TransCtx<'tcx, 'ctx> {
    type C = FmtCtx<'a>;

    fn into_fmt(self) -> Self::C {
        FmtCtx {
            type_decls: Some(&self.type_decls),
            fun_decls: Some(&self.fun_decls),
            global_decls: Some(&self.global_decls),
            trait_decls: Some(&self.trait_decls),
            trait_impls: Some(&self.trait_impls),
            region_vars: im::Vector::new(),
            type_vars: None,
            const_generic_vars: None,
            locals: None,
        }
    }
}

impl<'tcx, 'ctx, 'ctx1, 'a> IntoFormatter for &'a BodyTransCtx<'tcx, 'ctx, 'ctx1> {
    type C = FmtCtx<'a>;

    fn into_fmt(self) -> Self::C {
        FmtCtx {
            type_decls: Some(&self.t_ctx.type_decls),
            fun_decls: Some(&self.t_ctx.fun_decls),
            global_decls: Some(&self.t_ctx.global_decls),
            trait_decls: Some(&self.t_ctx.trait_decls),
            trait_impls: Some(&self.t_ctx.trait_impls),
            region_vars: self.region_vars.clone(),
            type_vars: Some(&self.type_vars),
            const_generic_vars: Some(&self.const_generic_vars),
            locals: Some(&self.vars),
        }
    }
}

impl<'a> FmtCtx<'a> {
    fn fmt_decl_group<Id: Copy>(
        &self,
        f: &mut fmt::Formatter,
        gr: &GDeclarationGroup<Id>,
    ) -> fmt::Result
    where
        Self: DeclFormatter<Id>,
    {
        for id in gr.get_ids() {
            writeln!(f, "{}\n", self.format_decl(id))?
        }
        fmt::Result::Ok(())
    }
}

impl<'tcx, 'ctx> fmt::Display for TransCtx<'tcx, 'ctx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let fmt: FmtCtx = self.into_fmt();

        match &self.ordered_decls {
            None => {
                // We do simple: types, globals, traits, functions
                for (_, d) in &self.type_decls {
                    writeln!(f, "{}\n", fmt.format_object(d))?
                }

                for (_, d) in &self.global_decls {
                    writeln!(f, "{}\n", fmt.format_object(d))?
                }

                for (_, d) in &self.trait_decls {
                    writeln!(f, "{}\n", fmt.format_object(d))?
                }

                for (_, d) in &self.trait_impls {
                    writeln!(f, "{}\n", fmt.format_object(d))?
                }

                for (_, d) in &self.fun_decls {
                    writeln!(f, "{}\n", fmt.format_object(d))?
                }
            }
            Some(ordered_decls) => {
                for gr in ordered_decls {
                    use DeclarationGroup::*;
                    match gr {
                        Type(gr) => fmt.fmt_decl_group(f, gr)?,
                        Fun(gr) => fmt.fmt_decl_group(f, gr)?,
                        Global(gr) => fmt.fmt_decl_group(f, gr)?,
                        TraitDecl(gr) => fmt.fmt_decl_group(f, gr)?,
                        TraitImpl(gr) => fmt.fmt_decl_group(f, gr)?,
                    }
                }
            }
        };

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
        let fmt: FmtCtx = self.into_fmt();

        match &self.ordered_decls {
            None => {
                // We do simple: types, globals, traits, functions
                for (_, d) in &self.type_decls {
                    writeln!(f, "{}\n", fmt.format_object(d))?
                }

                for (_, d) in llbc_globals {
                    writeln!(f, "{}\n", fmt.format_object(d))?
                }

                for (_, d) in &self.trait_decls {
                    writeln!(f, "{}\n", fmt.format_object(d))?
                }

                for (_, d) in &self.trait_impls {
                    writeln!(f, "{}\n", fmt.format_object(d))?
                }

                for (_, d) in llbc_funs {
                    writeln!(f, "{}\n", fmt.format_object(d))?
                }
            }
            Some(ordered_decls) => {
                for gr in ordered_decls {
                    use DeclarationGroup::*;
                    match gr {
                        Type(gr) => fmt.fmt_decl_group(f, gr)?,
                        Fun(gr) => {
                            for id in gr.get_ids() {
                                match llbc_funs.get(id) {
                                    None => writeln!(f, "Unknown decl: {:?}\n", id)?,
                                    Some(d) => writeln!(f, "{}\n", d.fmt_with_ctx(&fmt))?,
                                }
                            }
                        }
                        Global(gr) => {
                            for id in gr.get_ids() {
                                match llbc_globals.get(id) {
                                    None => writeln!(f, "Unknown decl: {:?}\n", id)?,
                                    Some(d) => writeln!(f, "{}\n", d.fmt_with_ctx(&fmt))?,
                                }
                            }
                        }
                        TraitDecl(gr) => fmt.fmt_decl_group(f, gr)?,
                        TraitImpl(gr) => fmt.fmt_decl_group(f, gr)?,
                    }
                }
            }
        };

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
