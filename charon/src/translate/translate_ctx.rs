//! The translation contexts.
use crate::common::*;
use crate::formatter::{DeclFormatter, FmtCtx, Formatter, IntoFormatter};
use crate::gast::*;
use crate::get_mir::MirLevel;
use crate::ids::{Generator, MapGenerator, Vector};
use crate::llbc_ast;
use crate::meta::{self, Attribute, ItemMeta, RawSpan};
use crate::meta::{FileId, FileName, InlineAttr, LocalFileId, Span, VirtualFileId};
use crate::names::Name;
use crate::pretty::FmtWithCtx;
use crate::reorder_decls::{DeclarationGroup, DeclarationsGroups, GDeclarationGroup};
use crate::translate_predicates::NonLocalTraitClause;
use crate::translate_traits::ClauseTransCtx;
use crate::types::*;
use crate::ullbc_ast as ast;
use crate::values::*;
use hax_frontend_exporter as hax;
use hax_frontend_exporter::SInto;
use linked_hash_set::LinkedHashSet;
use macros::{EnumAsGetters, EnumIsA, VariantIndexArity, VariantName};
use rustc_error_messages::MultiSpan;
use rustc_hir::def_id::DefId;
use rustc_hir::Node as HirNode;
use rustc_middle::ty::TyCtxt;
use rustc_session::Session;
use std::cmp::{Ord, Ordering, PartialOrd};
use std::collections::{BTreeMap, HashMap, HashSet, VecDeque};
use std::fmt;

macro_rules! register_error_or_panic {
    ($ctx:expr, $span: expr, $msg: expr) => {{
        $ctx.span_err($span, &$msg);
        if !$ctx.continue_on_failure() {
            panic!("{}", $msg);
        }
    }};
}
pub(crate) use register_error_or_panic;

/// Macro to either panic or return on error, depending on the CLI options
macro_rules! error_or_panic {
    ($ctx:expr, $span:expr, $msg:expr) => {{
        $crate::translate_ctx::register_error_or_panic!($ctx, $span, $msg);
        let e = crate::common::Error {
            span: $span,
            msg: $msg.to_string(),
        };
        return Err(e);
    }};
}
pub(crate) use error_or_panic;

/// Custom assert to either panic or return an error
macro_rules! error_assert {
    ($ctx:expr, $span: expr, $b: expr) => {
        if !$b {
            let msg = format!("assertion failure: {:?}", stringify!($b));
            $crate::translate_ctx::error_or_panic!($ctx, $span, msg);
        }
    };
    ($ctx:expr, $span: expr, $b: expr, $msg: expr) => {
        if !$b {
            $crate::translate_ctx::error_or_panic!($ctx, $span, $msg);
        }
    };
}
pub(crate) use error_assert;

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

/// The id of a translated item.
#[derive(
    PartialEq,
    Eq,
    Hash,
    EnumIsA,
    EnumAsGetters,
    VariantName,
    VariantIndexArity,
    Copy,
    Clone,
    Debug,
    PartialOrd,
    Ord,
)]
pub enum AnyTransId {
    Type(TypeDeclId),
    Fun(FunDeclId),
    Global(GlobalDeclId),
    TraitDecl(TraitDeclId),
    TraitImpl(TraitImplId),
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
    pub(crate) fn get_id(&self) -> DefId {
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

/// The options that control translation.
pub struct TransOptions {
    /// The level at which to extract the MIR
    pub mir_level: MirLevel,
    /// Error out if some code ends up being duplicated by the control-flow
    /// reconstruction (note that because several patterns in a match may lead
    /// to the same branch, it is node always possible not to duplicate code).
    pub no_code_duplication: bool,
    /// Whether to extract the bodies of foreign methods and structs with private fields.
    pub extract_opaque_bodies: bool,
    /// Modules to consider opaque.
    pub opaque_mods: HashSet<String>,
}

/// The data of a translated crate.
#[derive(Default)]
pub struct TranslatedCrate {
    /// The name of the crate.
    pub crate_name: String,

    /// File names to ids and vice-versa
    pub file_to_id: HashMap<FileName, FileId>,
    pub id_to_file: HashMap<FileId, FileName>,
    pub real_file_counter: Generator<LocalFileId>,
    pub virtual_file_counter: Generator<VirtualFileId>,

    /// All the ids, in the order in which we encountered them
    pub all_ids: LinkedHashSet<AnyTransId>,
    /// The map from rustc id to translated id.
    pub id_map: HashMap<DefId, AnyTransId>,
    /// The reverse map of ids.
    pub reverse_id_map: HashMap<AnyTransId, DefId>,
    /// Generator of translated type ids
    pub type_id_gen: Generator<TypeDeclId>,
    /// Generator of translated function ids.
    pub fun_id_gen: Generator<ast::FunDeclId>,
    /// Generator of translated global ids.
    pub global_id_gen: Generator<ast::GlobalDeclId>,
    /// Generator of translated trait decl ids
    pub trait_decl_id_gen: Generator<ast::TraitDeclId>,
    /// Generator of translated trait impls ids
    pub trait_impl_id_gen: Generator<ast::TraitImplId>,

    /// The translated type definitions
    pub type_decls: TypeDecls,
    /// The translated function definitions
    pub fun_decls: ast::FunDecls,
    /// The translated and reconstructed function definitions
    pub structured_fun_decls: llbc_ast::FunDecls,
    /// The translated global definitions
    pub global_decls: ast::GlobalDecls,
    /// The translated and reconstructed global definitions
    pub structured_global_decls: llbc_ast::GlobalDecls,
    /// The translated trait declarations
    pub trait_decls: ast::TraitDecls,
    /// The translated trait declarations
    pub trait_impls: ast::TraitImpls,
    /// The re-ordered groups of declarations, initialized as empty.
    pub ordered_decls: Option<DeclarationsGroups>,
}

/// The context for tracking and reporting errors.
pub struct ErrorCtx<'ctx> {
    /// If true, do not abort on the first error and attempt to extract as much as possible.
    pub continue_on_failure: bool,
    /// If true, print the errors as warnings, and do not abort.
    pub errors_as_warnings: bool,

    /// The compiler session, used for displaying errors.
    pub session: &'ctx Session,
    /// The ids of the declarations for which extraction we encountered errors.
    pub decls_with_errors: HashSet<DefId>,
    /// The ids of the declarations we completely failed to extract and had to ignore.
    pub ignored_failed_decls: HashSet<DefId>,
    /// Dependency graph with sources. See [DepSource].
    pub dep_sources: HashMap<DefId, HashSet<DepSource>>,
    /// The id of the definition we are exploring, used to track the source of errors.
    pub def_id: Option<DefId>,
    /// The number of errors encountered so far.
    pub error_count: usize,
}

/// Translation context used while translating the crate data into our representation.
pub struct TranslateCtx<'tcx, 'ctx> {
    /// The Rust compiler type context
    pub tcx: TyCtxt<'tcx>,
    /// The Hax context
    pub hax_state: hax::State<hax::Base<'tcx>, (), (), ()>,

    /// The options that control translation.
    pub options: TransOptions,
    /// The translated data.
    pub translated: TranslatedCrate,

    /// Context for tracking and reporting errors.
    pub errors: ErrorCtx<'ctx>,
    /// The declarations we came accross and which we haven't translated yet.
    /// We use an ordered map to make sure we translate them in a specific
    /// order (this avoids stealing issues when querying the MIR bodies).
    pub priority_queue: BTreeMap<OrdRustId, AnyTransId>,
}

/// A translation context for type/global/function bodies.
/// Simply augments the [TranslateCtx] with local variables.
///
/// Remark: for now we don't really need to use collections from the [im] crate,
/// because we don't need the O(1) clone operation, but we may need it once we
/// implement support for universally quantified traits, where we might need
/// to be able to dive in/out of universal quantifiers. Also, it doesn't cost
/// us to use those collections.
pub(crate) struct BodyTransCtx<'tcx, 'ctx, 'ctx1> {
    /// The definition we are currently extracting.
    /// TODO: this duplicates the field of [TranslateCtx]
    pub def_id: DefId,
    /// The translation context containing the top-level definitions/ids.
    pub t_ctx: &'ctx mut TranslateCtx<'tcx, 'ctx1>,
    /// A hax state with an owner id
    pub hax_state: hax::State<hax::Base<'tcx>, (), (), rustc_hir::def_id::DefId>,
    /// The regions.
    /// We use DeBruijn indices, so we have a stack of regions.
    /// See the comments for [Region::BVar].
    pub region_vars: im::Vector<Vector<RegionId, RegionVar>>,
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
    pub free_region_vars: std::collections::BTreeMap<hax::Region, RegionId>,
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
    pub bound_region_vars: im::Vector<im::Vector<RegionId>>,
    /// The type variables
    pub type_vars: Vector<TypeVarId, TypeVar>,
    /// The map from rust type variable indices to translated type variable
    /// indices.
    pub type_vars_map: MapGenerator<u32, TypeVarId>,
    /// The "regular" variables
    pub vars: Vector<VarId, ast::Var>,
    /// The map from rust variable indices to translated variables indices.
    pub vars_map: MapGenerator<usize, VarId>,
    /// The const generic variables
    pub const_generic_vars: Vector<ConstGenericVarId, ConstGenericVar>,
    /// The map from rust const generic variables to translate const generic
    /// variable indices.
    pub const_generic_vars_map: MapGenerator<u32, ConstGenericVarId>,
    /// A context for clause translation. It accumulates translated clauses.
    pub clause_translation_context: ClauseTransCtx,
    /// All the trait clauses accessible from the current environment. When `hax` gives us a
    /// `ImplExprAtom::LocalBound`, we use this to recover the specific trait reference it
    /// corresponds to.
    /// FIXME: hax should take care of this matching up.
    pub trait_clauses: HashMap<TraitDeclId, Vec<NonLocalTraitClause>>,
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
    /// The translated blocks. We can't use `ast::Vector<BlockId, ast::BlockData>`
    /// here because we might generate several fresh indices before actually
    /// adding the resulting blocks to the map.
    pub blocks: im::OrdMap<ast::BlockId, ast::BlockData>,
    /// The map from rust blocks to translated blocks.
    /// Note that when translating terminators like DropAndReplace, we might have
    /// to introduce new blocks which don't appear in the original MIR.
    pub blocks_map: MapGenerator<hax::BasicBlock, ast::BlockId>,
    /// We register the blocks to translate in a stack, so as to avoid
    /// writing the translation functions as recursive functions. We do
    /// so because we had stack overflows in the past.
    pub blocks_stack: VecDeque<hax::BasicBlock>,
}

impl ErrorCtx<'_> {
    pub(crate) fn continue_on_failure(&self) -> bool {
        self.continue_on_failure
    }
    pub(crate) fn has_errors(&self) -> bool {
        self.error_count > 0
    }

    /// Report an error without registering anything.
    pub(crate) fn span_err_no_register<S: Into<MultiSpan>>(&self, span: S, msg: &str) {
        let msg = msg.to_string();
        if self.errors_as_warnings {
            self.session.span_warn(span, msg);
        } else {
            self.session.span_err(span, msg);
        }
    }

    /// Report and register an error.
    pub fn span_err<S: Into<MultiSpan>>(&mut self, span: S, msg: &str) {
        self.span_err_no_register(span, msg);
        self.error_count += 1;
        if let Some(id) = self.def_id {
            let _ = self.decls_with_errors.insert(id);
        }
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

    pub(crate) fn ignore_failed_decl(&mut self, id: DefId) {
        self.ignored_failed_decls.insert(id);
    }
}

impl<'tcx, 'ctx> TranslateCtx<'tcx, 'ctx> {
    pub fn continue_on_failure(&self) -> bool {
        self.errors.continue_on_failure()
    }

    /// Span an error and register the error.
    pub fn span_err<S: Into<MultiSpan>>(&mut self, span: S, msg: &str) {
        self.errors.span_err(span, msg)
    }

    /// Register a file if it is a "real" file and was not already registered
    fn register_file(&mut self, filename: FileName) -> FileId {
        // Lookup the file if it was already registered
        match self.translated.file_to_id.get(&filename) {
            Option::Some(id) => *id,
            Option::None => {
                // Generate the fresh id
                let id = match &filename {
                    FileName::Local(_) => {
                        FileId::LocalId(self.translated.real_file_counter.fresh_id())
                    }
                    FileName::Virtual(_) => {
                        FileId::VirtualId(self.translated.virtual_file_counter.fresh_id())
                    }
                    FileName::NotReal(_) => unimplemented!(),
                };
                self.translated.file_to_id.insert(filename.clone(), id);
                self.translated.id_to_file.insert(id, filename);
                id
            }
        }
    }

    /// Compute the span information for a Rust definition identified by its id.
    pub(crate) fn translate_span_from_rid(&mut self, def_id: DefId) -> Span {
        // Retrieve the span from the def id
        let rspan = meta::get_rspan_from_def_id(self.tcx, def_id);
        let rspan = rspan.sinto(&self.hax_state);
        self.translate_span_from_rspan(rspan)
    }

    /// Compute the meta information for a Rust item identified by its id.
    pub(crate) fn translate_item_meta_from_rid(&mut self, def_id: DefId) -> ItemMeta {
        let span = self.translate_span_from_rid(def_id);
        // Default to `false` for impl blocks and closures.
        let public = self
            .translate_visibility_from_rid(def_id, span.span)
            .unwrap_or(false);
        let attributes = self.translate_attributes_from_rid(def_id);
        let opaque = attributes
            .iter()
            .any(|attr| attr == "charon::opaque" || attr == "aeneas::opaque");
        let rename = {
            let str = attributes.iter().find(|str| {
                str.starts_with("charon::rename(") || str.starts_with("aeneas::rename(")
            });
            if let Some(str) = str {
                let charon_rename = str.strip_prefix("charon::rename(\"");
                let aeneas_rename = str.strip_prefix("aeneas::rename(\"");
                let rename = charon_rename
                    .or(aeneas_rename)
                    .and_then(|str| str.strip_suffix("\")"));
                if let Some(str) = rename {
                    if !str.is_empty() {
                        let first_char_alphabetic = str
                            .chars()
                            .nth(0)
                            .expect("Attribute `rename` should not be empty")
                            .is_alphabetic();
                        let is_identifier = first_char_alphabetic
                            && str
                                .chars()
                                .all(|c| c.is_alphanumeric() || c == '_' || c == '-');
                        if !is_identifier {
                            self.span_err(span, "Attribute `rename` should only contains alphanumeric characters, `_` and `-` and should start with a letter");
                            None
                        } else {
                            Some(rename.unwrap().to_string())
                        }
                    } else {
                        self.span_err(span, "Attribute `rename` should not be empty");
                        None
                    }
                } else {
                    self.span_err(
                        span,
                        "Attribute `rename` should be of the shape `rename(\"...\")`",
                    );
                    None
                }
            } else {
                None
            }
        };
        ItemMeta {
            span,
            attributes: attributes,
            inline: self.translate_inline_from_rid(def_id),
            public,
            opaque,
            rename,
        }
    }

    pub fn translate_span(&mut self, rspan: hax::Span) -> meta::RawSpan {
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
        meta::RawSpan {
            file_id,
            beg,
            end,
            rust_span_data: rspan.rust_span_data.unwrap(),
        }
    }

    /// Compute span data from a Rust source scope
    pub fn translate_span_from_source_info(
        &mut self,
        source_scopes: &hax::IndexVec<hax::SourceScope, hax::SourceScopeData>,
        source_info: &hax::SourceInfo,
    ) -> Span {
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

            Span {
                span: parent_span,
                generated_from_span: Some(span),
            }
        } else {
            Span {
                span,
                generated_from_span: None,
            }
        }
    }

    // TODO: rename
    pub(crate) fn translate_span_from_rspan(&mut self, rspan: hax::Span) -> Span {
        // Translate the span
        let span = self.translate_span(rspan);

        Span {
            span,
            generated_from_span: None,
        }
    }

    /// Returns the attributes (`#[...]`) of this item.
    pub(crate) fn item_attributes(&self, id: DefId) -> &[rustc_ast::Attribute] {
        use rustc_hir::hir_id::HirId;
        id.as_local()
            .map(|local_def_id| self.tcx.hir().attrs(HirId::make_owner(local_def_id)))
            .unwrap_or_default()
    }

    /// Translates a rust attribute. Returns `None` if the attribute is a doc comment (rustc
    /// encodes them as attributes). For now we use `String`s for `Attributes`.
    pub(crate) fn translate_attribute(&self, attr: &rustc_ast::Attribute) -> Option<Attribute> {
        use rustc_ast::ast::AttrKind;
        use rustc_ast_pretty::pprust;
        match &attr.kind {
            AttrKind::Normal(normal_attr) => {
                // Use `pprust` to render the attribute like it is written in the source.
                use pprust::PrintState;
                Some(pprust::State::to_string(|s| {
                    s.print_attr_item(&normal_attr.item, attr.span)
                }))
            }
            AttrKind::DocComment(..) => None,
        }
    }

    pub(crate) fn translate_attributes_from_rid(&self, id: DefId) -> Vec<Attribute> {
        self.item_attributes(id)
            .iter()
            .filter_map(|attr| self.translate_attribute(attr))
            .collect()
    }

    pub(crate) fn translate_inline_from_rid(&self, id: DefId) -> Option<InlineAttr> {
        use rustc_attr as rustc;
        if !self.tcx.def_kind(id).has_codegen_attrs() {
            return None;
        }
        match self.tcx.codegen_fn_attrs(id).inline {
            rustc::InlineAttr::None => None,
            rustc::InlineAttr::Hint => Some(InlineAttr::Hint),
            rustc::InlineAttr::Never => Some(InlineAttr::Never),
            rustc::InlineAttr::Always => Some(InlineAttr::Always),
        }
    }

    /// Returns the visibility of the item/field/etc. Returns `None` for items that don't have a
    /// visibility, like impl blocks.
    pub(crate) fn translate_visibility_from_rid(
        &mut self,
        id: DefId,
        span: RawSpan,
    ) -> Option<bool> {
        use rustc_hir::def::DefKind::*;
        let def_kind = self.tcx.def_kind(id);
        match def_kind {
            AssocConst
            | AssocFn
            | Const
            | Enum
            | Field
            | Fn
            | ForeignTy
            | Macro { .. }
            | Mod
            | Static { .. }
            | Struct
            | Trait
            | TraitAlias
            | TyAlias { .. }
            | Union
            | Use => Some(self.tcx.visibility(id).is_public()),
            // These kinds don't have visibility modifiers (which would cause `visibility` to panic).
            Closure | Impl { .. } => None,
            // Kinds we shouldn't be calling this function on.
            AnonConst
            | AssocTy
            | ConstParam
            | Ctor { .. }
            | ExternCrate
            | ForeignMod
            | Generator
            | GlobalAsm
            | InlineConst
            | LifetimeParam
            | OpaqueTy
            | TyParam
            | Variant => {
                register_error_or_panic!(
                    self,
                    span,
                    "Called `translate_visibility_from_rid` on `{def_kind:?}`"
                );
                None
            }
        }
    }

    /// Whether this item is in an `extern { .. }` block, in which case it has no body.
    pub(crate) fn id_is_extern_item(&mut self, id: DefId) -> bool {
        id.as_local().is_some_and(|local_def_id| {
            let node = self.tcx.hir().find_by_def_id(local_def_id);
            matches!(node, Some(HirNode::ForeignItem(_)))
        })
    }

    pub(crate) fn is_opaque_name(&self, name: &Name) -> bool {
        name.is_in_modules(&self.translated.crate_name, &self.options.opaque_mods)
    }

    pub(crate) fn id_is_opaque(&mut self, id: DefId) -> Result<bool, Error> {
        let name = self.def_id_to_name(id)?;
        Ok(self.is_opaque_name(&name) || self.id_is_extern_item(id))
    }

    pub(crate) fn id_is_transparent(&mut self, id: DefId) -> Result<bool, Error> {
        Ok(!(self.id_is_opaque(id)?))
    }

    /// Register the fact that `id` is a dependency of `src` (if `src` is not `None`).
    pub(crate) fn register_dep_source(&mut self, src: &Option<DepSource>, id: DefId) {
        self.errors.register_dep_source(src, id)
    }

    pub(crate) fn register_id(&mut self, src: &Option<DepSource>, id: OrdRustId) -> AnyTransId {
        let rust_id = id.get_id();
        self.register_dep_source(src, rust_id);
        match self.translated.id_map.get(&rust_id) {
            Some(tid) => *tid,
            None => {
                let trans_id = match id {
                    OrdRustId::Type(_) => AnyTransId::Type(self.translated.type_id_gen.fresh_id()),
                    OrdRustId::TraitDecl(_) => {
                        AnyTransId::TraitDecl(self.translated.trait_decl_id_gen.fresh_id())
                    }
                    OrdRustId::TraitImpl(_) => {
                        AnyTransId::TraitImpl(self.translated.trait_impl_id_gen.fresh_id())
                    }
                    OrdRustId::Global(_) => {
                        AnyTransId::Global(self.translated.global_id_gen.fresh_id())
                    }
                    OrdRustId::ConstFun(_) | OrdRustId::Fun(_) => {
                        AnyTransId::Fun(self.translated.fun_id_gen.fresh_id())
                    }
                };
                // Add the id to the queue of declarations to translate
                self.priority_queue.insert(id, trans_id);
                self.translated.id_map.insert(id.get_id(), trans_id);
                self.translated.reverse_id_map.insert(trans_id, id.get_id());
                self.translated.all_ids.insert(trans_id);
                trans_id
            }
        }
    }

    pub(crate) fn register_type_decl_id(
        &mut self,
        src: &Option<DepSource>,
        id: DefId,
    ) -> TypeDeclId {
        *self.register_id(src, OrdRustId::Type(id)).as_type()
    }

    pub(crate) fn register_fun_decl_id(
        &mut self,
        src: &Option<DepSource>,
        id: DefId,
    ) -> ast::FunDeclId {
        // FIXME: cache this or even better let hax handle this
        let id = if self.tcx.is_const_fn_raw(id) {
            OrdRustId::ConstFun(id)
        } else {
            OrdRustId::Fun(id)
        };
        *self.register_id(src, id).as_fun()
    }

    /// Returns an [Option] because we may ignore some builtin or auto traits
    /// like [core::marker::Sized] or [core::marker::Sync].
    pub(crate) fn register_trait_decl_id(
        &mut self,
        src: &Option<DepSource>,
        id: DefId,
    ) -> Result<Option<ast::TraitDeclId>, Error> {
        use crate::assumed;
        if assumed::IGNORE_BUILTIN_MARKER_TRAITS {
            let name = self.def_id_to_name(id)?;
            if assumed::is_marker_trait(&name) {
                return Ok(None);
            }
        }

        let id = OrdRustId::TraitDecl(id);
        let trait_decl_id = *self.register_id(src, id).as_trait_decl();
        Ok(Some(trait_decl_id))
    }

    /// Returns an [Option] because we may ignore some builtin or auto traits
    /// like [core::marker::Sized] or [core::marker::Sync].
    pub(crate) fn register_trait_impl_id(
        &mut self,
        src: &Option<DepSource>,
        rust_id: DefId,
    ) -> Result<Option<ast::TraitImplId>, Error> {
        // Check if we need to filter
        {
            // Retrieve the id of the implemented trait decl
            let id = self.tcx.trait_id_of_impl(rust_id).unwrap();
            let _ = self.register_trait_decl_id(src, id)?;
        }

        let id = OrdRustId::TraitImpl(rust_id);
        let trait_impl_id = *self.register_id(src, id).as_trait_impl();
        Ok(Some(trait_impl_id))
    }

    pub(crate) fn register_global_decl_id(
        &mut self,
        src: &Option<DepSource>,
        id: DefId,
    ) -> ast::GlobalDeclId {
        *self.register_id(src, OrdRustId::Global(id)).as_global()
    }

    pub(crate) fn with_def_id<F, T>(&mut self, def_id: DefId, f: F) -> T
    where
        F: FnOnce(&mut Self) -> T,
    {
        let current_def_id = self.errors.def_id;
        self.errors.def_id = Some(def_id);
        let ret = f(self);
        self.errors.def_id = current_def_id;
        ret
    }
}

impl<'tcx, 'ctx, 'ctx1> BodyTransCtx<'tcx, 'ctx, 'ctx1> {
    /// Create a new `ExecContext`.
    pub(crate) fn new(def_id: DefId, t_ctx: &'ctx mut TranslateCtx<'tcx, 'ctx1>) -> Self {
        let hax_state = t_ctx.make_hax_state_with_id(def_id);
        BodyTransCtx {
            def_id,
            t_ctx,
            hax_state,
            region_vars: im::vector![Vector::new()],
            free_region_vars: std::collections::BTreeMap::new(),
            bound_region_vars: im::Vector::new(),
            type_vars: Vector::new(),
            type_vars_map: MapGenerator::new(),
            vars: Vector::new(),
            vars_map: MapGenerator::new(),
            const_generic_vars: Vector::new(),
            const_generic_vars_map: MapGenerator::new(),
            clause_translation_context: Default::default(),
            trait_clauses: Default::default(),
            registering_trait_clauses: false,
            regions_outlive: Vec::new(),
            types_outlive: Vec::new(),
            trait_type_constraints: Vec::new(),
            blocks: im::OrdMap::new(),
            blocks_map: MapGenerator::new(),
            blocks_stack: VecDeque::new(),
        }
    }

    pub fn continue_on_failure(&self) -> bool {
        self.t_ctx.continue_on_failure()
    }

    pub fn span_err(&mut self, span: rustc_span::Span, msg: &str) {
        self.t_ctx.span_err(span, msg)
    }

    pub(crate) fn translate_span_from_rspan(&mut self, rspan: hax::Span) -> Span {
        self.t_ctx.translate_span_from_rspan(rspan)
    }

    pub(crate) fn get_local(&self, local: &hax::Local) -> Option<VarId> {
        use rustc_index::Idx;
        self.vars_map.get(&local.index())
    }

    #[allow(dead_code)]
    pub(crate) fn get_block_id_from_rid(&self, rid: hax::BasicBlock) -> Option<ast::BlockId> {
        self.blocks_map.get(&rid)
    }

    pub(crate) fn get_var_from_id(&self, var_id: VarId) -> Option<&ast::Var> {
        self.vars.get(var_id)
    }

    pub(crate) fn register_type_decl_id(
        &mut self,
        span: rustc_span::Span,
        id: DefId,
    ) -> TypeDeclId {
        let src = self.make_dep_source(span);
        self.t_ctx.register_type_decl_id(&src, id)
    }

    pub(crate) fn register_fun_decl_id(
        &mut self,
        span: rustc_span::Span,
        id: DefId,
    ) -> ast::FunDeclId {
        let src = self.make_dep_source(span);
        self.t_ctx.register_fun_decl_id(&src, id)
    }

    pub(crate) fn register_global_decl_id(
        &mut self,
        span: rustc_span::Span,
        id: DefId,
    ) -> ast::GlobalDeclId {
        let src = self.make_dep_source(span);
        self.t_ctx.register_global_decl_id(&src, id)
    }

    /// Returns an [Option] because we may ignore some builtin or auto traits
    /// like [core::marker::Sized] or [core::marker::Sync].
    pub(crate) fn register_trait_decl_id(
        &mut self,
        span: rustc_span::Span,
        id: DefId,
    ) -> Result<Option<ast::TraitDeclId>, Error> {
        let src = self.make_dep_source(span);
        self.t_ctx.register_trait_decl_id(&src, id)
    }

    /// Returns an [Option] because we may ignore some builtin or auto traits
    /// like [core::marker::Sized] or [core::marker::Sync].
    pub(crate) fn register_trait_impl_id(
        &mut self,
        span: rustc_span::Span,
        id: DefId,
    ) -> Result<Option<ast::TraitImplId>, Error> {
        let src = self.make_dep_source(span);
        self.t_ctx.register_trait_impl_id(&src, id)
    }

    /// Push a free region.
    ///
    /// Important: we must push *all* the free regions (which are early-bound
    /// regions) before pushing any (late-)bound region.
    pub(crate) fn push_free_region(&mut self, r: hax::Region, name: Option<String>) -> RegionId {
        // Check that there are no late-bound regions
        assert!(self.bound_region_vars.is_empty());
        let rid = self.region_vars[0].push_with(|index| RegionVar { index, name });
        self.free_region_vars.insert(r, rid);
        rid
    }

    /// Set the first bound regions group
    pub(crate) fn set_first_bound_regions_group(&mut self, names: Vec<Option<String>>) {
        assert!(self.bound_region_vars.is_empty());

        // Register the variables
        let var_ids: im::Vector<RegionId> = names
            .into_iter()
            .map(|name| self.region_vars[0].push_with(|index| RegionVar { index, name }))
            .collect();

        // Push the group
        self.bound_region_vars.push_front(var_ids);
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
        assert!(!self.region_vars.is_empty());
        self.region_vars.push_front(Vector::new());

        // Register the variables
        let var_ids: im::Vector<RegionId> = names
            .into_iter()
            .map(|name| self.region_vars[0].push_with(|index| RegionVar { index, name }))
            .collect();

        // Push the group
        self.bound_region_vars.push_front(var_ids);

        // Call the continuation
        let res = f(self);

        // Reset
        self.bound_region_vars.pop_front();
        self.region_vars.pop_front();

        // Return
        res
    }

    pub(crate) fn push_type_var(&mut self, rindex: u32, name: String) -> TypeVarId {
        let var_id = self.type_vars_map.insert(rindex);
        assert!(var_id == self.type_vars.next_id());
        self.type_vars.push_with(|index| TypeVar { index, name })
    }

    pub(crate) fn push_var(&mut self, rid: usize, ty: Ty, name: Option<String>) {
        let var_id = self.vars_map.insert(rid);
        assert!(var_id == self.vars.next_id());
        self.vars.push_with(|index| ast::Var { index, name, ty });
    }

    pub(crate) fn push_const_generic_var(&mut self, rid: u32, ty: LiteralTy, name: String) {
        let var_id = self.const_generic_vars_map.insert(rid);
        assert!(var_id == self.const_generic_vars.next_id());
        self.const_generic_vars
            .push_with(|index| (ConstGenericVar { index, name, ty }));
    }

    pub(crate) fn fresh_block_id(&mut self, rid: hax::BasicBlock) -> ast::BlockId {
        // Push to the stack of blocks awaiting translation
        self.blocks_stack.push_back(rid);
        // Insert in the map
        self.blocks_map.insert(rid)
    }

    pub(crate) fn push_block(&mut self, id: ast::BlockId, block: ast::BlockData) {
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
    pub(crate) fn get_local_trait_clauses(&self) -> Vector<TraitClauseId, TraitClause> {
        let ClauseTransCtx::Base(clauses) = &self.clause_translation_context else {
            panic!()
        };
        // Sanity check
        assert!(clauses
            .iter()
            .enumerate()
            .all(|(i, c)| c.clause_id.index() == i));
        // Return
        clauses.clone()
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
    pub(crate) fn with_clause_translation_context<F, T>(
        &mut self,
        new_ctx: ClauseTransCtx,
        f: F,
    ) -> (T, ClauseTransCtx)
    where
        F: FnOnce(&mut Self) -> T,
    {
        use std::mem::replace;

        // Save the trait instance id generator
        let old_ctx = replace(&mut self.clause_translation_context, new_ctx);

        // Apply the continuation
        let out = f(self);

        // Restore
        let new_ctx = replace(&mut self.clause_translation_context, old_ctx);

        // Return
        (out, new_ctx)
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

impl<'tcx, 'ctx, 'a> IntoFormatter for &'a TranslateCtx<'tcx, 'ctx> {
    type C = FmtCtx<'a>;

    fn into_fmt(self) -> Self::C {
        self.translated.into_fmt()
    }
}

impl<'tcx, 'ctx, 'a> IntoFormatter for &'a TranslatedCrate {
    type C = FmtCtx<'a>;

    fn into_fmt(self) -> Self::C {
        FmtCtx {
            translated: Some(self),
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
            translated: Some(&self.t_ctx.translated),
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

impl<'tcx, 'ctx> fmt::Display for TranslateCtx<'tcx, 'ctx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.translated.fmt_with_ullbc_defs(f)
    }
}

impl TranslatedCrate {
    pub(crate) fn fmt_with_ullbc_defs(&self, f: &mut fmt::Formatter) -> fmt::Result {
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

    pub(crate) fn fmt_with_llbc_defs(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let fmt: FmtCtx = self.into_fmt();
        let llbc_globals = &self.structured_global_decls;
        let llbc_funs = &self.structured_fun_decls;

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

pub struct LlbcFmtCtx<'a> {
    pub translated: &'a TranslatedCrate,
}

impl<'a> fmt::Display for LlbcFmtCtx<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.translated.fmt_with_llbc_defs(f)
    }
}
