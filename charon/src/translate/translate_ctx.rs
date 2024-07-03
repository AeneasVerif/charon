//! The translation contexts.
use crate::common::*;
use crate::formatter::{FmtCtx, Formatter, IntoFormatter};
use crate::gast::*;
use crate::get_mir::MirLevel;
use crate::ids::{Generator, MapGenerator, Vector};
use crate::meta::{self, AttrInfo, Attribute, ItemMeta, ItemOpacity, RawSpan};
use crate::meta::{FileId, FileName, InlineAttr, LocalFileId, Span, VirtualFileId};
use crate::names::Name;
use crate::reorder_decls::DeclarationsGroups;
use crate::translate_predicates::NonLocalTraitClause;
use crate::translate_traits::ClauseTransCtx;
use crate::types::*;
use crate::ullbc_ast as ast;
use crate::values::*;
use derive_visitor::{Drive, DriveMut};
use hax_frontend_exporter as hax;
use hax_frontend_exporter::SInto;
use linked_hash_set::LinkedHashSet;
use macros::{EnumAsGetters, EnumIsA, VariantIndexArity, VariantName};
use rustc_error_messages::MultiSpan;
use rustc_errors::DiagCtxtHandle;
use rustc_hir::def_id::DefId;
use rustc_hir::Node as HirNode;
use rustc_middle::ty::TyCtxt;
use serde::{Deserialize, Serialize};
use std::cmp::{Ord, PartialOrd};
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
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct DepSource {
    pub src_id: DefId,
    pub span: rustc_span::Span,
}

impl DepSource {
    /// Value with which we order `DepSource`s.
    fn sort_key(&self) -> impl Ord {
        (self.src_id.index, self.src_id.krate)
    }
}

/// Manual impls because `DefId` is not orderable.
impl PartialOrd for DepSource {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for DepSource {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.sort_key().cmp(&other.sort_key())
    }
}

impl DepSource {
    pub(crate) fn make(src_id: DefId, span: rustc_span::Span) -> Option<Self> {
        Some(DepSource { src_id, span })
    }
}

/// The id of a translated item.
#[derive(
    Copy,
    Clone,
    Debug,
    PartialOrd,
    Ord,
    PartialEq,
    Eq,
    Hash,
    EnumIsA,
    EnumAsGetters,
    VariantName,
    VariantIndexArity,
    Serialize,
    Deserialize,
    Drive,
    DriveMut,
)]
pub enum AnyTransId {
    Type(TypeDeclId),
    Fun(FunDeclId),
    Global(GlobalDeclId),
    TraitDecl(TraitDeclId),
    TraitImpl(TraitImplId),
}

/// Implement `TryFrom`  and `From` to convert between an enum and its variants.
macro_rules! wrap_unwrap_enum {
    ($enum:ident::$variant:ident($variant_ty:ident)) => {
        impl TryFrom<$enum> for $variant_ty {
            type Error = ();
            fn try_from(x: $enum) -> Result<Self, Self::Error> {
                match x {
                    $enum::$variant(x) => Ok(x),
                    _ => Err(()),
                }
            }
        }

        impl From<$variant_ty> for $enum {
            fn from(x: $variant_ty) -> Self {
                $enum::$variant(x)
            }
        }
    };
}

wrap_unwrap_enum!(AnyTransId::Fun(FunDeclId));
wrap_unwrap_enum!(AnyTransId::Global(GlobalDeclId));
wrap_unwrap_enum!(AnyTransId::Type(TypeDeclId));
wrap_unwrap_enum!(AnyTransId::TraitDecl(TraitDeclId));
wrap_unwrap_enum!(AnyTransId::TraitImpl(TraitImplId));

/// A translated item.
#[derive(Debug, Clone, Copy, EnumIsA, EnumAsGetters, VariantName, VariantIndexArity)]
pub enum AnyTransItem<'ctx> {
    Type(&'ctx TypeDecl),
    Fun(&'ctx FunDecl),
    Global(&'ctx GlobalDecl),
    TraitDecl(&'ctx TraitDecl),
    TraitImpl(&'ctx TraitImpl),
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

impl OrdRustId {
    /// Value with which we order values.
    fn sort_key(&self) -> impl Ord {
        let (variant_index, _) = self.variant_index_arity();
        let def_id = self.get_id();
        (variant_index, def_id.index, def_id.krate)
    }
}

/// Manual impls because `DefId` is not orderable.
impl PartialOrd for OrdRustId {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for OrdRustId {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.sort_key().cmp(&other.sort_key())
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

    /// The translated type definitions
    pub type_decls: Vector<TypeDeclId, TypeDecl>,
    /// The translated function definitions
    pub fun_decls: Vector<FunDeclId, FunDecl>,
    /// The translated global definitions
    pub global_decls: Vector<GlobalDeclId, GlobalDecl>,
    /// The bodies of functions and constants
    pub bodies: Vector<BodyId, Body>,
    /// The translated trait declarations
    pub trait_decls: Vector<TraitDeclId, TraitDecl>,
    /// The translated trait declarations
    pub trait_impls: Vector<TraitImplId, TraitImpl>,
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
    pub dcx: DiagCtxtHandle<'ctx>,
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
    /// Stack of the translations currently happening. Used to avoid cycles where items need to
    /// translate themselves transitively.
    pub translate_stack: Vec<AnyTransId>,
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
    pub region_vars: VecDeque<Vector<RegionId, RegionVar>>,
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
    /// **Important**:
    /// ==============
    /// We use DeBruijn indices. See the comments for [Region::Var].
    pub bound_region_vars: VecDeque<Box<[RegionId]>>,
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
    pub trait_clauses: BTreeMap<TraitDeclId, Vec<NonLocalTraitClause>>,
    ///
    pub types_outlive: Vec<TypeOutlives>,
    ///
    pub regions_outlive: Vec<RegionOutlives>,
    ///
    pub trait_type_constraints: Vec<TraitTypeConstraint>,
    /// The translated blocks. We can't use `ast::Vector<BlockId, ast::BlockData>`
    /// here because we might generate several fresh indices before actually
    /// adding the resulting blocks to the map.
    pub blocks: BTreeMap<ast::BlockId, ast::BlockData>,
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
            self.dcx.span_warn(span, msg);
        } else {
            self.dcx.span_err(span, msg);
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

impl TranslatedCrate {
    pub fn get_item(&self, trans_id: AnyTransId) -> Option<AnyTransItem<'_>> {
        match trans_id {
            AnyTransId::Type(id) => self.type_decls.get(id).map(AnyTransItem::Type),
            AnyTransId::Fun(id) => self.fun_decls.get(id).map(AnyTransItem::Fun),
            AnyTransId::Global(id) => self.global_decls.get(id).map(AnyTransItem::Global),
            AnyTransId::TraitDecl(id) => self.trait_decls.get(id).map(AnyTransItem::TraitDecl),
            AnyTransId::TraitImpl(id) => self.trait_impls.get(id).map(AnyTransItem::TraitImpl),
        }
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
            Some(id) => *id,
            None => {
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

    pub(crate) fn translate_attr_info_from_rid(&mut self, def_id: DefId, span: Span) -> AttrInfo {
        // Default to `false` for impl blocks and closures.
        let public = self
            .translate_visibility_from_rid(def_id, span.span)
            .unwrap_or(false);
        let attributes = self.translate_attributes_from_rid(def_id);

        let rename = {
            let mut renames = attributes
                .iter()
                .filter(|a| a.is_rename())
                .map(|a| a.as_rename())
                .cloned();
            let rename = renames.next();
            if renames.next().is_some() {
                self.span_err(
                    span,
                    "There should be at most one `charon::rename(\"...\")` \
                    or `aeneas::rename(\"...\")` attribute per declaration",
                );
            }
            rename
        };

        AttrInfo {
            attributes,
            inline: self.translate_inline_from_rid(def_id),
            public,
            rename,
        }
    }

    /// Compute the meta information for a Rust item identified by its id.
    pub(crate) fn translate_item_meta_from_rid(
        &mut self,
        def_id: DefId,
    ) -> Result<ItemMeta, Error> {
        let span = self.translate_span_from_rid(def_id);
        let name = self.def_id_to_name(def_id)?;
        let attr_info = self.translate_attr_info_from_rid(def_id, span);
        let is_local = def_id.is_local();

        let opacity = {
            let is_opaque = self.is_opaque_name(&name)
                || self.id_is_extern_item(def_id)
                || attr_info.attributes.iter().any(|attr| attr.is_opaque());
            if is_opaque {
                ItemOpacity::Opaque
            } else if !is_local && !self.options.extract_opaque_bodies {
                ItemOpacity::Foreign
            } else {
                ItemOpacity::Transparent
            }
        };

        Ok(ItemMeta {
            span,
            attr_info,
            name,
            is_local,
            opacity,
        })
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

    /// Returns the attributes (`#[...]`) of this node.
    pub(crate) fn node_attributes(&self, id: DefId) -> &[rustc_ast::Attribute] {
        id.as_local()
            .map(|local_def_id| {
                self.tcx
                    .hir()
                    .attrs(self.tcx.local_def_id_to_hir_id(local_def_id))
            })
            .unwrap_or_default()
    }

    /// Translates a rust attribute. Returns `None` if the attribute is a doc comment (rustc
    /// encodes them as attributes). For now we use `String`s for `Attributes`.
    pub(crate) fn translate_attribute(&mut self, attr: &rustc_ast::Attribute) -> Option<Attribute> {
        use rustc_ast::ast::AttrKind;
        use rustc_ast_pretty::pprust;
        match &attr.kind {
            AttrKind::Normal(normal_attr) => {
                // Use `pprust` to render the attribute somewhat like it is written in the source.
                // WARNING: this can change whitespace, and soetimes even adds newlines. Maybe we
                // should use spans and SourceMap info instead.
                use pprust::PrintState;
                let s =
                    pprust::State::to_string(|s| s.print_attr_item(&normal_attr.item, attr.span));
                match Attribute::parse(s) {
                    Ok(a) => Some(a),
                    Err(msg) => {
                        self.span_err(attr.span, &format!("Error parsing attribute: {msg}"));
                        None
                    }
                }
            }
            AttrKind::DocComment(..) => None,
        }
    }

    pub(crate) fn translate_attributes_from_rid(&mut self, id: DefId) -> Vec<Attribute> {
        // Collect to drop the borrow on `self`.
        let vec = self.node_attributes(id).to_vec();
        vec.iter()
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
            | Use
            | Variant => Some(self.tcx.visibility(id).is_public()),
            // These kinds don't have visibility modifiers (which would cause `visibility` to panic).
            Closure | Impl { .. } => None,
            // Kinds we shouldn't be calling this function on.
            AnonConst
            | AssocTy
            | ConstParam
            | Ctor { .. }
            | ExternCrate
            | ForeignMod
            | GlobalAsm
            | InlineConst
            | LifetimeParam
            | OpaqueTy
            | TyParam => {
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
        self.tcx
            .hir()
            .get_if_local(id)
            .is_some_and(|node| matches!(node, HirNode::ForeignItem(_)))
    }

    pub(crate) fn is_opaque_name(&self, name: &Name) -> bool {
        name.is_in_modules(&self.translated.crate_name, &self.options.opaque_mods)
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
                    OrdRustId::Type(_) => {
                        AnyTransId::Type(self.translated.type_decls.reserve_slot())
                    }
                    OrdRustId::TraitDecl(_) => {
                        AnyTransId::TraitDecl(self.translated.trait_decls.reserve_slot())
                    }
                    OrdRustId::TraitImpl(_) => {
                        AnyTransId::TraitImpl(self.translated.trait_impls.reserve_slot())
                    }
                    OrdRustId::Global(_) => {
                        AnyTransId::Global(self.translated.global_decls.reserve_slot())
                    }
                    OrdRustId::ConstFun(_) | OrdRustId::Fun(_) => {
                        AnyTransId::Fun(self.translated.fun_decls.reserve_slot())
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
        let hax_state = hax::State::new_from_state_and_id(&t_ctx.hax_state, def_id);
        BodyTransCtx {
            def_id,
            t_ctx,
            hax_state,
            region_vars: [Vector::new()].into(),
            free_region_vars: std::collections::BTreeMap::new(),
            bound_region_vars: Default::default(),
            type_vars: Vector::new(),
            type_vars_map: MapGenerator::new(),
            vars: Vector::new(),
            vars_map: MapGenerator::new(),
            const_generic_vars: Vector::new(),
            const_generic_vars_map: MapGenerator::new(),
            clause_translation_context: Default::default(),
            trait_clauses: Default::default(),
            regions_outlive: Vec::new(),
            types_outlive: Vec::new(),
            trait_type_constraints: Vec::new(),
            blocks: Default::default(),
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
        let var_ids: Box<[RegionId]> = names
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
        let var_ids: Box<[RegionId]> = names
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
            regions_outlive: self.regions_outlive.clone(),
            types_outlive: self.types_outlive.clone(),
            trait_type_constraints: self.trait_type_constraints.clone(),
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
            ..Default::default()
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

impl<'tcx, 'ctx> fmt::Display for TranslateCtx<'tcx, 'ctx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.translated.fmt(f)
    }
}

impl fmt::Display for TranslatedCrate {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let fmt: FmtCtx = self.into_fmt();
        match &self.ordered_decls {
            None => {
                // We do simple: types, globals, traits, functions
                for d in &self.type_decls {
                    writeln!(f, "{}\n", fmt.format_object(d))?
                }
                for d in &self.global_decls {
                    writeln!(f, "{}\n", fmt.format_object(d))?
                }
                for d in &self.trait_decls {
                    writeln!(f, "{}\n", fmt.format_object(d))?
                }
                for d in &self.trait_impls {
                    writeln!(f, "{}\n", fmt.format_object(d))?
                }
                for d in &self.fun_decls {
                    writeln!(f, "{}\n", fmt.format_object(d))?
                }
            }
            Some(ordered_decls) => {
                for gr in ordered_decls {
                    for id in gr.get_ids() {
                        writeln!(f, "{}\n", fmt.format_decl_id(id))?
                    }
                }
            }
        }
        fmt::Result::Ok(())
    }
}
