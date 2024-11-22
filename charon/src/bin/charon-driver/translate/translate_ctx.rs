//! The translation contexts.
use super::translate_types::translate_bound_region_kind_name;
use charon_lib::ast::*;
use charon_lib::common::hash_by_addr::HashByAddr;
use charon_lib::formatter::{FmtCtx, IntoFormatter};
use charon_lib::ids::{MapGenerator, Vector};
use charon_lib::name_matcher::NamePattern;
use charon_lib::options::CliOpts;
use charon_lib::ullbc_ast as ast;
use hax_frontend_exporter::SInto;
use hax_frontend_exporter::{self as hax, DefPathItem};
use itertools::Itertools;
use macros::VariantIndexArity;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use std::borrow::Cow;
use std::cmp::Ord;
use std::collections::HashMap;
use std::collections::{BTreeMap, VecDeque};
use std::fmt;
use std::fmt::Debug;
use std::mem;
use std::path::{Component, PathBuf};
use std::sync::Arc;

// Re-export to avoid having to fix imports.
pub(crate) use charon_lib::errors::{
    error_assert, error_or_panic, register_error_or_panic, DepSource, ErrorCtx,
};

/// TODO: maybe we should always target MIR Built, this would make things
/// simpler. In particular, the MIR optimized is very low level and
/// reveals too many types and data-structures that we don't want to manipulate.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum MirLevel {
    /// Original MIR, directly translated from HIR.
    Built,
    /// Not sure what this is. Not well tested.
    Promoted,
    /// MIR after optimization passes. The last one before codegen.
    Optimized,
}

/// The options that control translation.
pub struct TranslateOptions {
    /// The level at which to extract the MIR
    pub mir_level: MirLevel,
    /// List of patterns to assign a given opacity to. For each name, the most specific pattern that
    /// matches determines the opacity of the item. When no options are provided this is initialized
    /// to treat items in the crate as transparent and items in other crates as foreign.
    pub item_opacities: Vec<(NamePattern, ItemOpacity)>,
}

impl TranslateOptions {
    pub(crate) fn new(error_ctx: &mut ErrorCtx<'_>, options: &CliOpts) -> Self {
        let mut parse_pattern = |s: &str| match NamePattern::parse(s) {
            Ok(p) => Ok(p),
            Err(e) => {
                let msg = format!("failed to parse pattern `{s}` ({e})");
                error_or_panic!(error_ctx, Span::dummy(), msg)
            }
        };

        let mir_level = if options.mir_optimized {
            MirLevel::Optimized
        } else if options.mir_promoted {
            MirLevel::Promoted
        } else {
            MirLevel::Built
        };

        let item_opacities = {
            use ItemOpacity::*;
            let mut opacities = vec![];

            // This is how to treat items that don't match any other pattern.
            if options.extract_opaque_bodies {
                opacities.push(("_".to_string(), Transparent));
            } else {
                opacities.push(("_".to_string(), Foreign));
            }

            // We always include the items from the crate.
            opacities.push(("crate".to_owned(), Transparent));

            for pat in options.include.iter() {
                opacities.push((pat.to_string(), Transparent));
            }
            for pat in options.opaque.iter() {
                opacities.push((pat.to_string(), Opaque));
            }
            for pat in options.exclude.iter() {
                opacities.push((pat.to_string(), Invisible));
            }

            // We always hide this trait.
            opacities.push((format!("core::alloc::Allocator"), Invisible));
            opacities.push((
                format!("alloc::alloc::{{impl core::alloc::Allocator for _}}"),
                Invisible,
            ));

            opacities
                .into_iter()
                .filter_map(|(s, opacity)| parse_pattern(&s).ok().map(|pat| (pat, opacity)))
                .collect()
        };

        TranslateOptions {
            mir_level,
            item_opacities,
        }
    }
}

/// The id of an untranslated item. Note that a given `DefId` may show up as multiple different
/// item sources, e.g. a constant will have both a `Global` version (for the constant itself) and a
/// `FunDecl` one (for its initializer function).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, VariantIndexArity)]
pub enum TransItemSource {
    Global(DefId),
    TraitDecl(DefId),
    TraitImpl(DefId),
    Fun(DefId),
    Type(DefId),
}

impl TransItemSource {
    pub(crate) fn to_def_id(&self) -> DefId {
        match self {
            TransItemSource::Global(id)
            | TransItemSource::TraitDecl(id)
            | TransItemSource::TraitImpl(id)
            | TransItemSource::Fun(id)
            | TransItemSource::Type(id) => *id,
        }
    }
}

impl TransItemSource {
    /// Value with which we order values.
    fn sort_key(&self) -> impl Ord {
        let (variant_index, _) = self.variant_index_arity();
        let def_id = self.to_def_id();
        (def_id.krate, def_id.index, variant_index)
    }
}

/// Manual impls because `DefId` is not orderable.
impl PartialOrd for TransItemSource {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for TransItemSource {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.sort_key().cmp(&other.sort_key())
    }
}

/// Translation context used while translating the crate data into our representation.
pub struct TranslateCtx<'tcx, 'ctx> {
    /// The Rust compiler type context
    pub tcx: TyCtxt<'tcx>,
    /// Path to the toolchain root.
    pub sysroot: PathBuf,
    /// The Hax context
    pub hax_state: hax::StateWithBase<'tcx>,

    /// The options that control translation.
    pub options: TranslateOptions,
    /// The translated data.
    pub translated: TranslatedCrate,

    /// The map from rustc id to translated id.
    pub id_map: HashMap<TransItemSource, AnyTransId>,
    /// The reverse map of ids.
    pub reverse_id_map: HashMap<AnyTransId, TransItemSource>,
    /// The reverse filename map.
    pub file_to_id: HashMap<FileName, FileId>,

    /// Context for tracking and reporting errors.
    pub errors: ErrorCtx<'ctx>,
    /// The declarations we came accross and which we haven't translated yet. We keep them sorted
    /// to make the output order a bit more stable.
    pub items_to_translate: BTreeMap<TransItemSource, AnyTransId>,
    /// Stack of the translations currently happening. Used to avoid cycles where items need to
    /// translate themselves transitively.
    // FIXME: we don't use recursive item translation anywhere.
    pub translate_stack: Vec<AnyTransId>,
    /// Cache the names to compute them only once each.
    pub cached_names: HashMap<DefId, Name>,
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
    /// TODO: this duplicates the field of [ErrorCtx]
    pub def_id: DefId,
    /// The id of the definition we are currently extracting, if there is one.
    pub item_id: Option<AnyTransId>,
    /// The translation context containing the top-level definitions/ids.
    pub t_ctx: &'ctx mut TranslateCtx<'tcx, 'ctx1>,
    /// A hax state with an owner id
    pub hax_state: hax::StateWithOwner<'tcx>,
    /// Whether to consider a `ImplExprAtom::Error` as an error for us. True except inside type
    /// aliases, because rust does not enforce correct trait bounds on type aliases.
    pub error_on_impl_expr_error: bool,

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
    /// The generic parameters for the item. `regions` must be empty, as regions are handled
    /// separately.
    pub generic_params: GenericParams,
    /// The map from rust type variable indices to translated type variable indices.
    pub type_vars_map: HashMap<u32, TypeVarId>,
    /// The map from rust const generic variables to translate const generic
    /// variable indices.
    pub const_generic_vars_map: HashMap<u32, ConstGenericVarId>,
    /// (For traits only) accumulated implied trait clauses.
    pub parent_trait_clauses: Vector<TraitClauseId, TraitClause>,
    /// (For traits only) accumulated trait clauses on associated types.
    pub item_trait_clauses: HashMap<TraitItemName, Vector<TraitClauseId, TraitClause>>,

    /// Cache the translation of types. This harnesses the deduplication of `TyKind` that hax does.
    pub type_trans_cache: HashMap<HashByAddr<Arc<hax::TyKind>>, Ty>,

    /// The (regular) variables in the current function body.
    pub locals: Locals,
    /// The map from rust variable indices to translated variables indices.
    pub vars_map: HashMap<usize, VarId>,
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

/// Translates `T` into `U` using `hax`'s `SInto` trait, catching any hax panics.
pub fn catch_sinto<S, T, U>(s: &S, err: &mut ErrorCtx, span: Span, x: &T) -> Result<U, Error>
where
    T: Debug + SInto<S, U>,
{
    let unwind_safe_s = std::panic::AssertUnwindSafe(s);
    let unwind_safe_x = std::panic::AssertUnwindSafe(x);
    std::panic::catch_unwind(move || unwind_safe_x.sinto(*unwind_safe_s))
        .or_else(|_| error_or_panic!(err, span, format!("Hax panicked when translating `{x:?}`.")))
}

impl<'tcx, 'ctx> TranslateCtx<'tcx, 'ctx> {
    pub fn continue_on_failure(&self) -> bool {
        self.errors.continue_on_failure()
    }

    /// Span an error and register the error.
    pub fn span_err(&mut self, span: Span, msg: &str) {
        self.errors.span_err(span, msg)
    }

    /// Register a file if it is a "real" file and was not already registered
    /// `span` must be a span from which we obtained that filename.
    fn register_file(&mut self, filename: FileName, span: rustc_span::Span) -> FileId {
        // Lookup the file if it was already registered
        match self.file_to_id.get(&filename) {
            Some(id) => *id,
            None => {
                let source_file = self.tcx.sess.source_map().lookup_source_file(span.lo());
                let file = File {
                    name: filename.clone(),
                    contents: source_file.src.as_deref().cloned(),
                };
                let id = self.translated.files.push(file);
                self.file_to_id.insert(filename, id);
                id
            }
        }
    }

    fn path_elem_for_def(
        &mut self,
        span: Span,
        def: &hax::DefId,
    ) -> Result<Option<PathElem>, Error> {
        let path_elem = def.path_item();
        // Disambiguator disambiguates identically-named (but distinct) identifiers. This happens
        // notably with macros and inherent impl blocks.
        let disambiguator = Disambiguator::new(path_elem.disambiguator as usize);
        // Match over the key data
        let path_elem = match path_elem.data {
            DefPathItem::CrateRoot { name, .. } => {
                // Sanity check
                error_assert!(self, span, path_elem.disambiguator == 0);
                Some(PathElem::Ident(name.clone(), disambiguator))
            }
            // We map the three namespaces onto a single one. We can always disambiguate by looking
            // at the definition.
            DefPathItem::TypeNs(symbol)
            | DefPathItem::ValueNs(symbol)
            | DefPathItem::MacroNs(symbol) => Some(PathElem::Ident(symbol, disambiguator)),
            DefPathItem::Impl => {
                let def_id = def.to_rust_def_id();
                let full_def = self.hax_def(def_id)?;
                // Two cases, depending on whether the impl block is
                // a "regular" impl block (`impl Foo { ... }`) or a trait
                // implementation (`impl Bar for Foo { ... }`).
                let impl_elem = match full_def.kind() {
                    // Inherent impl ("regular" impl)
                    hax::FullDefKind::InherentImpl { ty, .. } => {
                        // We need to convert the type, which may contain quantified
                        // substs and bounds. In order to properly do so, we introduce
                        // a body translation context.
                        let mut bt_ctx = BodyTransCtx::new(def_id, None, self);
                        let generics = bt_ctx.translate_def_generics(span, &full_def)?;
                        let ty = bt_ctx.translate_ty(span, &ty)?;
                        ImplElem::Ty(generics, ty)
                    }
                    // Trait implementation
                    hax::FullDefKind::TraitImpl { .. } => {
                        let impl_id = self.register_trait_impl_id(&None, def_id);
                        ImplElem::Trait(impl_id)
                    }
                    _ => unreachable!(),
                };

                Some(PathElem::Impl(impl_elem, disambiguator))
            }
            // TODO: do nothing for now
            DefPathItem::OpaqueTy => None,
            // TODO: this is not very satisfactory, but on the other hand
            // we should be able to extract closures in local let-bindings
            // (i.e., we shouldn't have to introduce top-level let-bindings).
            DefPathItem::Closure => Some(PathElem::Ident("closure".to_string(), disambiguator)),
            // Do nothing, functions in `extern` blocks are in the same namespace as the
            // block.
            DefPathItem::ForeignMod => None,
            // Do nothing, the constructor of a struct/variant has the same name as the
            // struct/variant.
            DefPathItem::Ctor => None,
            DefPathItem::Use => Some(PathElem::Ident("<use>".to_string(), disambiguator)),
            _ => {
                let def_id = def.to_rust_def_id();
                error_or_panic!(
                    self,
                    span,
                    format!("Unexpected DefPathItem for `{def_id:?}`: {path_elem:?}")
                );
            }
        };
        Ok(path_elem)
    }

    /// Retrieve an item name from a [DefId].
    /// We lookup the path associated to an id, and convert it to a name.
    /// Paths very precisely identify where an item is. There are important
    /// subcases, like the items in an `Impl` block:
    /// ```ignore
    /// impl<T> List<T> {
    ///   fn new() ...
    /// }
    /// ```
    ///
    /// One issue here is that "List" *doesn't appear* in the path, which would
    /// look like the following:
    ///
    ///   `TypeNS("Crate") :: Impl :: ValueNs("new")`
    ///                       ^^^
    ///           This is where "List" should be
    ///
    /// For this reason, whenever we find an `Impl` path element, we actually
    /// lookup the type of the sub-path, from which we can derive a name.
    ///
    /// Besides, as there may be several "impl" blocks for one type, each impl
    /// block is identified by a unique number (rustc calls this a
    /// "disambiguator"), which we grab.
    ///
    /// Example:
    /// ========
    /// For instance, if we write the following code in crate `test` and module
    /// `bla`:
    /// ```ignore
    /// impl<T> Foo<T> {
    ///   fn foo() { ... }
    /// }
    ///
    /// impl<T> Foo<T> {
    ///   fn bar() { ... }
    /// }
    /// ```
    ///
    /// The names we will generate for `foo` and `bar` are:
    /// `[Ident("test"), Ident("bla"), Ident("Foo"), Impl(impl<T> Ty<T>, Disambiguator(0)), Ident("foo")]`
    /// `[Ident("test"), Ident("bla"), Ident("Foo"), Impl(impl<T> Ty<T>, Disambiguator(1)), Ident("bar")]`
    pub fn hax_def_id_to_name(&mut self, def: &hax::DefId) -> Result<Name, Error> {
        let def_id = def.to_rust_def_id();
        if let Some(name) = self.cached_names.get(&def_id) {
            return Ok(name.clone());
        }
        trace!("Computing name for `{def_id:?}`");

        let parent_name = if let Some(parent) = &def.parent {
            self.hax_def_id_to_name(parent)?
        } else {
            Name { name: Vec::new() }
        };
        let span = self.def_span(def_id);
        let mut name = parent_name;
        if let Some(path_elem) = self.path_elem_for_def(span, &def)? {
            name.name.push(path_elem);
        }

        trace!("Computed name for `{def_id:?}`: `{name:?}`");
        self.cached_names.insert(def_id, name.clone());
        Ok(name)
    }

    pub fn def_id_to_name(&mut self, def_id: DefId) -> Result<Name, Error> {
        self.hax_def_id_to_name(&def_id.sinto(&self.hax_state))
    }

    /// Translates `T` into `U` using `hax`'s `SInto` trait, catching any hax panics.
    pub fn catch_sinto<S, T, U>(&mut self, s: &S, span: Span, x: &T) -> Result<U, Error>
    where
        T: Debug + SInto<S, U>,
    {
        catch_sinto(s, &mut self.errors, span, x)
    }

    pub fn hax_def(&mut self, def_id: impl Into<DefId>) -> Result<Arc<hax::FullDef>, Error> {
        let def_id: DefId = def_id.into();
        let span = self.def_span(def_id);
        // Hax takes care of caching the translation.
        catch_sinto(&self.hax_state, &mut self.errors, span, &def_id)
    }

    pub(crate) fn translate_attr_info(&mut self, def: &hax::FullDef) -> AttrInfo {
        // Default to `false` for impl blocks and closures.
        let public = def.visibility.unwrap_or(false);
        let inline = self.translate_inline(def);
        let attributes = def
            .attributes
            .iter()
            .filter_map(|attr| self.translate_attribute(&attr))
            .collect_vec();

        let rename = {
            let mut renames = attributes.iter().filter_map(|a| a.as_rename()).cloned();
            let rename = renames.next();
            if renames.next().is_some() {
                let span = self.translate_span_from_hax(&def.span);
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
            inline,
            public,
            rename,
        }
    }

    /// Compute the meta information for a Rust item.
    pub(crate) fn translate_item_meta(
        &mut self,
        def: &hax::FullDef,
        name: Name,
        opacity: ItemOpacity,
    ) -> ItemMeta {
        let span = def.source_span.as_ref().unwrap_or(&def.span);
        let span = self.translate_span_from_hax(span);
        let attr_info = self.translate_attr_info(def);
        let is_local = def.def_id.is_local;

        let opacity = if self.is_extern_item(def)
            || attr_info.attributes.iter().any(|attr| attr.is_opaque())
        {
            // Force opaque in these cases.
            ItemOpacity::Opaque.max(opacity)
        } else {
            opacity
        };

        ItemMeta {
            name,
            span,
            source_text: def.source_text.clone(),
            attr_info,
            is_local,
            opacity,
        }
    }

    pub fn translate_filename(&mut self, name: &hax::FileName) -> meta::FileName {
        match name {
            hax::FileName::Real(name) => {
                use hax::RealFileName;
                match name {
                    RealFileName::LocalPath(path) => {
                        let path = if let Ok(path) = path.strip_prefix(&self.sysroot) {
                            // The path to files in the standard library may be full paths to somewhere
                            // in the sysroot. This may depend on how the toolchain is installed
                            // (rustup vs nix), so we normalize the paths here to avoid
                            // inconsistencies in the translation.
                            if let Ok(path) = path.strip_prefix("lib/rustlib/src/rust") {
                                let mut rewritten_path: PathBuf = "/rustc".into();
                                rewritten_path.extend(path);
                                rewritten_path
                            } else {
                                // Unclear if this can happen, but just in case.
                                let mut rewritten_path: PathBuf = "/toolchain".into();
                                rewritten_path.extend(path);
                                rewritten_path
                            }
                        } else {
                            path.clone()
                        };
                        FileName::Local(path)
                    }
                    RealFileName::Remapped { virtual_name, .. } => {
                        // We use the virtual name because it is always available.
                        // That name normally starts with `/rustc/<hash>/`. For our purposes we hide
                        // the hash.
                        let mut components_iter = virtual_name.components();
                        if let Some(
                            [Component::RootDir, Component::Normal(rustc), Component::Normal(hash)],
                        ) = components_iter.by_ref().array_chunks().next()
                            && rustc.to_str() == Some("rustc")
                            && hash.len() == 40
                        {
                            let path_without_hash = [Component::RootDir, Component::Normal(rustc)]
                                .into_iter()
                                .chain(components_iter)
                                .collect();
                            FileName::Virtual(path_without_hash)
                        } else {
                            FileName::Virtual(virtual_name.clone())
                        }
                    }
                }
            }
            hax::FileName::QuoteExpansion(_)
            | hax::FileName::Anon(_)
            | hax::FileName::MacroExpansion(_)
            | hax::FileName::ProcMacroSourceCode(_)
            | hax::FileName::CliCrateAttr(_)
            | hax::FileName::Custom(_)
            | hax::FileName::DocTest(..)
            | hax::FileName::InlineAsm(_) => {
                // We use the debug formatter to generate a filename.
                // This is not ideal, but filenames are for debugging anyway.
                FileName::NotReal(format!("{name:?}"))
            }
        }
    }

    pub fn translate_raw_span(&mut self, rspan: &hax::Span) -> meta::RawSpan {
        let filename = self.translate_filename(&rspan.filename);
        let rust_span_data = rspan.rust_span_data.unwrap();
        let file_id = match &filename {
            FileName::NotReal(_) => {
                // For now we forbid not real filenames
                unimplemented!();
            }
            FileName::Virtual(_) | FileName::Local(_) => {
                self.register_file(filename, rust_span_data.span())
            }
        };

        fn convert_loc(loc: &hax::Loc) -> Loc {
            Loc {
                line: loc.line,
                col: loc.col,
            }
        }
        let beg = convert_loc(&rspan.lo);
        let end = convert_loc(&rspan.hi);

        // Put together
        meta::RawSpan {
            file_id,
            beg,
            end,
            rust_span_data,
        }
    }

    /// Compute span data from a Rust source scope
    pub fn translate_span_from_source_info(
        &mut self,
        source_scopes: &hax::IndexVec<hax::SourceScope, hax::SourceScopeData>,
        source_info: &hax::SourceInfo,
    ) -> Span {
        // Translate the span
        let span = self.translate_raw_span(&source_info.span);

        // Lookup the top-most inlined parent scope.
        let mut parent_span = None;
        let mut scope_data = &source_scopes[source_info.scope];
        while let Some(parent_scope) = scope_data.inlined_parent_scope {
            scope_data = &source_scopes[parent_scope];
            parent_span = Some(&scope_data.span);
        }

        if let Some(parent_span) = parent_span {
            let parent_span = self.translate_raw_span(parent_span);
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

    pub(crate) fn translate_span_from_hax(&mut self, span: &hax::Span) -> Span {
        Span {
            span: self.translate_raw_span(span),
            generated_from_span: None,
        }
    }

    pub(crate) fn def_span(&mut self, def_id: impl Into<DefId>) -> Span {
        let def_id = def_id.into();
        let def_kind = hax::get_def_kind(self.tcx, def_id);
        let span = hax::get_def_span(self.tcx, def_id, def_kind);
        let span = span.sinto(&self.hax_state);
        self.translate_span_from_hax(&span)
    }

    /// Translates a rust attribute. Returns `None` if the attribute is a doc comment (rustc
    /// encodes them as attributes). For now we use `String`s for `Attributes`.
    pub(crate) fn translate_attribute(&mut self, attr: &hax::Attribute) -> Option<Attribute> {
        match &attr.kind {
            hax::AttrKind::Normal(normal_attr) => {
                let raw_attr = RawAttribute {
                    path: normal_attr.item.path.clone(),
                    args: match &normal_attr.item.args {
                        hax::AttrArgs::Empty => None,
                        hax::AttrArgs::Delimited(args) => Some(args.tokens.clone()),
                        hax::AttrArgs::Eq(_, hax::AttrArgsEq::Hir(lit)) => self
                            .tcx
                            .sess
                            .source_map()
                            .span_to_snippet(lit.span.rust_span_data.unwrap().span())
                            .ok(),
                        hax::AttrArgs::Eq(..) => None,
                    },
                };
                match Attribute::parse_from_raw(raw_attr) {
                    Ok(a) => Some(a),
                    Err(msg) => {
                        let span = self.translate_span_from_hax(&attr.span);
                        self.span_err(span, &format!("Error parsing attribute: {msg}"));
                        None
                    }
                }
            }
            hax::AttrKind::DocComment(_kind, comment) => {
                Some(Attribute::DocComment(comment.to_string()))
            }
        }
    }

    pub(crate) fn translate_inline(&self, def: &hax::FullDef) -> Option<InlineAttr> {
        match def.kind() {
            hax::FullDefKind::Fn { inline, .. } | hax::FullDefKind::AssocFn { inline, .. } => {
                match inline {
                    hax::InlineAttr::None => None,
                    hax::InlineAttr::Hint => Some(InlineAttr::Hint),
                    hax::InlineAttr::Never => Some(InlineAttr::Never),
                    hax::InlineAttr::Always => Some(InlineAttr::Always),
                }
            }
            _ => None,
        }
    }

    /// Whether this item is in an `extern { .. }` block, in which case it has no body.
    pub(crate) fn is_extern_item(&mut self, def: &hax::FullDef) -> bool {
        def.parent.as_ref().is_some_and(|parent| {
            self.hax_def(parent).is_ok_and(|parent_def| {
                matches!(parent_def.kind(), hax::FullDefKind::ForeignMod { .. })
            })
        })
    }

    pub(crate) fn opacity_for_name(&self, name: &Name) -> ItemOpacity {
        // Find the most precise pattern that matches this name. There is always one since
        // the list contains the `_` pattern. If there are conflicting settings for this item, we
        // err on the side of being more opaque.
        let (_, opacity) = self
            .options
            .item_opacities
            .iter()
            .filter(|(pat, _)| pat.matches(&self.translated, name))
            .max()
            .unwrap();
        *opacity
    }

    /// Register the fact that `id` is a dependency of `src` (if `src` is not `None`).
    pub(crate) fn register_dep_source(
        &mut self,
        src: &Option<DepSource>,
        def_id: DefId,
        item_id: AnyTransId,
    ) {
        if let Some(src) = src {
            if src.src_id != item_id && !def_id.is_local() {
                self.errors
                    .external_dep_sources
                    .entry(item_id)
                    .or_default()
                    .insert(*src);
            }
        }
    }

    pub(crate) fn register_id(
        &mut self,
        src: &Option<DepSource>,
        id: TransItemSource,
    ) -> AnyTransId {
        let item_id = match self.id_map.get(&id) {
            Some(tid) => *tid,
            None => {
                let trans_id = match id {
                    TransItemSource::Type(_) => {
                        AnyTransId::Type(self.translated.type_decls.reserve_slot())
                    }
                    TransItemSource::TraitDecl(_) => {
                        AnyTransId::TraitDecl(self.translated.trait_decls.reserve_slot())
                    }
                    TransItemSource::TraitImpl(_) => {
                        AnyTransId::TraitImpl(self.translated.trait_impls.reserve_slot())
                    }
                    TransItemSource::Global(_) => {
                        AnyTransId::Global(self.translated.global_decls.reserve_slot())
                    }
                    TransItemSource::Fun(_) => {
                        AnyTransId::Fun(self.translated.fun_decls.reserve_slot())
                    }
                };
                // Add the id to the queue of declarations to translate
                self.items_to_translate.insert(id, trans_id);
                self.id_map.insert(id, trans_id);
                self.reverse_id_map.insert(trans_id, id);
                self.translated.all_ids.insert(trans_id);
                // Store the name early so the name matcher can identify paths. We can't to it for
                // trait impls because they register themselves when computing their name.
                if !matches!(id, TransItemSource::TraitImpl(_)) {
                    if let Ok(name) = self.def_id_to_name(id.to_def_id()) {
                        self.translated.item_names.insert(trans_id, name);
                    }
                }
                trans_id
            }
        };
        self.register_dep_source(src, id.to_def_id(), item_id);
        item_id
    }

    pub(crate) fn register_type_decl_id(
        &mut self,
        src: &Option<DepSource>,
        id: impl Into<DefId>,
    ) -> TypeDeclId {
        *self
            .register_id(src, TransItemSource::Type(id.into()))
            .as_type()
            .unwrap()
    }

    pub(crate) fn register_fun_decl_id(
        &mut self,
        src: &Option<DepSource>,
        id: impl Into<DefId>,
    ) -> FunDeclId {
        *self
            .register_id(src, TransItemSource::Fun(id.into()))
            .as_fun()
            .unwrap()
    }

    pub(crate) fn register_trait_decl_id(
        &mut self,
        src: &Option<DepSource>,
        id: impl Into<DefId>,
    ) -> TraitDeclId {
        *self
            .register_id(src, TransItemSource::TraitDecl(id.into()))
            .as_trait_decl()
            .unwrap()
    }

    pub(crate) fn register_trait_impl_id(
        &mut self,
        src: &Option<DepSource>,
        id: impl Into<DefId>,
    ) -> TraitImplId {
        let id = id.into();
        // Register the corresponding trait early so we can filter on its name.
        {
            let def = self.hax_def(id).expect("hax failed when translating item");
            let hax::FullDefKind::TraitImpl { trait_pred, .. } = def.kind() else {
                unreachable!()
            };
            let trait_rust_id = &trait_pred.trait_ref.def_id;
            let _ = self.register_trait_decl_id(src, trait_rust_id);
        }

        *self
            .register_id(src, TransItemSource::TraitImpl(id))
            .as_trait_impl()
            .unwrap()
    }

    pub(crate) fn register_global_decl_id(
        &mut self,
        src: &Option<DepSource>,
        id: impl Into<DefId>,
    ) -> GlobalDeclId {
        *self
            .register_id(src, TransItemSource::Global(id.into()))
            .as_global()
            .unwrap()
    }

    pub(crate) fn with_def_id<F, T>(&mut self, def_id: DefId, item_id: AnyTransId, f: F) -> T
    where
        F: FnOnce(&mut Self) -> T,
    {
        let current_def_id = self.errors.def_id;
        let current_def_id_is_local = self.errors.def_id_is_local;
        self.errors.def_id = Some(item_id);
        self.errors.def_id_is_local = def_id.is_local();
        let ret = f(self);
        self.errors.def_id = current_def_id;
        self.errors.def_id_is_local = current_def_id_is_local;
        ret
    }
}

impl<'tcx, 'ctx, 'ctx1> BodyTransCtx<'tcx, 'ctx, 'ctx1> {
    /// Create a new `ExecContext`.
    pub(crate) fn new(
        def_id: DefId,
        item_id: Option<AnyTransId>,
        t_ctx: &'ctx mut TranslateCtx<'tcx, 'ctx1>,
    ) -> Self {
        let hax_state = hax::State::new_from_state_and_id(&t_ctx.hax_state, def_id);
        BodyTransCtx {
            def_id,
            item_id,
            t_ctx,
            hax_state,
            error_on_impl_expr_error: true,
            region_vars: [Vector::new()].into(),
            free_region_vars: Default::default(),
            bound_region_vars: Default::default(),
            generic_params: Default::default(),
            type_vars_map: Default::default(),
            const_generic_vars_map: Default::default(),
            parent_trait_clauses: Default::default(),
            item_trait_clauses: Default::default(),
            type_trans_cache: Default::default(),
            locals: Default::default(),
            vars_map: Default::default(),
            blocks: Default::default(),
            blocks_map: Default::default(),
            blocks_stack: Default::default(),
        }
    }

    pub fn continue_on_failure(&self) -> bool {
        self.t_ctx.continue_on_failure()
    }

    pub fn span_err(&mut self, span: Span, msg: &str) {
        self.t_ctx.span_err(span, msg)
    }

    pub(crate) fn translate_span_from_hax(&mut self, rspan: &hax::Span) -> Span {
        self.t_ctx.translate_span_from_hax(rspan)
    }

    pub(crate) fn def_span(&mut self, def_id: impl Into<DefId>) -> Span {
        self.t_ctx.def_span(def_id)
    }

    pub(crate) fn translate_local(&self, local: &hax::Local) -> Option<VarId> {
        use rustc_index::Idx;
        self.vars_map.get(&local.index()).copied()
    }

    #[allow(dead_code)]
    pub(crate) fn get_block_id_from_rid(&self, rid: hax::BasicBlock) -> Option<ast::BlockId> {
        self.blocks_map.get(&rid)
    }

    pub(crate) fn register_type_decl_id(&mut self, span: Span, id: impl Into<DefId>) -> TypeDeclId {
        let src = self.make_dep_source(span);
        self.t_ctx.register_type_decl_id(&src, id)
    }

    pub(crate) fn register_fun_decl_id(&mut self, span: Span, id: impl Into<DefId>) -> FunDeclId {
        let src = self.make_dep_source(span);
        self.t_ctx.register_fun_decl_id(&src, id)
    }

    pub(crate) fn register_global_decl_id(
        &mut self,
        span: Span,
        id: impl Into<DefId>,
    ) -> GlobalDeclId {
        let src = self.make_dep_source(span);
        self.t_ctx.register_global_decl_id(&src, id)
    }

    /// Returns an [Option] because we may ignore some builtin or auto traits
    /// like [core::marker::Sized] or [core::marker::Sync].
    pub(crate) fn register_trait_decl_id(
        &mut self,
        span: Span,
        id: impl Into<DefId>,
    ) -> TraitDeclId {
        let src = self.make_dep_source(span);
        self.t_ctx.register_trait_decl_id(&src, id)
    }

    /// Returns an [Option] because we may ignore some builtin or auto traits
    /// like [core::marker::Sized] or [core::marker::Sync].
    pub(crate) fn register_trait_impl_id(
        &mut self,
        span: Span,
        id: impl Into<DefId>,
    ) -> TraitImplId {
        let src = self.make_dep_source(span);
        self.t_ctx.register_trait_impl_id(&src, id)
    }

    /// Push a free region.
    ///
    /// Important: we must push *all* the free regions (which are early-bound
    /// regions) before pushing any (late-)bound region.
    pub(crate) fn push_free_region(&mut self, r: hax::Region) -> RegionId {
        let name = super::translate_types::translate_region_name(&r);
        // Check that there are no late-bound regions
        assert!(self.bound_region_vars.is_empty());
        let rid = self.region_vars[0].push_with(|index| RegionVar { index, name });
        self.free_region_vars.insert(r, rid);
        rid
    }

    /// Translate a binder of regions by appending the stored reguions to the given vector.
    pub(crate) fn translate_region_binder(
        &mut self,
        span: Span,
        binder: hax::Binder<()>,
        region_vars: &mut Vector<RegionId, RegionVar>,
    ) -> Result<Box<[RegionId]>, Error> {
        use hax::BoundVariableKind::*;
        binder
            .bound_vars
            .into_iter()
            .map(|p| match p {
                Region(region) => {
                    let name = translate_bound_region_kind_name(&region);
                    let id = region_vars.push_with(|index| RegionVar { index, name });
                    Ok(id)
                }
                Ty(_) => {
                    error_or_panic!(self, span, "Unexpected locally bound type variable");
                }
                Const => {
                    error_or_panic!(
                        self,
                        span,
                        "Unexpected locally bound const generic variable"
                    );
                }
            })
            .try_collect()
    }

    /// Set the first bound regions group
    pub(crate) fn set_first_bound_regions_group(
        &mut self,
        span: Span,
        binder: hax::Binder<()>,
    ) -> Result<(), Error> {
        assert!(self.bound_region_vars.is_empty());
        assert_eq!(self.region_vars.len(), 1);

        // Register the variables
        // There may already be lifetimes in the current group.
        let mut region_vars = mem::take(&mut self.region_vars[0]);
        let var_ids = self.translate_region_binder(span, binder, &mut region_vars)?;
        self.region_vars[0] = region_vars;
        self.bound_region_vars.push_front(var_ids);
        // Translation of types depends on bound variables, we must not mix that up.
        self.type_trans_cache = Default::default();

        Ok(())
    }

    /// Push a group of bound regions and call the continuation.
    /// We use this when diving into a `for<'a>`, or inside an arrow type (because
    /// it contains universally quantified regions).
    pub(crate) fn with_locally_bound_regions_group<F, T>(
        &mut self,
        span: Span,
        binder: hax::Binder<()>,
        f: F,
    ) -> Result<T, Error>
    where
        F: FnOnce(&mut Self) -> Result<T, Error>,
    {
        assert!(!self.region_vars.is_empty());

        // Register the variables
        let mut bound_vars = Vector::new();
        let var_ids = self.translate_region_binder(span, binder, &mut bound_vars)?;
        self.bound_region_vars.push_front(var_ids);
        self.region_vars.push_front(bound_vars);
        // Translation of types depends on bound variables, we must not mix that up.
        let old_ty_cache = std::mem::take(&mut self.type_trans_cache);

        // Call the continuation
        let res = f(self);

        // Reset
        self.bound_region_vars.pop_front();
        self.region_vars.pop_front();
        self.type_trans_cache = old_ty_cache;

        // Return
        res
    }

    pub(crate) fn push_type_var(&mut self, rid: u32, name: String) -> TypeVarId {
        let var_id = self
            .generic_params
            .types
            .push_with(|index| TypeVar { index, name });
        self.type_vars_map.insert(rid, var_id);
        var_id
    }

    pub(crate) fn push_var(&mut self, rid: usize, ty: Ty, name: Option<String>) {
        let var_id = self.locals.vars.push_with(|index| Var { index, name, ty });
        self.vars_map.insert(rid, var_id);
    }

    pub(crate) fn push_const_generic_var(&mut self, rid: u32, ty: LiteralTy, name: String) {
        let var_id = self
            .generic_params
            .const_generics
            .push_with(|index| ConstGenericVar { index, name, ty });
        self.const_generic_vars_map.insert(rid, var_id);
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

    pub(crate) fn make_dep_source(&self, span: Span) -> Option<DepSource> {
        Some(DepSource {
            src_id: self.item_id?,
            span: self.def_id.is_local().then_some(span),
        })
    }
}

impl<'tcx, 'ctx, 'a> IntoFormatter for &'a TranslateCtx<'tcx, 'ctx> {
    type C = FmtCtx<'a>;

    fn into_fmt(self) -> Self::C {
        self.translated.into_fmt()
    }
}

impl<'tcx, 'ctx, 'ctx1, 'a> IntoFormatter for &'a BodyTransCtx<'tcx, 'ctx, 'ctx1> {
    type C = FmtCtx<'a>;

    fn into_fmt(self) -> Self::C {
        // Translate our generics into a stack of generics. Only the outermost binder has
        // non-region parameters.
        let mut generics: VecDeque<Cow<'_, GenericParams>> = self
            .region_vars
            .iter()
            .cloned()
            .map(|regions| {
                Cow::Owned(GenericParams {
                    regions,
                    ..Default::default()
                })
            })
            .collect();
        let outermost_generics = generics.back_mut().unwrap().to_mut();
        outermost_generics.types = self.generic_params.types.clone();
        outermost_generics.const_generics = self.generic_params.const_generics.clone();
        FmtCtx {
            translated: Some(&self.t_ctx.translated),
            generics,
            locals: Some(&self.locals),
        }
    }
}

impl<'tcx, 'ctx> fmt::Display for TranslateCtx<'tcx, 'ctx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.translated.fmt(f)
    }
}
