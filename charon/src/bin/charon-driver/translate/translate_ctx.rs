//! The translation contexts.
use super::translate_types::translate_bound_region_kind_name;
use charon_lib::ast::*;
use charon_lib::common::hash_by_addr::HashByAddr;
use charon_lib::formatter::{FmtCtx, IntoFormatter};
use charon_lib::ids::Vector;
use charon_lib::options::TranslateOptions;
use hax_frontend_exporter::SInto;
use hax_frontend_exporter::{self as hax, DefPathItem};
use itertools::Itertools;
use macros::VariantIndexArity;
use rustc_middle::ty::TyCtxt;
use std::borrow::Cow;
use std::cell::RefCell;
use std::cmp::Ord;
use std::collections::{BTreeSet, HashMap, HashSet};
use std::fmt::Debug;
use std::path::{Component, PathBuf};
use std::sync::Arc;
use std::{fmt, mem};

// Re-export to avoid having to fix imports.
pub(crate) use charon_lib::errors::{
    error_assert, raise_error, register_error, DepSource, ErrorCtx, Level,
};

/// The id of an untranslated item. Note that a given `DefId` may show up as multiple different
/// item sources, e.g. a constant will have both a `Global` version (for the constant itself) and a
/// `FunDecl` one (for its initializer function).
#[derive(Clone, Debug, PartialEq, Eq, Hash, VariantIndexArity)]
pub enum TransItemSource {
    Global(hax::DefId),
    TraitDecl(hax::DefId),
    TraitImpl(hax::DefId),
    Fun(hax::DefId),
    Type(hax::DefId),
}

impl TransItemSource {
    pub(crate) fn as_def_id(&self) -> &hax::DefId {
        match self {
            TransItemSource::Global(id)
            | TransItemSource::TraitDecl(id)
            | TransItemSource::TraitImpl(id)
            | TransItemSource::Fun(id)
            | TransItemSource::Type(id) => id,
        }
    }
}

impl TransItemSource {
    /// Value with which we order values.
    fn sort_key(&self) -> impl Ord {
        let (variant_index, _) = self.variant_index_arity();
        let def_id = self.as_def_id();
        (def_id.index, variant_index)
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
pub struct TranslateCtx<'tcx> {
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
    pub errors: RefCell<ErrorCtx>,
    /// The declarations we came accross and which we haven't translated yet. We keep them sorted
    /// to make the output order a bit more stable.
    pub items_to_translate: BTreeSet<TransItemSource>,
    /// The declaration we've already processed (successfully or not).
    pub processed: HashSet<TransItemSource>,
    /// Cache the names to compute them only once each.
    pub cached_names: HashMap<hax::DefId, Name>,
    /// Cache the `ItemMeta`s to compute them only once each.
    pub cached_item_metas: HashMap<hax::DefId, ItemMeta>,
}

/// A level of binding for type-level variables. Each item has a top-level binding level
/// corresponding to the parameters and clauses to the items. We may then encounter inner binding
/// levels in the following cases:
/// - `for<..>` binders in predicates;
/// - `fn<..>` function pointer types;
/// - `dyn Trait` types, represented as `dyn<T: Trait>` (TODO);
/// - types in a trait declaration or implementation block (TODO);
/// - methods in a trait declaration or implementation block (TODO).
///
/// At each level, we store two things: a `GenericParams` that contains the parameters bound at
/// this level, and various maps from the rustc-internal indices to our indices.
#[derive(Debug)]
pub(crate) struct BindingLevel {
    /// The parameters and predicates bound at this level.
    pub params: GenericParams,
    /// Whether this binder corresponds to an item (method, type) or not (`for<..>` predicate, `fn`
    /// pointer, etc). This indicates whether it corresponds to a rustc `ParamEnv` and therefore
    /// whether we should resolve rustc variables there.
    pub is_item_binder: bool,
    /// Rust makes the distinction between early and late-bound region parameters. We do not make
    /// this distinction, and merge early and late bound regions. For details, see:
    /// https://smallcultfollowing.com/babysteps/blog/2013/10/29/intermingled-parameter-lists/
    /// https://smallcultfollowing.com/babysteps/blog/2013/11/04/intermingled-parameter-lists/
    ///
    /// The map from rust early regions to translated region indices.
    pub early_region_vars: std::collections::BTreeMap<hax::EarlyParamRegion, RegionId>,
    /// The map from rust late/bound regions to translated region indices.
    pub bound_region_vars: Vec<RegionId>,
    /// The map from rust type variable indices to translated type variable indices.
    pub type_vars_map: HashMap<u32, TypeVarId>,
    /// The map from rust const generic variables to translate const generic variable indices.
    pub const_generic_vars_map: HashMap<u32, ConstGenericVarId>,
    /// Cache the translation of types. This harnesses the deduplication of `TyKind` that hax does.
    pub type_trans_cache: HashMap<HashByAddr<Arc<hax::TyKind>>, Ty>,
}

impl BindingLevel {
    pub(crate) fn new(is_item_binder: bool) -> Self {
        Self {
            params: Default::default(),
            is_item_binder,
            early_region_vars: Default::default(),
            bound_region_vars: Default::default(),
            type_vars_map: Default::default(),
            const_generic_vars_map: Default::default(),
            type_trans_cache: Default::default(),
        }
    }

    /// Important: we must push all the early-bound regions before pushing any other region.
    pub(crate) fn push_early_region(&mut self, region: hax::EarlyParamRegion) -> RegionId {
        let name = super::translate_types::translate_region_name(&region);
        // Check that there are no late-bound regions
        assert!(
            self.bound_region_vars.is_empty(),
            "Early regions must be tralsnated before late ones"
        );
        let rid = self
            .params
            .regions
            .push_with(|index| RegionVar { index, name });
        self.early_region_vars.insert(region, rid);
        rid
    }

    /// Important: we must push all the early-bound regions before pushing any other region.
    pub(crate) fn push_bound_region(&mut self, region: hax::BoundRegionKind) -> RegionId {
        let name = translate_bound_region_kind_name(&region);
        let rid = self
            .params
            .regions
            .push_with(|index| RegionVar { index, name });
        self.bound_region_vars.push(rid);
        rid
    }

    pub(crate) fn push_type_var(&mut self, rid: u32, name: String) -> TypeVarId {
        let var_id = self.params.types.push_with(|index| TypeVar { index, name });
        self.type_vars_map.insert(rid, var_id);
        var_id
    }

    pub(crate) fn push_const_generic_var(&mut self, rid: u32, ty: LiteralTy, name: String) {
        let var_id = self
            .params
            .const_generics
            .push_with(|index| ConstGenericVar { index, name, ty });
        self.const_generic_vars_map.insert(rid, var_id);
    }

    /// Translate a binder of regions by appending the stored reguions to the given vector.
    pub(crate) fn push_params_from_binder(&mut self, binder: hax::Binder<()>) -> Result<(), Error> {
        use hax::BoundVariableKind::*;
        for p in binder.bound_vars {
            match p {
                Region(region) => {
                    self.push_bound_region(region);
                }
                Ty(_) => {
                    panic!("Unexpected locally bound type variable");
                }
                Const => {
                    panic!("Unexpected locally bound const generic variable");
                }
            }
        }
        Ok(())
    }
}

/// A translation context for items.
/// Augments the [TranslateCtx] with type-level variables.
pub(crate) struct ItemTransCtx<'tcx, 'ctx> {
    /// The definition we are currently extracting.
    /// TODO: this duplicates the field of [ErrorCtx]
    pub def_id: hax::DefId,
    /// The id of the definition we are currently extracting, if there is one.
    pub item_id: Option<AnyTransId>,
    /// The translation context containing the top-level definitions/ids.
    pub t_ctx: &'ctx mut TranslateCtx<'tcx>,
    /// Whether to consider a `ImplExprAtom::Error` as an error for us. True except inside type
    /// aliases, because rust does not enforce correct trait bounds on type aliases.
    pub error_on_impl_expr_error: bool,

    /// The stack of generic parameter binders for the current context. Each binder introduces an
    /// entry in this stack, with the entry as index `0` being the innermost binder. These
    /// parameters are referenced using [`DeBruijnVar`]; see there for details.
    pub binding_levels: BindingStack<BindingLevel>,
    /// (For traits only) accumulated implied trait clauses.
    pub parent_trait_clauses: Vector<TraitClauseId, TraitClause>,
    /// (For traits only) accumulated trait clauses on associated types.
    pub item_trait_clauses: HashMap<TraitItemName, Vector<TraitClauseId, TraitClause>>,
}

/// Translates `T` into `U` using `hax`'s `SInto` trait, catching any hax panics.
pub fn catch_sinto<S, T, U>(
    s: &S,
    err: &mut ErrorCtx,
    krate: &TranslatedCrate,
    span: Span,
    x: &T,
) -> Result<U, Error>
where
    T: Debug + SInto<S, U>,
{
    let unwind_safe_s = std::panic::AssertUnwindSafe(s);
    let unwind_safe_x = std::panic::AssertUnwindSafe(x);
    std::panic::catch_unwind(move || unwind_safe_x.sinto(*unwind_safe_s)).or_else(|_| {
        raise_error!(
            err,
            crate(krate),
            span,
            "Hax panicked when translating `{x:?}`."
        )
    })
}

impl<'tcx, 'ctx> TranslateCtx<'tcx> {
    /// Span an error and register the error.
    pub fn span_err(&self, span: Span, msg: &str, level: Level) -> Error {
        self.errors
            .borrow_mut()
            .span_err(&self.translated, span, msg, level)
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
        def_id: &hax::DefId,
    ) -> Result<Option<PathElem>, Error> {
        let path_elem = def_id.path_item();
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
            DefPathItem::TypeNs(None) => None,
            DefPathItem::TypeNs(Some(symbol))
            | DefPathItem::ValueNs(symbol)
            | DefPathItem::MacroNs(symbol) => Some(PathElem::Ident(symbol, disambiguator)),
            DefPathItem::Impl => {
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
                        let mut bt_ctx = ItemTransCtx::new(def_id.clone(), None, self);
                        bt_ctx.translate_def_generics(span, &full_def)?;
                        let ty = bt_ctx.translate_ty(span, &ty)?;
                        ImplElem::Ty(Binder {
                            kind: BinderKind::InherentImplBlock,
                            params: bt_ctx.into_generics(),
                            skip_binder: ty,
                        })
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
            DefPathItem::Use => Some(PathElem::Ident("{use}".to_string(), disambiguator)),
            DefPathItem::AnonConst => Some(PathElem::Ident("{const}".to_string(), disambiguator)),
            DefPathItem::PromotedConst => Some(PathElem::Ident(
                "{promoted_const}".to_string(),
                disambiguator,
            )),
            _ => {
                raise_error!(
                    self,
                    span,
                    "Unexpected DefPathItem for `{def_id:?}`: {path_elem:?}"
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
    pub fn hax_def_id_to_name(&mut self, def_id: &hax::DefId) -> Result<Name, Error> {
        if let Some(name) = self.cached_names.get(&def_id) {
            return Ok(name.clone());
        }
        trace!("Computing name for `{def_id:?}`");

        let parent_name = if let Some(parent) = &def_id.parent {
            self.hax_def_id_to_name(parent)?
        } else {
            Name { name: Vec::new() }
        };
        let span = self.def_span(def_id);
        let mut name = parent_name;
        if let Some(path_elem) = self.path_elem_for_def(span, &def_id)? {
            name.name.push(path_elem);
        }

        trace!("Computed name for `{def_id:?}`: `{name:?}`");
        self.cached_names.insert(def_id.clone(), name.clone());
        Ok(name)
    }

    /// Translates `T` into `U` using `hax`'s `SInto` trait, catching any hax panics.
    pub fn catch_sinto<S, T, U>(&mut self, s: &S, span: Span, x: &T) -> Result<U, Error>
    where
        T: Debug + SInto<S, U>,
    {
        catch_sinto(s, &mut *self.errors.borrow_mut(), &self.translated, span, x)
    }

    pub fn hax_def(&mut self, def_id: &hax::DefId) -> Result<Arc<hax::FullDef>, Error> {
        let span = self.def_span(def_id);
        // Hax takes care of caching the translation.
        let unwind_safe_s = std::panic::AssertUnwindSafe(&self.hax_state);
        std::panic::catch_unwind(move || def_id.full_def(*unwind_safe_s))
            .or_else(|_| raise_error!(self, span, "Hax panicked when translating `{def_id:?}`."))
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
                register_error!(
                    self,
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
        name_opacity: ItemOpacity,
    ) -> ItemMeta {
        if let Some(item_meta) = self.cached_item_metas.get(&def.def_id) {
            return item_meta.clone();
        }
        let span = def.source_span.as_ref().unwrap_or(&def.span);
        let span = self.translate_span_from_hax(span);
        let attr_info = self.translate_attr_info(def);
        let is_local = def.def_id.is_local;
        let lang_item = def
            .lang_item
            .clone()
            .or_else(|| def.diagnostic_item.clone());

        let opacity = if self.is_extern_item(def)
            || attr_info.attributes.iter().any(|attr| attr.is_opaque())
        {
            // Force opaque in these cases.
            ItemOpacity::Opaque.max(name_opacity)
        } else {
            name_opacity
        };

        let item_meta = ItemMeta {
            name,
            span,
            source_text: def.source_text.clone(),
            attr_info,
            is_local,
            opacity,
            lang_item,
        };
        self.cached_item_metas
            .insert(def.def_id.clone(), item_meta.clone());
        item_meta
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
            // We use the debug formatter to generate a filename.
            // This is not ideal, but filenames are for debugging anyway.
            _ => FileName::NotReal(format!("{name:?}")),
        }
    }

    pub fn translate_raw_span(&mut self, rspan: &hax::Span) -> meta::RawSpan {
        let filename = self.translate_filename(&rspan.filename);
        let rust_span = rspan.rust_span_data.unwrap().span();
        let file_id = match &filename {
            FileName::NotReal(_) => {
                // For now we forbid not real filenames
                unimplemented!();
            }
            FileName::Virtual(_) | FileName::Local(_) => self.register_file(filename, rust_span),
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
        meta::RawSpan { file_id, beg, end }
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

    pub(crate) fn def_span(&mut self, def_id: &hax::DefId) -> Span {
        let span = def_id.def_span(&self.hax_state);
        self.translate_span_from_hax(&span)
    }

    /// Translates a rust attribute. Returns `None` if the attribute is a doc comment (rustc
    /// encodes them as attributes). For now we use `String`s for `Attributes`.
    pub(crate) fn translate_attribute(&mut self, attr: &hax::Attribute) -> Option<Attribute> {
        use hax::Attribute as Haxttribute;
        use hax::AttributeKind as HaxttributeKind;
        match attr {
            Haxttribute::Parsed(HaxttributeKind::DocComment { comment, .. }) => {
                Some(Attribute::DocComment(comment.to_string()))
            }
            Haxttribute::Parsed(_) => None,
            Haxttribute::Unparsed(attr) => {
                let raw_attr = RawAttribute {
                    path: attr.path.clone(),
                    args: match &attr.args {
                        hax::AttrArgs::Empty => None,
                        hax::AttrArgs::Delimited(args) => Some(args.tokens.clone()),
                        hax::AttrArgs::Eq { expr, .. } => self
                            .tcx
                            .sess
                            .source_map()
                            .span_to_snippet(expr.span.rust_span_data.unwrap().span())
                            .ok(),
                    },
                };
                match Attribute::parse_from_raw(raw_attr) {
                    Ok(a) => Some(a),
                    Err(msg) => {
                        let span = self.translate_span_from_hax(&attr.span);
                        register_error!(self, span, "Error parsing attribute: {msg}");
                        None
                    }
                }
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
                    hax::InlineAttr::Force { .. } => Some(InlineAttr::Always),
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
        self.options.opacity_for_name(&self.translated, name)
    }

    pub(crate) fn register_id_no_enqueue(
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
                self.id_map.insert(id.clone(), trans_id);
                self.reverse_id_map.insert(trans_id, id.clone());
                self.translated.all_ids.insert(trans_id);
                // Store the name early so the name matcher can identify paths. We can't to it for
                // trait impls because they register themselves when computing their name.
                if !matches!(id, TransItemSource::TraitImpl(_)) {
                    if let Ok(name) = self.hax_def_id_to_name(id.as_def_id()) {
                        self.translated.item_names.insert(trans_id, name);
                    }
                }
                trans_id
            }
        };
        self.errors
            .borrow_mut()
            .register_dep_source(src, item_id, id.as_def_id().is_local);
        item_id
    }

    /// Register this id and enqueue it for translation.
    pub(crate) fn register_and_enqueue_id(
        &mut self,
        src: &Option<DepSource>,
        id: TransItemSource,
    ) -> AnyTransId {
        self.items_to_translate.insert(id.clone());
        self.register_id_no_enqueue(src, id)
    }

    pub(crate) fn register_type_decl_id(
        &mut self,
        src: &Option<DepSource>,
        id: &hax::DefId,
    ) -> TypeDeclId {
        *self
            .register_and_enqueue_id(src, TransItemSource::Type(id.clone()))
            .as_type()
            .unwrap()
    }

    pub(crate) fn register_fun_decl_id(
        &mut self,
        src: &Option<DepSource>,
        id: &hax::DefId,
    ) -> FunDeclId {
        *self
            .register_and_enqueue_id(src, TransItemSource::Fun(id.clone()))
            .as_fun()
            .unwrap()
    }

    pub(crate) fn register_trait_decl_id(
        &mut self,
        src: &Option<DepSource>,
        id: &hax::DefId,
    ) -> TraitDeclId {
        *self
            .register_and_enqueue_id(src, TransItemSource::TraitDecl(id.clone()))
            .as_trait_decl()
            .unwrap()
    }

    pub(crate) fn register_trait_impl_id(
        &mut self,
        src: &Option<DepSource>,
        id: &hax::DefId,
    ) -> TraitImplId {
        // Register the corresponding trait early so we can filter on its name.
        if let Ok(def) = self.hax_def(id) {
            let hax::FullDefKind::TraitImpl { trait_pred, .. } = def.kind() else {
                unreachable!()
            };
            let trait_rust_id = &trait_pred.trait_ref.def_id;
            let _ = self.register_trait_decl_id(src, trait_rust_id);
        }

        *self
            .register_and_enqueue_id(src, TransItemSource::TraitImpl(id.clone()))
            .as_trait_impl()
            .unwrap()
    }

    pub(crate) fn register_global_decl_id(
        &mut self,
        src: &Option<DepSource>,
        id: &hax::DefId,
    ) -> GlobalDeclId {
        *self
            .register_and_enqueue_id(src, TransItemSource::Global(id.clone()))
            .as_global()
            .unwrap()
    }

    pub(crate) fn with_def_id<F, T>(
        &mut self,
        def_id: &hax::DefId,
        item_id: Option<AnyTransId>,
        f: F,
    ) -> T
    where
        F: FnOnce(&mut Self) -> T,
    {
        let mut errors = self.errors.borrow_mut();
        let current_def_id = mem::replace(&mut errors.def_id, item_id);
        let current_def_id_is_local = mem::replace(&mut errors.def_id_is_local, def_id.is_local);
        drop(errors); // important: release the refcell "lock"
        let ret = f(self);
        let mut errors = self.errors.borrow_mut();
        errors.def_id = current_def_id;
        errors.def_id_is_local = current_def_id_is_local;
        ret
    }
}

impl<'tcx, 'ctx> ItemTransCtx<'tcx, 'ctx> {
    /// Create a new `ExecContext`.
    pub(crate) fn new(
        def_id: hax::DefId,
        item_id: Option<AnyTransId>,
        t_ctx: &'ctx mut TranslateCtx<'tcx>,
    ) -> Self {
        ItemTransCtx {
            def_id,
            item_id,
            t_ctx,
            error_on_impl_expr_error: true,
            binding_levels: Default::default(),
            parent_trait_clauses: Default::default(),
            item_trait_clauses: Default::default(),
        }
    }

    pub fn span_err(&self, span: Span, msg: &str, level: Level) -> Error {
        self.t_ctx.span_err(span, msg, level)
    }

    pub(crate) fn translate_span_from_hax(&mut self, rspan: &hax::Span) -> Span {
        self.t_ctx.translate_span_from_hax(rspan)
    }

    pub(crate) fn hax_def(&mut self, def_id: &hax::DefId) -> Result<Arc<hax::FullDef>, Error> {
        self.t_ctx.hax_def(def_id)
    }

    pub(crate) fn def_span(&mut self, def_id: &hax::DefId) -> Span {
        self.t_ctx.def_span(def_id)
    }

    pub(crate) fn register_id_no_enqueue(&mut self, span: Span, id: TransItemSource) -> AnyTransId {
        let src = self.make_dep_source(span);
        self.t_ctx.register_id_no_enqueue(&src, id)
    }

    pub(crate) fn register_type_decl_id(&mut self, span: Span, id: &hax::DefId) -> TypeDeclId {
        let src = self.make_dep_source(span);
        self.t_ctx.register_type_decl_id(&src, id)
    }

    pub(crate) fn register_fun_decl_id(&mut self, span: Span, id: &hax::DefId) -> FunDeclId {
        let src = self.make_dep_source(span);
        self.t_ctx.register_fun_decl_id(&src, id)
    }

    pub(crate) fn register_fun_decl_id_no_enqueue(
        &mut self,
        span: Span,
        id: &hax::DefId,
    ) -> FunDeclId {
        self.register_id_no_enqueue(span, TransItemSource::Fun(id.clone()))
            .as_fun()
            .copied()
            .unwrap()
    }

    pub(crate) fn register_global_decl_id(&mut self, span: Span, id: &hax::DefId) -> GlobalDeclId {
        let src = self.make_dep_source(span);
        self.t_ctx.register_global_decl_id(&src, id)
    }

    /// Returns an [Option] because we may ignore some builtin or auto traits
    /// like [core::marker::Sized] or [core::marker::Sync].
    pub(crate) fn register_trait_decl_id(&mut self, span: Span, id: &hax::DefId) -> TraitDeclId {
        let src = self.make_dep_source(span);
        self.t_ctx.register_trait_decl_id(&src, id)
    }

    /// Returns an [Option] because we may ignore some builtin or auto traits
    /// like [core::marker::Sized] or [core::marker::Sync].
    pub(crate) fn register_trait_impl_id(&mut self, span: Span, id: &hax::DefId) -> TraitImplId {
        let src = self.make_dep_source(span);
        self.t_ctx.register_trait_impl_id(&src, id)
    }

    /// Get the only binding level. Panics if there are other binding levels.
    pub(crate) fn the_only_binder(&self) -> &BindingLevel {
        assert_eq!(self.binding_levels.len(), 1);
        &self.outermost_binder()
    }

    pub(crate) fn outermost_binder(&self) -> &BindingLevel {
        self.binding_levels.outermost()
    }

    pub(crate) fn innermost_binder(&self) -> &BindingLevel {
        self.binding_levels.innermost()
    }

    pub(crate) fn innermost_binder_mut(&mut self) -> &mut BindingLevel {
        self.binding_levels.innermost_mut()
    }

    pub(crate) fn innermost_generics_mut(&mut self) -> &mut GenericParams {
        &mut self.innermost_binder_mut().params
    }

    pub(crate) fn lookup_bound_region(
        &mut self,
        span: Span,
        dbid: hax::DebruijnIndex,
        var: hax::BoundVar,
    ) -> Result<RegionDbVar, Error> {
        let dbid = DeBruijnId::new(dbid);
        if let Some(rid) = self
            .binding_levels
            .get(dbid)
            .and_then(|bl| bl.bound_region_vars.get(var))
        {
            Ok(DeBruijnVar::bound(dbid, *rid))
        } else {
            raise_error!(
                self,
                span,
                "Unexpected error: could not find region '{dbid}_{var}"
            )
        }
    }

    fn lookup_param<Id: Copy>(
        &mut self,
        span: Span,
        f: impl for<'a> Fn(&'a BindingLevel) -> Option<Id>,
        mk_err: impl FnOnce() -> String,
    ) -> Result<DeBruijnVar<Id>, Error> {
        for (dbid, bl) in self.binding_levels.iter_enumerated() {
            if let Some(id) = f(bl) {
                return Ok(DeBruijnVar::bound(dbid, id));
            }
        }
        let err = mk_err();
        raise_error!(self, span, "Unexpected error: could not find {}", err)
    }

    pub(crate) fn lookup_early_region(
        &mut self,
        span: Span,
        region: &hax::EarlyParamRegion,
    ) -> Result<RegionDbVar, Error> {
        self.lookup_param(
            span,
            |bl| bl.early_region_vars.get(region).copied(),
            || format!("the region variable {region:?}"),
        )
    }

    pub(crate) fn lookup_type_var(
        &mut self,
        span: Span,
        param: &hax::ParamTy,
    ) -> Result<TypeDbVar, Error> {
        self.lookup_param(
            span,
            |bl| bl.type_vars_map.get(&param.index).copied(),
            || format!("the type variable {}", param.name),
        )
    }

    pub(crate) fn lookup_const_generic_var(
        &mut self,
        span: Span,
        param: &hax::ParamConst,
    ) -> Result<ConstGenericDbVar, Error> {
        self.lookup_param(
            span,
            |bl| bl.const_generic_vars_map.get(&param.index).copied(),
            || format!("the const generic variable {}", param.name),
        )
    }

    pub(crate) fn lookup_clause_var(
        &mut self,
        span: Span,
        mut id: usize,
    ) -> Result<ClauseDbVar, Error> {
        // The clause indices returned by hax count clauses in order, starting from the parentmost.
        // While adding clauses to a binding level we already need to translate types and clauses,
        // so the innermost item binder may not have all the clauses yet. Hence for that binder we
        // ignore the clause count.
        let innermost_item_binder_id = self
            .binding_levels
            .iter_enumerated()
            .find(|(_, bl)| bl.is_item_binder)
            .unwrap()
            .0;
        // Iterate over the binders, starting from the outermost.
        for (dbid, bl) in self.binding_levels.iter_enumerated().rev() {
            let num_clauses_bound_at_this_level = bl.params.trait_clauses.elem_count();
            if id < num_clauses_bound_at_this_level || dbid == innermost_item_binder_id {
                let id = TraitClauseId::from_usize(id);
                return Ok(DeBruijnVar::bound(dbid, id));
            } else {
                id -= num_clauses_bound_at_this_level
            }
        }
        // Actually unreachable
        raise_error!(
            self,
            span,
            "Unexpected error: could not find clause variable {}",
            id
        )
    }

    pub(crate) fn lookup_cached_type(
        &self,
        cache_key: &HashByAddr<Arc<hax::TyKind>>,
    ) -> Option<Ty> {
        // Important: we can't reuse type caches from earlier binders as the new binder may change
        // what a given variable resolves to.
        self.innermost_binder()
            .type_trans_cache
            .get(&cache_key)
            .cloned()
    }

    /// Push a group of bound regions and call the continuation.
    /// We use this when diving into a `for<'a>`, or inside an arrow type (because
    /// it contains universally quantified regions).
    pub(crate) fn translate_region_binder<F, T, U>(
        &mut self,
        _span: Span,
        binder: &hax::Binder<T>,
        f: F,
    ) -> Result<RegionBinder<U>, Error>
    where
        F: FnOnce(&mut Self, &T) -> Result<U, Error>,
    {
        assert!(!self.binding_levels.is_empty());

        // Register the variables
        let mut binding_level = BindingLevel::new(false);
        binding_level.push_params_from_binder(binder.rebind(()))?;
        self.binding_levels.push(binding_level);

        // Call the continuation. Important: do not short-circuit on error here.
        let res = f(self, binder.hax_skip_binder_ref());

        // Reset
        let regions = self.binding_levels.pop().unwrap().params.regions;

        // Return
        res.map(|skip_binder| RegionBinder {
            regions,
            skip_binder,
        })
    }

    /// Push a new binding level corresponding to the provided `def` for the duration of the inner
    /// function call.
    pub(crate) fn translate_binder_for_def<F, U>(
        &mut self,
        span: Span,
        kind: BinderKind,
        def: &hax::FullDef,
        f: F,
    ) -> Result<Binder<U>, Error>
    where
        F: FnOnce(&mut Self) -> Result<U, Error>,
    {
        assert!(!self.binding_levels.is_empty());

        // Register the type-level parameters. This pushes a new binding level.
        self.translate_def_generics_without_parents(span, def)?;

        // Call the continuation. Important: do not short-circuit on error here.
        let res = f(self);

        // Reset
        let params = self.binding_levels.pop().unwrap().params;

        // Return
        res.map(|skip_binder| Binder {
            kind,
            params,
            skip_binder,
        })
    }

    pub(crate) fn make_dep_source(&self, span: Span) -> Option<DepSource> {
        Some(DepSource {
            src_id: self.item_id?,
            span: self.def_id.is_local.then_some(span),
        })
    }
}

impl<'a> IntoFormatter for &'a TranslateCtx<'_> {
    type C = FmtCtx<'a>;
    fn into_fmt(self) -> Self::C {
        self.translated.into_fmt()
    }
}

impl<'a> IntoFormatter for &'a ItemTransCtx<'_, '_> {
    type C = FmtCtx<'a>;
    fn into_fmt(self) -> Self::C {
        FmtCtx {
            translated: Some(&self.t_ctx.translated),
            generics: self.binding_levels.map_ref(|bl| Cow::Borrowed(&bl.params)),
            locals: None,
        }
    }
}

impl<'tcx, 'ctx> fmt::Display for TranslateCtx<'tcx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.translated.fmt(f)
    }
}
