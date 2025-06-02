//! The translation contexts.
use super::translate_crate::TransItemSource;
use super::translate_generics::BindingLevel;
use charon_lib::ast::*;
use charon_lib::formatter::{FmtCtx, IntoFormatter};
use charon_lib::ids::Vector;
use charon_lib::options::TranslateOptions;
use hax_frontend_exporter::{self as hax, DefPathItem};
use hax_frontend_exporter::{DefId, SInto};
use itertools::Itertools;
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
    pub cached_item_metas: HashMap<TransItemSource, ItemMeta>,
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

    /// Retrieve the name for this [`hax::DefId`]. Because a given `DefId` may give rise to several
    /// charon items, prefer to use `translate_name` when possible.
    ///
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
    pub fn def_id_to_name(&mut self, def_id: &hax::DefId) -> Result<Name, Error> {
        if let Some(name) = self.cached_names.get(&def_id) {
            return Ok(name.clone());
        }
        trace!("Computing name for `{def_id:?}`");

        let parent_name = if let Some(parent) = &def_id.parent {
            self.def_id_to_name(parent)?
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

    /// Retrieve the name for an item.
    pub fn translate_name(&mut self, src: &TransItemSource) -> Result<Name, Error> {
        let def_id = src.as_def_id();
        let mut name = self.def_id_to_name(def_id)?;
        match src {
            TransItemSource::ClosureTraitImpl(id, kind)
            | TransItemSource::ClosureMethod(id, kind) => {
                let _ = name.name.pop(); // Pop the `{closure}` path item
                let impl_id = self.register_closure_trait_impl_id(&None, id, *kind);
                name.name.push(PathElem::Impl(
                    ImplElem::Trait(impl_id),
                    Disambiguator::ZERO,
                ));

                if matches!(src, TransItemSource::ClosureMethod(..)) {
                    let fn_name = kind.method_name().to_string();
                    name.name
                        .push(PathElem::Ident(fn_name, Disambiguator::ZERO));
                }
            }
            _ => {}
        }
        Ok(name)
    }

    /// Remark: this **doesn't** register the def id (on purpose)
    pub(crate) fn translate_trait_item_name(
        &mut self,
        def_id: &hax::DefId,
    ) -> Result<TraitItemName, Error> {
        // Translate the name
        let name = self.def_id_to_name(def_id)?;
        let (name, id) = name.name.last().unwrap().as_ident().unwrap();
        assert!(id.is_zero());
        Ok(TraitItemName(name.to_string()))
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
        item_src: &TransItemSource,
        name: Name,
        name_opacity: ItemOpacity,
    ) -> ItemMeta {
        if let Some(item_meta) = self.cached_item_metas.get(&item_src) {
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
            .insert(item_src.clone(), item_meta.clone());
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

    pub(crate) fn get_lang_item(&self, item: rustc_hir::LangItem) -> DefId {
        self.t_ctx
            .tcx
            .lang_items()
            .get(item)
            .unwrap()
            .sinto(&self.t_ctx.hax_state)
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
            indent_level: 0,
        }
    }
}

impl<'tcx, 'ctx> fmt::Display for TranslateCtx<'tcx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.translated.fmt(f)
    }
}
