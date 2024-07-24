//! The translation contexts.
use super::translate_predicates::NonLocalTraitClause;
use super::translate_traits::PredicateLocation;
use charon_lib::ast::*;
use charon_lib::common::*;
use charon_lib::formatter::{FmtCtx, IntoFormatter};
use charon_lib::ids::{MapGenerator, Vector};
use charon_lib::options::TransOptions;
use charon_lib::ullbc_ast as ast;
use hax_frontend_exporter as hax;
use hax_frontend_exporter::SInto;
use macros::VariantIndexArity;
use rustc_ast::AttrArgs;
use rustc_ast_pretty::pprust;
use rustc_error_messages::MultiSpan;
use rustc_hir::def_id::DefId;
use rustc_hir::Node as HirNode;
use rustc_hir::{Item, ItemKind};
use rustc_middle::ty::TyCtxt;
use std::cmp::{Ord, PartialOrd};
use std::collections::HashMap;
use std::collections::{BTreeMap, VecDeque};
use std::fmt;
use std::path::Component;

// Re-export to avoid having to fix imports.
pub(crate) use charon_lib::errors::{
    error_assert, error_or_panic, register_error_or_panic, DepSource, ErrorCtx,
};

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
    /// Accumulated clauses to be put into the item's `GenericParams`.
    pub param_trait_clauses: Vector<TraitClauseId, TraitClause>,
    /// (For traits only) accumulated implied trait clauses.
    pub parent_trait_clauses: Vector<TraitClauseId, TraitClause>,
    /// (For traits only) accumulated trait clauses on associated types.
    pub item_trait_clauses: HashMap<TraitItemName, Vector<TraitClauseId, TraitClause>>,
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

    /// Retrieve an item name from a [DefId].
    pub fn def_id_to_name(&mut self, def_id: DefId) -> Result<Name, Error> {
        trace!("{:?}", def_id);
        let tcx = self.tcx;
        let span = tcx.def_span(def_id);

        // We have to be a bit careful when retrieving names from def ids. For instance,
        // due to reexports, [`TyCtxt::def_path_str`](TyCtxt::def_path_str) might give
        // different names depending on the def id on which it is called, even though
        // those def ids might actually identify the same definition.
        // For instance: `std::boxed::Box` and `alloc::boxed::Box` are actually
        // the same (the first one is a reexport).
        // This is why we implement a custom function to retrieve the original name
        // (though this makes us loose aliases - we may want to investigate this
        // issue in the future).

        // We lookup the path associated to an id, and convert it to a name.
        // Paths very precisely identify where an item is. There are important
        // subcases, like the items in an `Impl` block:
        // ```
        // impl<T> List<T> {
        //   fn new() ...
        // }
        // ```
        //
        // One issue here is that "List" *doesn't appear* in the path, which would
        // look like the following:
        //
        //   `TypeNS("Crate") :: Impl :: ValueNs("new")`
        //                       ^^^
        //           This is where "List" should be
        //
        // For this reason, whenever we find an `Impl` path element, we actually
        // lookup the type of the sub-path, from which we can derive a name.
        //
        // Besides, as there may be several "impl" blocks for one type, each impl
        // block is identified by a unique number (rustc calls this a
        // "disambiguator"), which we grab.
        //
        // Example:
        // ========
        // For instance, if we write the following code in crate `test` and module
        // `bla`:
        // ```
        // impl<T> Foo<T> {
        //   fn foo() { ... }
        // }
        //
        // impl<T> Foo<T> {
        //   fn bar() { ... }
        // }
        // ```
        //
        // The names we will generate for `foo` and `bar` are:
        // `[Ident("test"), Ident("bla"), Ident("Foo"), Disambiguator(0), Ident("foo")]`
        // `[Ident("test"), Ident("bla"), Ident("Foo"), Disambiguator(1), Ident("bar")]`
        let mut found_crate_name = false;
        let mut name: Vec<PathElem> = Vec::new();

        let def_path = tcx.def_path(def_id);
        let crate_name = tcx.crate_name(def_path.krate).to_string();

        let parents: Vec<DefId> = {
            let mut parents = vec![def_id];
            let mut cur_id = def_id;
            while let Some(parent) = tcx.opt_parent(cur_id) {
                parents.push(parent);
                cur_id = parent;
            }
            parents.into_iter().rev().collect()
        };

        // Rk.: below we try to be as tight as possible with regards to sanity
        // checks, to make sure we understand what happens with def paths, and
        // fail whenever we get something which is even slightly outside what
        // we expect.
        for cur_id in parents {
            let data = tcx.def_key(cur_id).disambiguated_data;
            // Match over the key data
            let disambiguator = Disambiguator::new(data.disambiguator as usize);
            use rustc_hir::definitions::DefPathData;
            match &data.data {
                DefPathData::TypeNs(symbol) => {
                    error_assert!(self, span, data.disambiguator == 0); // Sanity check
                    name.push(PathElem::Ident(symbol.to_string(), disambiguator));
                }
                DefPathData::ValueNs(symbol) => {
                    // I think `disambiguator != 0` only with names introduced by macros (though
                    // not sure).
                    name.push(PathElem::Ident(symbol.to_string(), disambiguator));
                }
                DefPathData::CrateRoot => {
                    // Sanity check
                    error_assert!(self, span, data.disambiguator == 0);

                    // This should be the beginning of the path
                    error_assert!(self, span, name.is_empty());
                    found_crate_name = true;
                    name.push(PathElem::Ident(crate_name.clone(), disambiguator));
                }
                DefPathData::Impl => {
                    // Two cases, depending on whether the impl block is
                    // a "regular" impl block (`impl Foo { ... }`) or a trait
                    // implementation (`impl Bar for Foo { ... }`).
                    let impl_elem = match self.tcx.impl_trait_ref(cur_id) {
                        None => {
                            // We need to convert the type, which may contain quantified
                            // substs and bounds. In order to properly do so, we introduce
                            // a body translation context.
                            let mut bt_ctx = BodyTransCtx::new(cur_id, self);

                            // Translate to hax types
                            // TODO: use the bounds
                            let _bounds: Vec<hax::Clause> = bt_ctx
                                .t_ctx
                                .tcx
                                .predicates_of(cur_id)
                                .predicates
                                .iter()
                                .map(|(x, _)| x.sinto(&bt_ctx.hax_state))
                                .collect();
                            let ty = tcx
                                .type_of(cur_id)
                                .instantiate_identity()
                                .sinto(&bt_ctx.hax_state);

                            bt_ctx.translate_generic_params(cur_id)?;
                            bt_ctx.translate_predicates_of(
                                None,
                                cur_id,
                                PredicateOrigin::WhereClauseOnImpl,
                                &PredicateLocation::Base,
                            )?;
                            let erase_regions = false;
                            // Inherent impl ("regular" impl)
                            let ty = bt_ctx.translate_ty(span, erase_regions, &ty)?;
                            let generics = bt_ctx.get_generics();
                            ImplElem::Ty(generics, ty)
                        }
                        Some(_) => {
                            let impl_id = self.register_trait_impl_id(&None, cur_id)?;
                            // // Trait implementation
                            // let trait_ref = trait_ref.sinto(&bt_ctx.hax_state);
                            // let erase_regions = false;
                            // let trait_ref =
                            //     bt_ctx.translate_trait_decl_ref(span, erase_regions, &trait_ref)?;
                            match impl_id {
                                None => error_or_panic!(self, span, "The trait reference was ignored while we need it to compute the name"),
                                Some(impl_id) => {
                                    ImplElem::Trait(impl_id)
                                }
                            }
                        }
                    };

                    name.push(PathElem::Impl(impl_elem, disambiguator));
                }
                DefPathData::OpaqueTy => {
                    // TODO: do nothing for now
                }
                DefPathData::MacroNs(symbol) => {
                    error_assert!(self, span, data.disambiguator == 0); // Sanity check

                    // There may be namespace collisions between, say, function
                    // names and macros (not sure). However, this isn't much
                    // of an issue here, because for now we don't expose macros
                    // in the AST, and only use macro names in [register], for
                    // instance to filter opaque modules.
                    name.push(PathElem::Ident(symbol.to_string(), disambiguator));
                }
                DefPathData::Closure => {
                    // TODO: this is not very satisfactory, but on the other hand
                    // we should be able to extract closures in local let-bindings
                    // (i.e., we shouldn't have to introduce top-level let-bindings).
                    name.push(PathElem::Ident("closure".to_string(), disambiguator))
                }
                DefPathData::ForeignMod => {
                    // Do nothing, functions in `extern` blocks are in the same namespace as the
                    // block.
                }
                _ => {
                    error_or_panic!(self, span, format!("Unexpected DefPathData: {:?}", data));
                }
            }
        }

        // We always add the crate name
        if !found_crate_name {
            name.push(PathElem::Ident(crate_name, Disambiguator::new(0)));
        }

        trace!("{:?}", name);
        Ok(Name { name })
    }

    /// Returns an optional name for an HIR item.
    ///
    /// If the option is `None`, it means the item is to be ignored (example: it
    /// is a `use` item).
    ///
    /// Rk.: this function is only used by [crate::register], and implemented with this
    /// context in mind.
    pub fn hir_item_to_name(&mut self, item: &Item) -> Result<Option<Name>, Error> {
        let def_id = item.owner_id.to_def_id();

        let name = match &item.kind {
            ItemKind::OpaqueTy(..) => unimplemented!(),
            ItemKind::Union(..) => unimplemented!(),
            ItemKind::ExternCrate(..) => {
                // We ignore this -
                // TODO: investigate when extern crates appear, and why
                None
            }
            ItemKind::Use(..) => None,
            ItemKind::TyAlias(..)
            | ItemKind::Enum(..)
            | ItemKind::Struct(..)
            | ItemKind::Fn(..)
            | ItemKind::Impl(..)
            | ItemKind::Mod(..)
            | ItemKind::ForeignMod { .. }
            | ItemKind::Const(..)
            | ItemKind::Static(..)
            | ItemKind::Macro(..)
            | ItemKind::Trait(..) => Some(self.def_id_to_name(def_id)?),
            _ => {
                unimplemented!("{:?}", item.kind);
            }
        };
        Ok(name)
    }

    pub fn hax_def_id_to_name(&mut self, def_id: &hax::DefId) -> Result<Name, Error> {
        // We have to create a hax state, which is annoying...
        self.def_id_to_name(DefId::from(def_id))
    }

    /// Compute the span information for a Rust definition identified by its id.
    pub(crate) fn translate_span_from_rid(&mut self, def_id: DefId) -> Span {
        // Retrieve the span from the def id.
        // Rem.: we use [TyCtxt::def_span], not [TyCtxt::def_ident_span] to retrieve the span.
        let rspan = self.tcx.def_span(def_id);
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

    pub fn translate_filename(&mut self, name: &hax::FileName) -> meta::FileName {
        match name {
            hax::FileName::Real(name) => {
                use hax::RealFileName;
                match name {
                    RealFileName::LocalPath(path) => FileName::Local(path.clone()),
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

    pub fn translate_span(&mut self, rspan: hax::Span) -> meta::RawSpan {
        let filename = self.translate_filename(&rspan.filename);
        let file_id = match &filename {
            FileName::NotReal(_) => {
                // For now we forbid not real filenames
                unimplemented!();
            }
            FileName::Virtual(_) | FileName::Local(_) => self.register_file(filename),
        };

        fn convert_loc(loc: hax::Loc) -> Loc {
            Loc {
                line: loc.line,
                col: loc.col,
            }
        }
        let beg = convert_loc(rspan.lo);
        let end = convert_loc(rspan.hi);

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

    /// Parse an attribute to recognize our special `charon::*` and `aeneas::*` attributes.
    pub(crate) fn parse_attribute(
        &mut self,
        normal_attr: &rustc_ast::NormalAttr,
        span: rustc_span::Span,
    ) -> Result<Attribute, String> {
        // We use `pprust` to render the attribute somewhat like it is written in the source.
        // WARNING: this can change whitespace, and sometimes even adds newlines. Maybe we
        // should use spans and SourceMap info instead.
        use pprust::PrintState;

        // If the attribute path has two components, the first of which is `charon` or `aeneas`, we
        // try to parse it. Otherwise we return `Unknown`.
        let attr_name = if let [path_start, attr_name] = normal_attr.item.path.segments.as_slice()
            && let path_start = path_start.ident.as_str()
            && (path_start == "charon" || path_start == "aeneas")
        {
            attr_name.ident.as_str()
        } else {
            let full_attr =
                pprust::State::to_string(|s| s.print_attr_item(&normal_attr.item, span));
            return Ok(Attribute::Unknown(full_attr));
        };

        let args = match &normal_attr.item.args {
            AttrArgs::Empty => None,
            AttrArgs::Delimited(args) => Some(rustc_ast_pretty::pprust::State::to_string(|s| {
                s.print_tts(&args.tokens, false)
            })),
            AttrArgs::Eq(..) => unimplemented!("`#[charon::foo = val]` syntax is unsupported"),
        };
        match Attribute::parse_special_attr(attr_name, args)? {
            Some(parsed) => Ok(parsed),
            None => {
                let full_attr = rustc_ast_pretty::pprust::State::to_string(|s| {
                    s.print_attr_item(&normal_attr.item, span)
                });
                Err(format!("Unrecognized attribute: `{full_attr}`"))
            }
        }
    }

    /// Translates a rust attribute. Returns `None` if the attribute is a doc comment (rustc
    /// encodes them as attributes). For now we use `String`s for `Attributes`.
    pub(crate) fn translate_attribute(&mut self, attr: &rustc_ast::Attribute) -> Option<Attribute> {
        use rustc_ast::ast::AttrKind;
        match &attr.kind {
            AttrKind::Normal(normal_attr) => match self.parse_attribute(&normal_attr, attr.span) {
                Ok(a) => Some(a),
                Err(msg) => {
                    self.span_err(attr.span, &format!("Error parsing attribute: {msg}"));
                    None
                }
            },
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
        if IGNORE_BUILTIN_MARKER_TRAITS {
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
            param_trait_clauses: Default::default(),
            parent_trait_clauses: Default::default(),
            item_trait_clauses: Default::default(),
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
        // Sanity checks
        assert!(self.region_vars.len() == 1);
        assert!(self
            .param_trait_clauses
            .iter()
            .enumerate()
            .all(|(i, c)| c.clause_id.index() == i));
        GenericParams {
            regions: self.region_vars[0].clone(),
            types: self.type_vars.clone(),
            const_generics: self.const_generic_vars.clone(),
            trait_clauses: self.param_trait_clauses.clone(),
            regions_outlive: self.regions_outlive.clone(),
            types_outlive: self.types_outlive.clone(),
            trait_type_constraints: self.trait_type_constraints.clone(),
        }
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
