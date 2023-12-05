//! Defines some utilities for [crate::names]
//!
//! For now, we have one function per object kind (type, trait, function,
//! module): many of them could be factorized (will do).
use crate::formatter::AstFormatter;
use crate::names::*;
use crate::translate_ctx::*;
use hax_frontend_exporter as hax;
use hax_frontend_exporter::SInto;
use rustc_hir::{Item, ItemKind};
use rustc_span::def_id::DefId;
use std::collections::HashSet;

impl PathElem {
    fn equals_ident(&self, id: &str) -> bool {
        match self {
            PathElem::Ident(s, d) => s == id && d.is_zero(),
            PathElem::Impl(_) => false,
        }
    }

    pub fn fmt_with_ctx<C>(&self, ctx: &C) -> String
    where
        C: AstFormatter,
    {
        match self {
            PathElem::Ident(s, d) => {
                let d = if d.is_zero() {
                    "".to_string()
                } else {
                    format!("#{}", d)
                };
                format!("{s}{d}")
            }
            PathElem::Impl(impl_elem) => impl_elem.fmt_with_ctx(ctx),
        }
    }
}

impl ImplElem {
    pub fn fmt_with_ctx<C>(&self, ctx: &C) -> String
    where
        C: AstFormatter,
    {
        let d = if self.disambiguator.is_zero() {
            "".to_string()
        } else {
            format!("#{}", self.disambiguator)
        };
        let ctx = ctx.set_generics(&self.generics);
        // Just printing the generics (not the predicates)
        format!("{{{}{d}}}", self.ty.fmt_with_ctx(&ctx),)
    }
}

impl Name {
    pub fn fmt_with_ctx<C>(&self, ctx: &C) -> String
    where
        C: AstFormatter,
    {
        let name = self
            .name
            .iter()
            .map(|x| x.fmt_with_ctx(ctx))
            .collect::<Vec<String>>();
        name.join("::")
    }
}

impl Name {
    #[allow(clippy::len_without_is_empty)]
    pub fn len(&self) -> usize {
        self.name.len()
    }

    /// Compare the name to a constant array.
    /// This ignores disambiguators.
    ///
    /// `equal`: if `true`, check that the name is equal to the ref. If `false`:
    /// only check if the ref is a prefix of the name.
    pub fn compare_with_ref_name(&self, equal: bool, ref_name: &[&str]) -> bool {
        let name: Vec<&PathElem> = self.name.iter().filter(|e| e.is_ident()).collect();

        if name.len() < ref_name.len() || (equal && name.len() != ref_name.len()) {
            return false;
        }

        for i in 0..ref_name.len() {
            if !name[i].equals_ident(ref_name[i]) {
                return false;
            }
        }
        true
    }

    /// Compare the name to a constant array.
    /// This ignores disambiguators.
    pub fn equals_ref_name(&self, ref_name: &[&str]) -> bool {
        self.compare_with_ref_name(true, ref_name)
    }

    /// Compare the name to a constant array.
    /// This ignores disambiguators.
    pub fn prefix_is_same(&self, ref_name: &[&str]) -> bool {
        self.compare_with_ref_name(false, ref_name)
    }

    /// Return `true` if the name identifies an item inside the module: `krate::module`
    pub fn is_in_module(&self, krate: &String, module: &String) -> bool {
        self.prefix_is_same(&[krate, module])
    }

    /// Similar to [Name::is_in_module]
    pub fn is_in_modules(&self, krate: &String, modules: &HashSet<String>) -> bool {
        if self.len() >= 2 {
            match (&self.name[0], &self.name[1]) {
                (PathElem::Ident(s0, _), PathElem::Ident(s1, _)) => {
                    s0 == krate && modules.contains(s1)
                }
                _ => false,
            }
        } else {
            false
        }
    }
}

impl<'tcx, 'ctx> TransCtx<'tcx, 'ctx> {
    /// Retrieve an item name from a [DefId].
    pub fn extended_def_id_to_name(&mut self, def_id: &hax::ExtendedDefId) -> Name {
        trace!("{:?}", def_id);
        let span = self.tcx.def_span(def_id.rust_def_id.unwrap());

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

        // Rk.: below we try to be as tight as possible with regards to sanity
        // checks, to make sure we understand what happens with def paths, and
        // fail whenever we get something which is even slightly outside what
        // we expect.
        for data in &def_id.path {
            // Match over the key data
            let disambiguator = Disambiguator::Id::new(data.disambiguator as usize);
            use hax::ExtendedDefPathItem;
            match &data.data {
                ExtendedDefPathItem::TypeNs(symbol) => {
                    assert!(data.disambiguator == 0); // Sanity check
                    name.push(PathElem::Ident(symbol.clone(), disambiguator));
                }
                ExtendedDefPathItem::ValueNs(symbol) => {
                    if data.disambiguator != 0 {
                        // I don't like that

                        // I think this only happens with names introduced by macros
                        // (though not sure). For instance:
                        // `betree_main::betree_utils::_#1::{impl#0}::deserialize::{impl#0}`
                        let s = symbol;
                        assert!(s == "_");
                        name.push(PathElem::Ident(s.clone(), disambiguator));
                    } else {
                        name.push(PathElem::Ident(symbol.clone(), disambiguator));
                    }
                }
                ExtendedDefPathItem::CrateRoot => {
                    // Sanity check
                    assert!(data.disambiguator == 0);

                    // This should be the beginning of the path
                    assert!(name.is_empty());
                    found_crate_name = true;
                    name.push(PathElem::Ident(def_id.krate.clone(), disambiguator));
                }
                ExtendedDefPathItem::Impl {
                    id,
                    substs,
                    bounds: _, // We actually need to directly interact with Rustc
                    ty,
                } => {
                    // We need to convert the type, which may contain quantified
                    // substs and bounds. In order to properly do so, we introduce
                    // a body translation context.
                    let id = id.unwrap();
                    let mut bt_ctx = BodyTransCtx::new(id, self);

                    bt_ctx
                        .translate_generic_params_from_hax(span, substs)
                        .unwrap();
                    bt_ctx.translate_predicates_of(None, id).unwrap();
                    let erase_regions = false;
                    let ty = bt_ctx.translate_ty(span, erase_regions, ty).unwrap();

                    name.push(PathElem::Impl(ImplElem {
                        generics: bt_ctx.get_generics(),
                        preds: bt_ctx.get_predicates(),
                        ty,
                        disambiguator,
                    }));
                }
                ExtendedDefPathItem::ImplTrait => {
                    // TODO: do nothing for now
                }
                ExtendedDefPathItem::MacroNs(symbol) => {
                    assert!(data.disambiguator == 0); // Sanity check

                    // There may be namespace collisions between, say, function
                    // names and macros (not sure). However, this isn't much
                    // of an issue here, because for now we don't expose macros
                    // in the AST, and only use macro names in [register], for
                    // instance to filter opaque modules.
                    name.push(PathElem::Ident(symbol.clone(), disambiguator));
                }
                ExtendedDefPathItem::ClosureExpr => {
                    // TODO: this is not very satisfactory, but on the other hand
                    // we should be able to extract closures in local let-bindings
                    // (i.e., we shouldn't have to introduce top-level let-bindings).
                    name.push(PathElem::Ident("closure".to_string(), disambiguator))
                }
                _ => {
                    error!("Unexpected ExtendedDefPathItem: {:?}", data);
                    unreachable!("Unexpected ExtendedDefPathItem: {:?}", data);
                }
            }
        }

        // We always add the crate name
        if !found_crate_name {
            name.push(PathElem::Ident(
                def_id.krate.clone(),
                Disambiguator::Id::new(0),
            ));
        }

        trace!("{:?}", name);
        Name { name }
    }

    pub(crate) fn make_hax_state_with_id(
        &mut self,
        def_id: DefId,
    ) -> hax::State<hax::Base<'tcx>, (), (), DefId> {
        hax::state::State {
            thir: (),
            mir: (),
            owner_id: def_id,
            base: hax::Base::new(
                self.tcx,
                hax::options::Options {
                    inline_macro_calls: Vec::new(),
                },
            ),
        }
    }

    /// Returns an optional name for an HIR item.
    ///
    /// If the option is `None`, it means the item is to be ignored (example: it
    /// is a `use` item).
    ///
    /// Rk.: this function is only used by [crate::register], and implemented with this
    /// context in mind.
    pub fn hir_item_to_name(&mut self, item: &Item) -> Option<Name> {
        // We have to create a hax state, which is annoying...
        let state = self.make_hax_state_with_id(item.owner_id.to_def_id());
        let def_id = item.owner_id.to_def_id().sinto(&state);

        match &item.kind {
            ItemKind::OpaqueTy(_) => unimplemented!(),
            ItemKind::Union(_, _) => unimplemented!(),
            ItemKind::ExternCrate(_) => {
                // We ignore this -
                // TODO: investigate when extern crates appear, and why
                Option::None
            }
            ItemKind::Use(_, _) => Option::None,
            ItemKind::TyAlias(_, _) => {
                // We ignore the type aliases - it seems they are inlined
                Option::None
            }
            ItemKind::Enum(_, _)
            | ItemKind::Struct(_, _)
            | ItemKind::Fn(_, _, _)
            | ItemKind::Impl(_)
            | ItemKind::Mod(_)
            | ItemKind::Const(_, _)
            | ItemKind::Static(_, _, _)
            | ItemKind::Macro(_, _)
            | ItemKind::Trait(..) => Option::Some(self.extended_def_id_to_name(&def_id)),
            _ => {
                unimplemented!("{:?}", item.kind);
            }
        }
    }

    // TODO: remove
    pub fn item_def_id_to_name(&mut self, def_id: rustc_span::def_id::DefId) -> Name {
        let state = self.make_hax_state_with_id(def_id);
        self.extended_def_id_to_name(&def_id.sinto(&state))
    }

    pub fn def_id_to_name(&mut self, def_id: &hax::DefId) -> Name {
        // We have to create a hax state, which is annoying...
        let state = self.make_hax_state_with_id(def_id.rust_def_id.unwrap());
        self.extended_def_id_to_name(&def_id.rust_def_id.unwrap().sinto(&state))
    }
}
