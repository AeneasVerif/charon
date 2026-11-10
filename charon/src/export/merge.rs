//! Generic logic for merging several [`CrateData`]s into one.
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::fmt::Debug;
use std::hash::Hash;
use std::mem;

use petgraph::prelude::DiGraphMap;
use petgraph::visit::{Dfs, Walker};

use crate::errors::ErrorCtx;
use crate::ids::IndexVec;
use crate::options::TranslateOptions;
use crate::transform::TransformCtx;
use crate::transform::ctx::TransformPass;
use crate::{ast::*, options::CliOpts};

use super::{CharonVersion, CrateData};

/// How to merge several crates into one.
pub(super) trait MergeStrategy {
    /// Uniquely identifies an input crate.
    type Key: Clone + Eq + Hash;

    /// The key of an input crate. Must be distinct for each input crate.
    fn key(&self, krate: &TranslatedCrate) -> Self::Key;

    /// Path element to append to the names of the items of the crate with that key.
    fn name_suffix(&self, _key: &Self::Key) -> Option<PathElem> {
        None
    }

    /// Decide what to do with each group of items that have the same name in several crates.
    /// This can edit/remove/add items, and returns a remapping of item ids that we then apply to
    /// the whole crate.
    fn link(
        &mut self,
        krate: &mut TranslatedCrate,
        groups: Vec<SeqHashMap<Self::Key, ItemId>>,
    ) -> Remapping;
}

/// A remapping of item ids, used to redirect the references to some items to other items.
#[derive(Default)]
pub(super) struct Remapping(HashMap<ItemId, ItemId>);

impl Remapping {
    /// Redirect the references to `from` to `to`.
    pub(super) fn add_remapping(&mut self, from: ItemId, to: ItemId) {
        if from != to {
            self.0.insert(from, to);
        }
    }
}

impl<'a> IntoIterator for &'a Remapping {
    type Item = (&'a ItemId, &'a ItemId);
    type IntoIter = std::collections::hash_map::Iter<'a, ItemId, ItemId>;
    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

/// Merge several crates into one.
/// In order:
/// 1. concatenate the crates together into one crate
/// 2. group items that have the same name across several crates
/// 3. call `MergeStrategy::link` with the groups from step 2
/// 4. apply the remapping given by step 3
/// 5. clean up the result
pub(super) fn merge<S: MergeStrategy>(
    options: CliOpts,
    krates: Vec<CrateData>,
    mut strategy: S,
) -> CrateData {
    let mut error_ctx = ErrorCtx::new();
    let tr_options = TranslateOptions::new(&mut error_ctx, &options);

    // step 1: concatenate all crates into one
    // this will also append the optional name suffix to all items
    let keys: Vec<_> = krates
        .iter()
        .map(|krate| strategy.key(&krate.translated))
        .collect();
    let name_suffixes = keys.iter().map(|key| strategy.name_suffix(key));
    let (mut merged, item_sources) = CrateMerger::process(krates.into_iter().zip(name_suffixes));

    // step 2: group items that have the same name across several crates
    // we pop the suffix here so that grouping finds anything at all
    let krate = &merged.translated;
    let groups = discover_groups(krate, |id, name| {
        let source = item_sources[&id];
        let mut name = name.clone();
        if strategy.name_suffix(&keys[source]).is_some() {
            name.name.pop();
        }
        Some((normalize_impl_elems(name, krate), keys[source].clone()))
    });

    // step 3: call `MergeStrategy::link` with the groups from step 2
    let remap = strategy.link(&mut merged.translated, groups);

    // step 4: apply the remapping given by step 3
    if !remap.0.is_empty() {
        merged
            .translated
            .drive_mut(&mut IdRefMapperVisitor::new(&remap));
    }

    // step 5: cleanup!
    let mut ctx = TransformCtx {
        options: tr_options,
        translated: merged.translated,
        errors: RefCell::new(error_ctx),
    };
    cleanup_post_merge(&mut ctx);
    merged.translated = ctx.translated;
    merged.translated.preset = options.preset;

    merged
}

// =============================================================================================
// Concatenate a set of crates into one.
// =============================================================================================

struct CrateMerger {
    merged: CrateData,
    file_name_to_id: HashMap<FileName, FileId>,
    /// For each item of the merged crate, the index of the input crate it comes from.
    item_sources: HashMap<ItemId, usize>,
}

impl CrateMerger {
    /// Concatenate the crates, appending the provided path element (if any) to every name in the
    /// corresponding crate. Also returns, for each item, the index of the crate it comes from.
    fn process(
        krates: impl IntoIterator<Item = (CrateData, Option<PathElem>)>,
    ) -> (CrateData, HashMap<ItemId, usize>) {
        let translated = TranslatedCrate::default();
        let mut merger = CrateMerger {
            merged: CrateData {
                charon_version: CharonVersion(crate::VERSION.to_owned()),
                translated,
                has_errors: false,
            },
            file_name_to_id: HashMap::new(),
            item_sources: HashMap::new(),
        };
        for (i, (krate, name_suffix)) in krates.into_iter().enumerate() {
            merger.add_one(i, krate, name_suffix);
        }

        (merger.merged, merger.item_sources)
    }

    fn add_one(&mut self, index: usize, krate: CrateData, name_suffix: Option<PathElem>) {
        let CrateData {
            charon_version: _, // Checked by deserialization already
            translated: mut krate,
            has_errors,
        } = krate;
        self.merged.has_errors |= has_errors;

        // Remap all ids inside `krate`.
        krate.drive_mut(&mut {
            let file_id_map = krate.files.map_ref(|file| {
                if let Some(&existing_id) = self.file_name_to_id.get(&file.name) {
                    existing_id
                } else {
                    let new_id = self.merged.translated.files.push_with(|new_id| {
                        let mut file = file.clone();
                        file.id = new_id;
                        file
                    });
                    self.file_name_to_id.insert(file.name.clone(), new_id);
                    new_id
                }
            });

            #[derive(Visitor)]
            struct RemapIdsVisitor {
                name_suffix: Option<PathElem>,
                file_id_map: IndexVec<FileId, FileId>,
                type_offset: usize,
                fun_offset: usize,
                global_offset: usize,
                trait_decl_offset: usize,
                trait_impl_offset: usize,
            }

            impl VisitAstMut for RemapIdsVisitor {
                fn enter_file_id(&mut self, id: &mut FileId) {
                    *id = self.file_id_map[*id];
                }
                fn enter_type_decl_id(&mut self, id: &mut TypeDeclId) {
                    *id += self.type_offset;
                }
                fn enter_fun_decl_id(&mut self, id: &mut FunDeclId) {
                    *id += self.fun_offset;
                }
                fn enter_global_decl_id(&mut self, id: &mut GlobalDeclId) {
                    *id += self.global_offset;
                }
                fn enter_trait_decl_id(&mut self, id: &mut TraitDeclId) {
                    *id += self.trait_decl_offset;
                }
                fn enter_trait_impl_id(&mut self, id: &mut TraitImplId) {
                    *id += self.trait_impl_offset;
                }
                fn visit_impl_restriction(
                    &mut self,
                    _x: &mut ImplRestriction,
                ) -> ControlFlow<Self::Break> {
                    ControlFlow::Continue(())
                }
                fn enter_name(&mut self, name: &mut Name) {
                    if let Some(suffix) = &self.name_suffix {
                        name.name.push(suffix.clone());
                    }
                }
            }

            RemapIdsVisitor {
                name_suffix,
                file_id_map,
                type_offset: self.merged.translated.type_decls.slot_count(),
                fun_offset: self.merged.translated.fun_decls.slot_count(),
                global_offset: self.merged.translated.global_decls.slot_count(),
                trait_decl_offset: self.merged.translated.trait_decls.slot_count(),
                trait_impl_offset: self.merged.translated.trait_impls.slot_count(),
            }
        });

        let TranslatedCrate {
            crate_name,
            preset: _, // The preset is shared by all crates
            target_information,
            runtime_checks,
            item_names,
            assoc_item_names,
            short_names: _, // Recomputed on the merged crate
            files: _,       // Done above
            type_decls,
            fun_decls,
            global_decls,
            trait_decls,
            trait_impls,
            ordered_decls: _, // Recomputed on the merged crate
        } = krate;
        if self.merged.translated.crate_name.is_empty() {
            self.merged.translated.crate_name = crate_name;
            self.merged.translated.runtime_checks = runtime_checks;
        } else {
            assert_eq!(
                self.merged.translated.runtime_checks, runtime_checks,
                "cannot merge crates with different runtime-check settings"
            );
        }
        self.merged
            .translated
            .target_information
            .extend(target_information);
        self.item_sources
            .extend(item_names.keys().map(|&id| (id, index)));
        self.merged.translated.item_names.extend(item_names);
        // add some padding to align assoc IDs with trait IDs
        let merged = &mut self.merged.translated;
        merged
            .assoc_item_names
            .reserve_slots(merged.trait_decls.slot_count() - merged.assoc_item_names.slot_count());
        merged.assoc_item_names.extend_from_other(assoc_item_names);
        self.merged
            .translated
            .type_decls
            .extend_from_other(type_decls);
        self.merged
            .translated
            .fun_decls
            .extend_from_other(fun_decls);
        self.merged
            .translated
            .global_decls
            .extend_from_other(global_decls);
        self.merged
            .translated
            .trait_decls
            .extend_from_other(trait_decls);
        self.merged
            .translated
            .trait_impls
            .extend_from_other(trait_impls);
    }
}

// =============================================================================================
// Group items that should be merged together
// =============================================================================================

/// Group items by `(key_name, item_kind)`, where `item_key` computes for each item its name for
/// grouping purposes and its key within the group. Returns, for each group, the items in that
/// group indexed by key. If two items in a group have the same key, the group is dropped.
fn discover_groups<K: Clone + Eq + Hash>(
    krate: &TranslatedCrate,
    item_key: impl Fn(ItemId, &Name) -> Option<(Name, K)>,
) -> Vec<SeqHashMap<K, ItemId>> {
    let mut groups_map: SeqHashMap<(Name, std::mem::Discriminant<ItemId>), SeqHashMap<K, ItemId>> =
        SeqHashMap::new();
    for (&item_id, name) in &krate.item_names {
        if let Some((base_name, key)) = item_key(item_id, name) {
            let group_key = (base_name, std::mem::discriminant(&item_id));
            let group = groups_map.entry(group_key).or_default();
            if group.contains_key(&key) {
                // Name collision within the same key: skip this group entirely.
                group.clear();
            } else {
                group.insert(key, item_id);
            }
        }
    }
    // We do a fixpoint: merging a group may lead to detecting that some names are actually the
    // same (because the names refer to impls/types).
    loop {
        let prev_len = groups_map.len();
        let mut remap = Remapping::default();
        for ids in groups_map.values().filter(|ids| !ids.is_empty()) {
            let canonical_id = *ids.values().next().unwrap();
            for &id in ids.values() {
                remap.add_remapping(id, canonical_id);
            }
        }
        for ((mut name, kind), ids) in mem::take(&mut groups_map) {
            name.drive_mut(&mut IdRefMapperVisitor::new(&remap));
            let group_key = (name, kind);
            let group = groups_map.entry(group_key).or_default();
            for (key, item_id) in ids {
                if group.contains_key(&key) {
                    // Name collision within the same key: skip this group entirely.
                    group.clear();
                    break;
                } else {
                    group.insert(key, item_id);
                }
            }
        }
        // Remove empty groups (from collisions) and check for convergence.
        groups_map.retain(|_, v| !v.is_empty());
        if prev_len == groups_map.len() {
            break;
        }
    }
    groups_map.into_values().collect()
}

/// Normalize a name for grouping across crates.
fn normalize_impl_elems(mut name: Name, krate: &TranslatedCrate) -> Name {
    for elem in &mut name.name {
        if let PathElem::Impl(ImplElem::Trait(id)) = elem {
            // Replace impl block references with something that contains the implemented trait
            // predicate instead. That way, comparing names for equality compares trait predicates
            // instead.
            if let Some(timpl) = krate.trait_impls.get(*id) {
                let mut params = GenericParams::default();
                params.trait_clauses.push(TraitParam {
                    clause_id: TraitClauseId::ZERO,
                    span: None,
                    origin: PredicateOrigin::WhereClauseOnImpl,
                    trait_: RegionBinder::empty(timpl.impl_trait.clone()),
                });
                *elem = PathElem::Impl(ImplElem::Ty(Box::new(Binder {
                    params,
                    skip_binder: Ty::mk_unit(),
                    kind: BinderKind::Other,
                })));
            }
        }
    }
    name
}

// =============================================================================================
// Cleanup the merged crate
// =============================================================================================

/// Recompute declaration order and run final whole-crate cleanup on the merged crate.
fn cleanup_post_merge(ctx: &mut TransformCtx) {
    if !ctx.options.translate_all_methods {
        remove_unmentioned_methods(&mut ctx.translated);
    }
    crate::transform::add_missing_info::compute_short_names::Transform.transform_ctx(ctx);
    crate::transform::add_missing_info::reorder_decls::Transform.transform_ctx(ctx);
    if ctx.options.unbind_item_vars {
        crate::transform::simplify_output::unbind_item_vars::Check.transform_ctx(ctx);
    }
}

/// Emulate the behavior of our lazy method translation scheme by removing default trait methods
/// that aren't usefully mentioned anywhere.
fn remove_unmentioned_methods(krate: &mut TranslatedCrate) {
    type MethodKey = (TraitDeclId, TraitMethodId);

    use ReachabilityNode::*;
    #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
    enum ReachabilityNode {
        Root,
        Method(MethodKey),
        Fun(FunDeclId),
    }

    #[derive(Visitor)]
    struct MentionedFunVisitor<F>(F);

    impl<F> VisitAst for MentionedFunVisitor<F>
    where
        F: FnMut(ReachabilityNode),
    {
        fn enter_fun_decl_id(&mut self, id: &FunDeclId) {
            (self.0)(Fun(*id));
        }

        fn enter_fn_ptr(&mut self, fn_ptr: &FnPtr) {
            if let FnPtrKind::Trait(trait_ref, method_id) = fn_ptr.kind.as_ref() {
                (self.0)(Method((trait_ref.trait_id(), *method_id)));
            }
        }
    }

    // Build a graph where the items we want to keep are reachable from the root. To start with
    // that's all the `FunDeclId`s that aren't a method (or a target-dispatch target coming from a
    // method), as well as all the methods without default. We end up with a graph where methods
    // with a default may end up not reachable.
    let graph = {
        let mut graph: DiGraphMap<ReachabilityNode, ()> = DiGraphMap::new();
        graph.add_node(Root);

        for (fun_id, fun) in krate.fun_decls.iter_indexed() {
            let fun_node = Fun(fun_id);
            graph.add_node(fun_node);

            if let FunSource::TraitDefault {
                trait_ref, item_id, ..
            }
            | FunSource::TraitImpl {
                trait_ref, item_id, ..
            } = &fun.src
            {
                let method_key = (trait_ref.id, *item_id);
                // The method node is reachable iff any of the corresponding function nodes is.
                graph.add_edge(Method(method_key), fun_node, ());
                graph.add_edge(fun_node, Method(method_key), ());
            }

            match &fun.src {
                FunSource::TraitDefault { .. }
                | FunSource::TraitImpl { .. }
                | FunSource::TargetDependent { .. } => {}
                // Functions that aren't any of the above are reachable. target-dependent functions
                // will be reachable if their dispatcher is.
                _ => {
                    graph.add_edge(Root, fun_node, ());
                }
            }

            let _ = fun.body.drive(&mut MentionedFunVisitor(|n| {
                graph.add_edge(fun_node, n, ());
            }));
        }

        for trait_decl in krate.trait_decls.iter() {
            for (method_id, method) in trait_decl.methods.iter_enumerated() {
                if method.skip_binder.default.is_none() {
                    graph.add_edge(Root, Method((trait_decl.def_id, method_id)), ());
                }
            }
        }

        graph
    };

    let reachable_nodes: HashSet<_> = Dfs::new(&graph, Root).iter(&graph).collect();

    let mut unused_methods: HashMap<TraitDeclId, HashSet<TraitMethodId>> = HashMap::new();
    // Iterate over unreachable nodes.
    for n in graph.nodes().filter(|n| !reachable_nodes.contains(n)) {
        match n {
            Root => {}
            Method((trait_id, method_id)) => {
                unused_methods
                    .entry(trait_id)
                    .or_default()
                    .insert(method_id);
            }
            Fun(fun_id) => {
                // Remove unreachable functions.
                krate.remove_item(ItemId::Fun(fun_id));
            }
        }
    }
    if unused_methods.is_empty() {
        return;
    }

    // Remove unreachable methods from both decls and impls.
    for trait_impl in krate.trait_impls.iter_mut() {
        let trait_id = trait_impl.impl_trait.id;
        if let Some(unused_methods) = unused_methods.get(&trait_id) {
            trait_impl
                .methods
                .retain(|method_id, _| !unused_methods.contains(&method_id));
        }
    }
    for (trait_id, unused_methods) in unused_methods {
        if let Some(trait_decl) = krate.trait_decls.get_mut(trait_id) {
            trait_decl
                .methods
                .retain(|method_id, _| !unused_methods.contains(&method_id));
        }
    }
}

// =============================================================================================
// Utilities
// =============================================================================================

/// Visitor that remaps references to the given items.
#[derive(Visitor)]
struct IdRefMapperVisitor<'a> {
    map: &'a Remapping,
}

impl<'a> IdRefMapperVisitor<'a> {
    fn new(remap: &'a Remapping) -> Self {
        Self { map: remap }
    }

    fn map<Id>(&self, id: &mut Id)
    where
        Id: Copy,
        Id: Into<ItemId>,
        ItemId: TryInto<Id, Error: Debug>,
    {
        if let Some(&new) = self.map.0.get(&(*id).into()) {
            *id = new.try_into().unwrap();
        }
    }
}

impl VisitAstMut for IdRefMapperVisitor<'_> {
    fn visit_body(&mut self, x: &mut Body) -> ControlFlow<Self::Break> {
        match x {
            // We skip `TargetDispatch` -- only `multi_target` generates them, and it will
            // have IDs we purposefully don't want to remap (since duplication is intended here)
            Body::TargetDispatch(_) => ControlFlow::Continue(()),
            _ => self.visit_inner(x),
        }
    }

    fn enter_type_decl_ref(&mut self, x: &mut TypeDeclRef) {
        self.map(&mut x.id);
    }
    fn enter_fun_decl_ref(&mut self, x: &mut FunDeclRef) {
        self.map(&mut x.id);
    }
    fn enter_global_decl_ref(&mut self, x: &mut GlobalDeclRef) {
        self.map(&mut x.id);
    }
    fn enter_trait_decl_ref(&mut self, x: &mut TraitDeclRef) {
        self.map(&mut x.id);
    }
    fn enter_trait_impl_ref(&mut self, x: &mut TraitImplRef) {
        self.map(&mut x.id);
    }

    fn enter_fn_ptr(&mut self, x: &mut FnPtr) {
        if let FnPtrKind::Fun(id) = x.kind.as_mut() {
            self.map(id)
        }
    }
    fn enter_impl_elem(&mut self, x: &mut ImplElem) {
        if let ImplElem::Trait(id) = x {
            self.map(id);
        }
    }
    fn enter_binder<T: AstVisitable>(&mut self, x: &mut Binder<T>) {
        match &mut x.kind {
            BinderKind::TraitType(trait_id, _) | BinderKind::TraitMethod(trait_id, _) => {
                self.map(trait_id);
            }
            BinderKind::InherentImplBlock | BinderKind::Dyn | BinderKind::Other => {}
        }
    }
}
