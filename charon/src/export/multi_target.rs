//! Merging multiple [`CrateData`]s from different compilation targets into one.
use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt::Debug;
use std::mem;

use itertools::Itertools;

use crate::errors::ErrorCtx;
use crate::ids::IndexVec;
use crate::options::TranslateOptions;
use crate::transform::TransformCtx;
use crate::transform::ctx::TransformPass;
use crate::{ast::*, options::CliOpts};

use super::{CharonVersion, CrateData};

/// Merge per-target [`CrateData`]s into a single [`CrateData`].
pub fn merge(options: CliOpts, krates: Vec<CrateData>) -> CrateData {
    let mut error_ctx = ErrorCtx::new();
    let tr_options = TranslateOptions::new(&mut error_ctx, &options);

    let mut merged = CrateMerger::process(options, krates);

    ItemDeduplicator::dedup(&mut merged.translated, &mut error_ctx);

    // Recompute declaration order on the merged crate.
    let mut ctx = TransformCtx {
        options: tr_options,
        translated: merged.translated,
        errors: RefCell::new(error_ctx),
    };
    crate::transform::add_missing_info::reorder_decls::Transform.transform_ctx(&mut ctx);
    merged.translated = ctx.translated;

    merged
}

// =============================================================================================
// Step 1: Merge a set of crates into one, remembering the source target in the names.
// =============================================================================================

struct CrateMerger {
    merged: CrateData,
    file_name_to_id: HashMap<FileName, FileId>,
}

impl CrateMerger {
    fn process(options: CliOpts, krates: Vec<CrateData>) -> CrateData {
        let mut translated = TranslatedCrate::default();
        translated.options = options;
        let mut merger = CrateMerger {
            merged: CrateData {
                charon_version: CharonVersion(crate::VERSION.to_owned()),
                translated,
                has_errors: false,
            },
            file_name_to_id: HashMap::new(),
        };
        for krate in krates {
            merger.add_one(krate);
        }

        merger.merged
    }

    fn add_one(&mut self, krate: CrateData) {
        let CrateData {
            charon_version: _, // Checked by deserialization already
            translated: mut krate,
            has_errors,
        } = krate;
        self.merged.has_errors |= has_errors;
        let target = krate
            .target_information
            .keys()
            .exactly_one()
            .ok()
            .unwrap()
            .clone();

        // Remap all ids inside `krate`.
        krate.drive_mut(&mut {
            let file_id_map = krate.files.map_ref(|file| {
                if let Some(&existing_id) = self.file_name_to_id.get(&file.name) {
                    existing_id
                } else {
                    let new_id = self.merged.translated.files.push(file.clone());
                    self.file_name_to_id.insert(file.name.clone(), new_id);
                    new_id
                }
            });

            #[derive(Visitor)]
            struct RemapIdsVisitor {
                target: TargetTriple,
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
                fn enter_name(&mut self, name: &mut Name) {
                    name.name.push(PathElem::Target(self.target.clone()));
                }
            }

            RemapIdsVisitor {
                target,
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
            options: _, // We discard the per-target options we made
            target_information,
            item_names,
            short_names: _, // TODO
            files: _,       // Done above
            type_decls,
            fun_decls,
            global_decls,
            trait_decls,
            trait_impls,
            unit_metadata,
            ordered_decls: _, // Recomputed on the merged crate
        } = krate;
        if self.merged.translated.crate_name.is_empty() {
            self.merged.translated.crate_name = crate_name;
        }
        self.merged
            .translated
            .target_information
            .extend(target_information);
        self.merged.translated.item_names.extend(item_names);
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
        if self.merged.translated.unit_metadata.is_none() {
            self.merged.translated.unit_metadata = unit_metadata;
        }
    }
}

// =============================================================================================
// Step 2: Deduplicates items that don't differ across targets and create façades for
// target-dependent functions
// =============================================================================================

generate_index_type!(TargetGroupId, "TargetGroup");

/// A set of items that share the same base name and item kind.
/// These are candidates for merging into a single cross-target item.
struct TargetGroup {
    ids: SeqHashMap<TargetTriple, ItemId>,
}

/// How a `TargetGroup` should be merged.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum MergeDecision {
    /// Don't merge this group.
    Skip,
    /// All the items are the same; merge them into one.
    Dedup,
    /// Function signatures match but bodies diffe; create a façade that dispatches to the
    /// per-target items.
    Facade,
}

impl TargetGroup {
    /// Deterministically chosen representative id.
    fn canonical_id(&self) -> ItemId {
        self.ids.values().next().copied().unwrap()
    }

    /// Whether this group is a group of function items.
    fn is_function_group(&self) -> bool {
        self.canonical_id().is_fun()
    }

    /// Compare the items of this group under the provided id mapping.
    fn decide_merge(
        &self,
        krate: &TranslatedCrate,
        remap: &HashMap<ItemId, ItemId>,
    ) -> MergeDecision {
        let canonical_id = self.canonical_id();
        let items: Vec<Option<ItemByVal>> = self
            .ids
            .values()
            .map(|&id| {
                krate
                    .get_item(id)
                    .map(|item| normalize_item(item.to_owned(), canonical_id, remap))
            })
            .collect_vec();

        // Items that don't exist in the crate can't be compared; if they're all missing we can
        // still merge them tho.
        if items.iter().all(|i| i.is_none()) {
            return MergeDecision::Dedup;
        }
        let items: Vec<_> = match items.into_iter().collect::<Option<Vec<_>>>() {
            Some(items) => items,
            None => return MergeDecision::Skip,
        };

        if items.iter().all_equal() {
            MergeDecision::Dedup
        } else if self.is_function_group()
            && items
                .iter()
                .map(|item| item.as_fun().unwrap())
                .map(|d| (&d.generics, &d.signature))
                .all_equal()
        {
            MergeDecision::Facade
        } else {
            MergeDecision::Skip
        }
    }

    /// Yields `(non_canonical_id, canonical_id)` pairs for building an ID remap.
    fn remap_entries<'a>(&'a self) -> impl Iterator<Item = (ItemId, ItemId)> + 'a {
        self.ids.values().map(|&id| (id, self.canonical_id()))
    }
    fn into_remap_entries(self) -> impl Iterator<Item = (ItemId, ItemId)> {
        let canonical_id = self.canonical_id();
        self.ids.into_values().map(move |id| (id, canonical_id))
    }

    /// Build a façade `FunDecl` for a group of functions with matching signatures but different
    /// bodies. The `def_id` is set to a placeholder and must be fixed up on insertion.
    fn build_facade_decl(&self, def_id: FunDeclId, krate: &TranslatedCrate) -> FunDecl {
        let canonical_fun_id = *self.canonical_id().as_fun().unwrap();
        let canonical = krate.fun_decls.get(canonical_fun_id).unwrap();

        let dispatch_map = self
            .ids
            .iter()
            .map(|(target, &id)| {
                let fun_decl_ref = FunDeclRef {
                    id: *id.as_fun().unwrap(),
                    generics: Box::new(canonical.generics.identity_args()),
                };
                (target.clone(), fun_decl_ref)
            })
            .collect();

        let mut item_meta = canonical.item_meta.clone();
        // Remove the target suffix (and do a little sanity check).
        item_meta.name.name.pop().unwrap().as_target().unwrap();

        FunDecl {
            def_id,
            item_meta,
            generics: canonical.generics.clone(),
            signature: canonical.signature.clone(),
            src: canonical.src.clone(),
            is_global_initializer: canonical.is_global_initializer,
            body: Body::TargetDispatch(dispatch_map),
        }
    }
}

/// Normalize a name for grouping across targets; returns the target.
fn normalize_name_for_grouping(
    name: &Name,
    krate: &TranslatedCrate,
) -> Option<(Name, TargetTriple)> {
    let (mut name, target) = name.strip_target_suffix()?;
    for elem in &mut name.name {
        if let PathElem::Impl(ImplElem::Trait(id)) = elem {
            // Replace ipl block references with something that contains the implemented trait
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
    Some((name, target))
}

/// Orchestrates deduplication of items across compilation targets.
struct ItemDeduplicator<'a> {
    krate: &'a mut TranslatedCrate,
    groups: IndexVec<TargetGroupId, TargetGroup>,
}

impl<'a> ItemDeduplicator<'a> {
    /// Entrypoint: deduplicate items that are the same across targets.
    pub fn dedup(krate: &'a mut TranslatedCrate, errors: &mut ErrorCtx) {
        let groups = Self::discover_groups(krate, errors);
        if groups.is_empty() {
            return;
        }
        let mut this = Self { krate, groups };
        let decisions = this.decide_group_mergings();
        this.apply_merge_decisions(decisions);
    }

    /// Group items by (base_name, item_kind), keeping only groups that have items in all targets.
    fn discover_groups(
        krate: &TranslatedCrate,
        _errors: &mut ErrorCtx,
    ) -> IndexVec<TargetGroupId, TargetGroup> {
        let num_targets = krate.target_information.len();
        let mut groups_map: SeqHashMap<
            (Name, std::mem::Discriminant<ItemId>),
            SeqHashMap<TargetTriple, ItemId>,
        > = SeqHashMap::new();
        for (&item_id, name) in &krate.item_names {
            if let Some((base_name, target)) = normalize_name_for_grouping(name, krate) {
                let key = (base_name, std::mem::discriminant(&item_id));
                let per_target = groups_map.entry(key).or_default();
                if per_target.contains_key(&target) {
                    // Name collision within the same target: skip this group entirely.
                    per_target.clear();
                } else {
                    per_target.insert(target, item_id);
                }
            }
        }
        // We do a fixpoint: merging a group may lead to detecting that some names are actually the
        // same (because the names refer to impls/types).
        loop {
            let prev_len = groups_map.len();
            let remap: HashMap<ItemId, ItemId> = groups_map
                .values()
                .cloned()
                .map(|ids| TargetGroup { ids })
                .flat_map(|g| g.into_remap_entries())
                .filter(|(x, y)| x != y)
                .collect();
            for ((mut name, kind), ids) in mem::take(&mut groups_map) {
                name.drive_mut(&mut IdRefMapperVisitor::new(&remap));
                let key = (name, kind);
                let per_target = groups_map.entry(key).or_default();
                for (target, item_id) in ids {
                    if per_target.contains_key(&target) {
                        // Name collision within the same target: skip this group entirely.
                        per_target.clear();
                        break;
                    } else {
                        per_target.insert(target, item_id);
                    }
                }
            }
            groups_map.retain(|_, v| v.len() == num_targets);
            if prev_len == groups_map.len() {
                break;
            }
        }
        let groups: IndexVec<TargetGroupId, TargetGroup> = groups_map
            .values()
            .filter(|&per_target| per_target.len() == num_targets)
            .cloned()
            .map(|ids| TargetGroup { ids })
            .collect();
        groups
    }

    /// Decide how to merge each group. Skipped groups are not included in the output.
    fn decide_group_mergings(&self) -> Vec<(TargetGroupId, MergeDecision)> {
        // Start with all groups as candidates.
        let mut candidates: Vec<(TargetGroupId, MergeDecision)> = self
            .groups
            .indices()
            .map(|id| (id, MergeDecision::Skip))
            .collect();

        // Fixpoint: assume that all included groups are mapped to a single item; keep the groups
        // that can be merged under such a mapping. Iterate until fixpoint.
        loop {
            let remap = self.build_remap(candidates.iter().map(|(id, _)| id));
            let prev_len = candidates.len();
            candidates.retain_mut(|(idx, decision)| {
                *decision = self.groups[*idx].decide_merge(self.krate, &remap);
                *decision != MergeDecision::Skip
            });
            if candidates.len() == prev_len {
                break;
            }
        }

        candidates
    }

    /// Build an id remap: for each candidate group, map non-canonical IDs → canonical ID.
    fn build_remap<'b>(
        &self,
        candidate_indices: impl IntoIterator<Item = &'b TargetGroupId>,
    ) -> HashMap<ItemId, ItemId> {
        candidate_indices
            .into_iter()
            .flat_map(|&idx| self.groups[idx].remap_entries())
            .filter(|(x, y)| x != y)
            .collect()
    }

    fn apply_merge_decisions(&mut self, decisions: Vec<(TargetGroupId, MergeDecision)>) {
        if decisions.is_empty() {
            return;
        }

        let mut remap = HashMap::new();
        let mut facade_decls: Vec<FunDecl> = Vec::new();
        for &(idx, decision) in &decisions {
            let mut group = &self.groups[idx];
            let target_id = match decision {
                MergeDecision::Skip => unreachable!(),
                MergeDecision::Dedup => {
                    self.dedup_group(idx); // takes mutable borrow; invalidates `group`
                    group = &self.groups[idx];
                    group.canonical_id()
                }
                MergeDecision::Facade => {
                    let facade_id = self.krate.fun_decls.reserve_slot();
                    // Insert facade decls later because the id remapping would mess up the
                    // dispatch maps.
                    facade_decls.push(group.build_facade_decl(facade_id, self.krate));
                    ItemId::Fun(facade_id)
                }
            };
            for &id in group.ids.values() {
                if id != target_id {
                    remap.insert(id, target_id);
                }
            }
        }

        // Remap all ids.
        self.krate.drive_mut(&mut IdRefMapperVisitor::new(&remap));

        for decl in facade_decls {
            self.krate
                .set_new_item_slot(ItemId::Fun(decl.def_id), ItemByVal::Fun(decl));
        }
    }

    fn dedup_group(&mut self, idx: TargetGroupId) {
        let group = &self.groups[idx];
        let canonical = group.canonical_id();

        // Remove the target suffix (and do a little sanity check).
        let mut name = self.krate.item_names.get(&canonical).cloned().unwrap();
        name.name.pop().unwrap().as_target().unwrap();
        if let Some(mut canonical_item) = self.krate.get_item_mut(canonical) {
            canonical_item.item_meta().name = name.clone();
        }
        self.krate.item_names.insert(canonical, name);

        // Merge per-target layouts into the canonical type.
        if let ItemId::Type(canonical_type_id) = canonical {
            let layouts = group
                .ids
                .values()
                .map(|&id| *id.as_type().unwrap())
                .flat_map(|id| {
                    self.krate
                        .type_decls
                        .get_mut(id)
                        .map(|tdecl| mem::take(&mut tdecl.layout))
                        .into_iter()
                        .flatten()
                })
                .collect();
            if let Some(dest) = self.krate.type_decls.get_mut(canonical_type_id) {
                dest.layout = layouts;
            }
        }

        // Remove non-canonical copies.
        for &id in group.ids.values() {
            if id != canonical {
                self.krate.remove_item(id);
            }
        }
    }
}

// =============================================================================================
// Utilities
// =============================================================================================

/// Normalize an item for cross-target comparison.
fn normalize_item(
    mut item: ItemByVal,
    canonical_id: ItemId,
    remap: &HashMap<ItemId, ItemId>,
) -> ItemByVal {
    item.as_mut().drive_mut(&mut IdRefMapperVisitor::new(remap));
    item.as_mut().set_id(canonical_id);
    item.as_mut()
        .item_meta()
        .name
        .name
        .retain(|elem| !matches!(elem, PathElem::Target(_)));
    if let ItemByVal::Type(ty_decl) = &mut item {
        // Layouts are allowed to differ per-target.
        ty_decl.layout.clear();
    }
    item
}

/// Visitor that remaps references to the given items.
#[derive(Visitor)]
struct IdRefMapperVisitor<'a> {
    map: &'a HashMap<ItemId, ItemId>,
}

impl<'a> IdRefMapperVisitor<'a> {
    fn new(remap: &'a HashMap<ItemId, ItemId>) -> Self {
        Self { map: remap }
    }

    fn map<Id>(&self, id: &mut Id)
    where
        Id: Copy,
        Id: Into<ItemId>,
        ItemId: TryInto<Id, Error: Debug>,
    {
        if let Some(&new) = self.map.get(&(*id).into()) {
            *id = new.try_into().unwrap();
        }
    }
}

impl VisitAstMut for IdRefMapperVisitor<'_> {
    fn enter_type_decl_ref(&mut self, x: &mut TypeDeclRef) {
        if let TypeId::Adt(id) = &mut x.id {
            self.map(id);
        }
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

    fn enter_projection_elem(&mut self, x: &mut ProjectionElem) {
        if let ProjectionElem::Field(proj, _) = x
            && let FieldProjKind::Adt(id, _) = proj
        {
            self.map(id);
        }
    }
    fn enter_fn_ptr(&mut self, x: &mut FnPtr) {
        match &mut *x.kind {
            FnPtrKind::Fun(FunId::Regular(id)) => self.map(id),
            FnPtrKind::Trait(_, _, id) => self.map(id),
            _ => {}
        }
    }
    fn enter_trait_method_ref(&mut self, x: &mut TraitMethodRef) {
        self.map(&mut x.method_decl_id);
    }
    fn enter_item_source(&mut self, x: &mut ItemSource) {
        if let ItemSource::VTableMethodPreShim(id, _, _) = x {
            self.map(id);
        }
    }
    fn enter_global_decl(&mut self, x: &mut GlobalDecl) {
        self.map(&mut x.init);
    }
    fn enter_fun_decl(&mut self, x: &mut FunDecl) {
        if let Some(id) = &mut x.is_global_initializer {
            self.map(id);
        }
    }
    fn enter_impl_elem(&mut self, x: &mut ImplElem) {
        if let ImplElem::Trait(id) = x {
            self.map(id);
        }
    }
}
