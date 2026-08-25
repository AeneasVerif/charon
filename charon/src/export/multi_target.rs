//! Merging multiple [`CrateData`]s from different compilation targets into one.
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::fmt::Debug;
use std::mem;

use itertools::Itertools;
use petgraph::prelude::DiGraphMap;
use petgraph::visit::{Dfs, Walker};

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

    let mut ctx = TransformCtx {
        options: tr_options,
        translated: merged.translated,
        errors: RefCell::new(error_ctx),
    };
    cleanup_post_merge(&mut ctx);
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
                fn visit_abort_kind(&mut self, _x: &mut AbortKind) -> ControlFlow<Self::Break> {
                    // Don't modify the name found there
                    ControlFlow::Continue(())
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
            assoc_item_names,
            short_names: _, // TODO
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
        }
        self.merged
            .translated
            .target_information
            .extend(target_information);
        self.merged.translated.item_names.extend(item_names);
        self.merged
            .translated
            .assoc_item_names
            .extend_from_other(assoc_item_names);
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

/// Compares items modulo the target-specific differences we want to ignore.
struct ItemComparer<'a> {
    remap: &'a HashMap<ItemId, ItemId>,
}

impl Visitor for ItemComparer<'_> {
    type Break = ();
}

impl<'a, T: AstVisitable> derive_generic_visitor::VisitTwo<'a, T> for ItemComparer<'_> {
    fn visit(&mut self, left: &'a T, right: &'a T) -> ControlFlow<Self::Break> {
        ZipAst::visit(self, left, right)
    }
}

impl ItemComparer<'_> {
    fn compare_items(&mut self, left: ItemRef<'_>, right: ItemRef<'_>) -> ControlFlow<()> {
        left.drive_two(&right, self)
    }

    fn compare_fun_interface(&mut self, left: &FunDecl, right: &FunDecl) -> ControlFlow<()> {
        self.visit(&left.item_meta.name, &right.item_meta.name)?;
        self.visit(&left.generics, &right.generics)?;
        self.visit(&left.signature, &right.signature)
    }

    fn compare_ids<Id: Copy + Into<ItemId>>(&self, left: &Id, right: &Id) -> ControlFlow<()> {
        let remap = |id: &Id| {
            let id = (*id).into();
            self.remap.get(&id).copied().unwrap_or(id)
        };
        if remap(left) == remap(right) {
            ControlFlow::Continue(())
        } else {
            ControlFlow::Break(())
        }
    }

    fn compare_iters<'a, T: AstVisitable + 'a>(
        &mut self,
        left: impl Iterator<Item = &'a T>,
        right: impl Iterator<Item = &'a T>,
    ) -> ControlFlow<()> {
        derive_generic_visitor::drive_iter_two(left, right, self)
    }
}

// Use lockstep visitation for "equality modulo" comparison.
impl ZipAst for ItemComparer<'_> {
    fn visit_type_decl_id(
        &mut self,
        left: &TypeDeclId,
        right: &TypeDeclId,
    ) -> ControlFlow<Self::Break> {
        self.compare_ids(left, right)
    }

    fn visit_fun_decl_id(
        &mut self,
        left: &FunDeclId,
        right: &FunDeclId,
    ) -> ControlFlow<Self::Break> {
        self.compare_ids(left, right)
    }

    fn visit_global_decl_id(
        &mut self,
        left: &GlobalDeclId,
        right: &GlobalDeclId,
    ) -> ControlFlow<Self::Break> {
        self.compare_ids(left, right)
    }

    fn visit_trait_decl_id(
        &mut self,
        left: &TraitDeclId,
        right: &TraitDeclId,
    ) -> ControlFlow<Self::Break> {
        self.compare_ids(left, right)
    }

    fn visit_trait_impl_id(
        &mut self,
        left: &TraitImplId,
        right: &TraitImplId,
    ) -> ControlFlow<Self::Break> {
        self.compare_ids(left, right)
    }

    fn visit_name(&mut self, left: &Name, right: &Name) -> ControlFlow<Self::Break> {
        let without_target = |elem: &&PathElem| !matches!(elem, PathElem::Target(_));
        self.compare_iters(
            left.name.iter().filter(without_target),
            right.name.iter().filter(without_target),
        )
    }

    fn visit_span(&mut self, _left: &Span, _right: &Span) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    fn visit_attr_info(&mut self, left: &AttrInfo, right: &AttrInfo) -> ControlFlow<Self::Break> {
        let AttrInfo {
            attributes: left_attributes,
            inline: left_inline,
            rename: left_rename,
            public: left_public,
        } = left;
        let AttrInfo {
            attributes: right_attributes,
            inline: right_inline,
            rename: right_rename,
            public: right_public,
        } = right;

        let is_stable = |attr: &&Attribute| !matches!(attr, Attribute::Unknown(attr) if attr.path.starts_with("rustc_"));
        self.compare_iters(
            left_attributes.iter().filter(is_stable),
            right_attributes.iter().filter(is_stable),
        )?;
        self.visit(left_inline, right_inline)?;
        self.visit(left_rename, right_rename)?;
        self.visit(left_public, right_public)
    }

    fn visit_item_meta(&mut self, left: &ItemMeta, right: &ItemMeta) -> ControlFlow<Self::Break> {
        let ItemMeta {
            name: left_name,
            span: left_span,
            // Source text isn't relevant to cross-target identity.
            source_text: _,
            attr_info: left_attr_info,
            is_local: left_is_local,
            opacity: left_opacity,
            lang_item: left_lang_item,
            diagnostic_item: left_diagnostic_item,
        } = left;
        let ItemMeta {
            name: right_name,
            span: right_span,
            source_text: _,
            attr_info: right_attr_info,
            is_local: right_is_local,
            opacity: right_opacity,
            lang_item: right_lang_item,
            diagnostic_item: right_diagnostic_item,
        } = right;

        self.visit(left_name, right_name)?;
        self.visit(left_span, right_span)?;
        self.visit(left_attr_info, right_attr_info)?;
        self.visit(left_is_local, right_is_local)?;
        self.visit(left_opacity, right_opacity)?;
        self.visit(left_lang_item, right_lang_item)?;
        self.visit(left_diagnostic_item, right_diagnostic_item)
    }

    fn visit_type_decl(&mut self, left: &TypeDecl, right: &TypeDecl) -> ControlFlow<Self::Break> {
        let TypeDecl {
            def_id: left_def_id,
            item_meta: left_item_meta,
            generics: left_generics,
            src: left_src,
            kind: left_kind,
            // Layouts are allowed to differ per target.
            layout: _,
            ptr_metadata: left_ptr_metadata,
        } = left;
        let TypeDecl {
            def_id: right_def_id,
            item_meta: right_item_meta,
            generics: right_generics,
            src: right_src,
            kind: right_kind,
            layout: _,
            ptr_metadata: right_ptr_metadata,
        } = right;

        self.visit(left_def_id, right_def_id)?;
        self.visit(left_item_meta, right_item_meta)?;
        self.visit(left_generics, right_generics)?;
        self.visit(left_src, right_src)?;
        self.visit(left_kind, right_kind)?;
        self.visit(left_ptr_metadata, right_ptr_metadata)
    }
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
        let items: Vec<Option<ItemRef<'_>>> = self
            .ids
            .values()
            .map(|&id| krate.get_item(id))
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

        let mut comparer = ItemComparer { remap };
        if items
            .iter()
            .tuple_windows()
            .all(|(&left, &right)| comparer.compare_items(left, right).is_continue())
        {
            MergeDecision::Dedup
        } else if self.is_function_group()
            && items
                .iter()
                .map(|item| item.as_fun().unwrap())
                .tuple_windows()
                .all(|(left, right)| comparer.compare_fun_interface(left, right).is_continue())
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

    /// Group items by (base_name, item_kind). Each group contains the versions of that item
    /// across all targets where it exists.
    fn discover_groups(
        krate: &TranslatedCrate,
        _errors: &mut ErrorCtx,
    ) -> IndexVec<TargetGroupId, TargetGroup> {
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
                .filter(|ids| !ids.is_empty())
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
            // Remove empty groups (from collisions) and check for convergence.
            groups_map.retain(|_, v| !v.is_empty());
            if prev_len == groups_map.len() {
                break;
            }
        }
        let groups: IndexVec<TargetGroupId, TargetGroup> = groups_map
            .into_values()
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
                    // Mark per-target functions as target-dependent.
                    for &id in group.ids.values() {
                        let fun_id = *id.as_fun().unwrap();
                        if let Some(fun_decl) = self.krate.fun_decls.get_mut(fun_id) {
                            fun_decl.src = FunSource::TargetDependent {
                                dispatcher: FunDeclRef {
                                    id: facade_id,
                                    generics: Box::new(fun_decl.generics.identity_args()),
                                },
                            };
                        }
                    }
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
// Step 3: Cleanup the merged crate
// =============================================================================================

/// Recompute declaration order and run final whole-crate cleanup on the merged crate.
fn cleanup_post_merge(ctx: &mut TransformCtx) {
    if !ctx.options.translate_all_methods {
        remove_unmentioned_methods(&mut ctx.translated);
    }
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
    #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
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
        if let Some(id) = x.as_adt_mut() {
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

    fn enter_fn_ptr(&mut self, x: &mut FnPtr) {
        if let FnPtrKind::Fun(FunId::Regular(id)) = x.kind.as_mut() {
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
