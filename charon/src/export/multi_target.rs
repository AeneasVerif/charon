//! Merging multiple [`CrateData`]s from different compilation targets into one.
use std::collections::HashMap;
use std::mem;

use itertools::Itertools;

use crate::ids::IndexVec;
use crate::{ast::*, options::CliOpts};

use super::CrateData;
use super::merge;

/// Merge per-target [`CrateData`]s into a single [`CrateData`].
pub fn merge(options: CliOpts, krates: Vec<CrateData>) -> CrateData {
    merge::merge(options, krates, MultiTarget)
}

struct MultiTarget;

impl merge::MergeStrategy for MultiTarget {
    type Key = TargetTriple;

    fn key(&self, krate: &TranslatedCrate) -> TargetTriple {
        krate
            .target_information
            .keys()
            .exactly_one()
            .ok()
            .unwrap()
            .clone()
    }

    /// Remember the source target in the names.
    fn name_suffix(&self, target: &TargetTriple) -> Option<PathElem> {
        Some(PathElem::Target(target.clone()))
    }

    /// Entrypoint: deduplicate items that are the same across targets. Each group contains the
    /// versions of an item across all targets where it exists. Returns how to remap item ids.
    fn link(
        &mut self,
        krate: &mut TranslatedCrate,
        groups: Vec<SeqHashMap<TargetTriple, ItemId>>,
    ) -> merge::Remapping {
        let groups = groups.into_iter().map(|ids| TargetGroup { ids }).collect();
        let mut dedup = ItemDeduplicator { krate, groups };
        let decisions = dedup.decide_group_mergings();
        dedup.apply_merge_decisions(decisions)
    }
}

// =============================================================================================
// Deduplicates items that don't differ across targets and create façades for
// target-dependent functions
// =============================================================================================

generate_index_type!(TargetGroupId, "TargetGroup");

/// A set of items that share the same base name and item kind.
/// These are candidates for merging into a single cross-target item.
struct TargetGroup {
    ids: SeqHashMap<TargetTriple, ItemId>,
}

/// How a `TargetGroup` should be merged.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
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
            started_from: left_started_from,
            is_extern: left_is_extern,
            opacity: left_opacity,
            lang_item: left_lang_item,
            diagnostic_item: left_diagnostic_item,
            has_errors: left_has_errors,
        } = left;
        let ItemMeta {
            name: right_name,
            span: right_span,
            source_text: _,
            attr_info: right_attr_info,
            is_local: right_is_local,
            started_from: right_started_from,
            is_extern: right_is_extern,
            opacity: right_opacity,
            lang_item: right_lang_item,
            diagnostic_item: right_diagnostic_item,
            has_errors: right_has_errors,
        } = right;

        self.visit(left_name, right_name)?;
        self.visit(left_span, right_span)?;
        self.visit(left_attr_info, right_attr_info)?;
        self.visit(left_is_local, right_is_local)?;
        self.visit(left_started_from, right_started_from)?;
        self.visit(left_is_extern, right_is_extern)?;
        self.visit(left_opacity, right_opacity)?;
        self.visit(left_lang_item, right_lang_item)?;
        self.visit(left_diagnostic_item, right_diagnostic_item)?;
        self.visit(left_has_errors, right_has_errors)?;
        ControlFlow::Continue(())
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
            monomorphic_layouts: _,
            ptr_metadata: left_ptr_metadata,
            marker_traits: left_marker_traits,
        } = left;
        let TypeDecl {
            def_id: right_def_id,
            item_meta: right_item_meta,
            generics: right_generics,
            src: right_src,
            kind: right_kind,
            layout: _,
            monomorphic_layouts: _,
            ptr_metadata: right_ptr_metadata,
            marker_traits: right_marker_traits,
        } = right;

        self.visit(left_def_id, right_def_id)?;
        self.visit(left_item_meta, right_item_meta)?;
        self.visit(left_generics, right_generics)?;
        self.visit(left_src, right_src)?;
        self.visit(left_kind, right_kind)?;
        self.visit(left_ptr_metadata, right_ptr_metadata)?;
        self.visit(left_marker_traits, right_marker_traits)
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
        let canonical_id = self.canonical_id();
        self.ids.values().map(move |&id| (id, canonical_id))
    }

    /// Build a façade `FunDecl` for a group of functions with matching signatures but different
    /// bodies.
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
/// Orchestrates deduplication of items across compilation targets.
struct ItemDeduplicator<'a> {
    krate: &'a mut TranslatedCrate,
    groups: IndexVec<TargetGroupId, TargetGroup>,
}

impl<'a> ItemDeduplicator<'a> {
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

    fn apply_merge_decisions(
        &mut self,
        decisions: Vec<(TargetGroupId, MergeDecision)>,
    ) -> merge::Remapping {
        let mut remap = merge::Remapping::default();
        for &(idx, decision) in &decisions {
            let group = &self.groups[idx];
            let target_id = match decision {
                MergeDecision::Skip => unreachable!(),
                MergeDecision::Dedup => {
                    let canonical_id = group.canonical_id();
                    self.dedup_group(idx);
                    canonical_id
                }
                MergeDecision::Facade => {
                    let facade_id = self.krate.fun_decls.reserve_slot();
                    let facade_decl = group.build_facade_decl(facade_id, self.krate);
                    self.krate
                        .set_new_item_slot(ItemId::Fun(facade_id), ItemByVal::Fun(facade_decl));
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
            let group = &self.groups[idx];
            for &id in group.ids.values() {
                remap.add_remapping(id, target_id);
            }
        }

        remap
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
            let mut layouts = TargetLayouts::default();
            let mut mono_layouts: SeqHashMap<GenericArgs, TargetLayouts> = SeqHashMap::new();
            for &id in group.ids.values() {
                if let Some(tdecl) = self.krate.type_decls.get_mut(*id.as_type().unwrap()) {
                    layouts.extend(mem::take(&mut tdecl.layout.0));
                    for (args, layouts) in mem::take(&mut tdecl.monomorphic_layouts) {
                        mono_layouts.entry(args).or_default().extend(layouts.0);
                    }
                }
            }
            if let Some(dest) = self.krate.type_decls.get_mut(canonical_type_id) {
                dest.layout = layouts;
                dest.monomorphic_layouts = mono_layouts;
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
