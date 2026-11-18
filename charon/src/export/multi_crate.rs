//! Merge several crates of the same build into one, ensuring each translated crate's local items
//! are kept. Allows having many local crates, so that the MIR level is the same across crates (since
//! foreign crates otherwise always use elaborated MIR).
use crate::{ast::*, options::CliOpts};

use super::CrateData;
use super::merge;

/// Merge per-crate [`CrateData`]s into a single [`CrateData`] named `crate_name`.
pub fn merge(options: CliOpts, krates: Vec<CrateData>, crate_name: String) -> CrateData {
    let mut merged = merge::merge(options, krates, MultiCrate);
    merged.translated.crate_name = crate_name;
    merged
}

struct MultiCrate;

impl merge::MergeStrategy for MultiCrate {
    type Key = String;

    fn key(&self, krate: &TranslatedCrate) -> String {
        krate.crate_name.clone()
    }

    /// For each group, keep the local item if there is one, otherwise an arbitrary one.
    fn link(
        &mut self,
        krate: &mut TranslatedCrate,
        groups: Vec<SeqHashMap<String, ItemId>>,
    ) -> merge::Remapping {
        let mut remap = merge::Remapping::default();
        for group in groups {
            let is_local = |id: &ItemId| {
                krate
                    .get_item(*id)
                    .is_some_and(|item| item.item_meta().is_local)
            };
            let locals = group
                .iter()
                .filter(|(_, id)| is_local(id))
                .collect::<Vec<_>>();
            let kept = match *locals.as_slice() {
                [(_, &id)] => id,
                // no local version, take any version (ideally one that has an item)
                [] => group
                    .values()
                    .copied()
                    .min_by_key(|&id| krate.get_item(id).is_none())
                    .unwrap(),
                // local to many (e.g. anon consts), prefer the owner's version
                [(_, &first), ..] => {
                    let owner = match krate.item_name(first).name.first() {
                        Some(PathElem::Ident(name, _)) => Some(name),
                        _ => None,
                    };
                    locals
                        .iter()
                        .find(|(crate_name, _)| Some(*crate_name) == owner)
                        .map_or(first, |&(_, &id)| id)
                }
            };
            for &id in group.values() {
                remap.add_remapping(id, kept);
            }
        }
        for (&id, _) in &remap {
            krate.remove_item(id);
        }
        remap
    }
}
