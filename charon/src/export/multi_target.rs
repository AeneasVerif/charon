//! Merging multiple [`CrateData`]s from different compilation targets into one.

use std::cell::RefCell;
use std::collections::HashMap;

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
