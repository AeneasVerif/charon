use crate::ids::Map;
use crate::llbc_ast;
use crate::meta::{FileId, FileName};
use crate::reorder_decls::DeclarationGroup;
use crate::translate_ctx::*;
use crate::types::*;
use crate::ullbc_ast;
use crate::ullbc_ast::{FunDeclId, GlobalDeclId, TraitDecl, TraitImpl};
use serde::{Deserialize, Serialize};
use std::fs::File;
use std::path::Path;

/// The data of a generic crate. We serialize this to pass it to `charon-ml`, so this must be as
/// stable as possible. This is used for both ULLBC and LLBC.
#[derive(Serialize, Deserialize)]
#[serde(rename = "Crate")]
pub struct GCrateData<FD, GD> {
    /// The version of charon currently being used. `charon-ml` inspects this and errors if it is
    /// trying to read an incompatible version (for now we compare versions for equality).
    pub charon_version: String,
    /// Crate name.
    pub name: String,
    /// The `id_to_file` map is serialized as a vector.
    /// We use this map for the spans: the spans only store the file ids, not
    /// the file names, in order to save space.
    pub id_to_file: Vec<(FileId, FileName)>,
    pub declarations: Vec<DeclarationGroup>,
    pub types: Vec<TypeDecl>,
    pub functions: Vec<FD>,
    pub globals: Vec<GD>,
    pub trait_decls: Vec<TraitDecl>,
    pub trait_impls: Vec<TraitImpl>,
    #[serde(skip)]
    /// If there were errors, this contains only a partial description of the input crate.
    pub has_errors: bool,
}

impl<FD: Serialize + Clone, GD: Serialize + Clone> GCrateData<FD, GD> {
    pub fn new(
        ctx: &TransformCtx,
        fun_decls: &Map<FunDeclId, FD>,
        global_decls: &Map<GlobalDeclId, GD>,
    ) -> Self {
        // Transform the map file id -> file into a vector.
        // Sort the vector to make the serialized file as stable as possible.
        let id_to_file = &ctx.translated.id_to_file;
        let mut file_ids: Vec<FileId> = id_to_file.keys().copied().collect();
        file_ids.sort();
        let id_to_file: Vec<(FileId, FileName)> = file_ids
            .into_iter()
            .map(|id| (id, id_to_file.get(&id).unwrap().clone()))
            .collect();

        // Note that we replace the maps with vectors (the declarations contain
        // their ids, so it is easy to reconstruct the maps from there).
        let declarations = ctx.translated.ordered_decls.clone().unwrap();
        let types = ctx.translated.type_decls.iter().cloned().collect();
        let functions = fun_decls.iter().cloned().collect();
        let globals = global_decls.iter().cloned().collect();
        let trait_decls = ctx.translated.trait_decls.iter().cloned().collect();
        let trait_impls = ctx.translated.trait_impls.iter().cloned().collect();
        GCrateData {
            charon_version: crate::VERSION.to_owned(),
            name: ctx.translated.crate_name.clone(),
            id_to_file,
            declarations,
            types,
            functions,
            globals,
            trait_decls,
            trait_impls,
            has_errors: ctx.has_errors(),
        }
    }

    /// Export the translated definitions to a JSON file.
    #[allow(clippy::result_unit_err)]
    pub fn serialize_to_file(&self, target_filename: &Path) -> Result<(), ()> {
        // Create the directory, if necessary (note that if the target directory
        // is not specified, there is no need to create it: otherwise we
        // couldn't have read the input file in the first place).
        let target_dir = target_filename.parent().unwrap();
        match std::fs::create_dir_all(target_dir) {
            std::result::Result::Ok(()) => (),
            std::result::Result::Err(_) => {
                error!("Could not create the directory: {:?}", target_dir);
                return Err(());
            }
        };

        // Create the file.
        let std::io::Result::Ok(outfile) = File::create(target_filename.clone()) else {
            error!("Could not open: {:?}", target_filename);
            return Err(())
        };
        // Write to the file.
        let std::result::Result::Ok(()) = serde_json::to_writer(&outfile, self) else {
            error!("Could not write to: {:?}", target_filename);
            return Err(());
        };

        // We canonicalize (i.e., make absolute) the path before printing it; this makes it clearer
        // to the user where to find the file.
        let target_filename = std::fs::canonicalize(target_filename).unwrap();
        if self.has_errors {
            info!(
                "Generated the partial (because we encountered errors) file: {}",
                target_filename.to_str().unwrap()
            );
        } else {
            info!("Generated the file: {}", target_filename.to_str().unwrap());
        }
        Ok(())
    }
}

/// The two kinds of crate data we construct.
pub enum CrateData {
    ULLBC(GCrateData<ullbc_ast::FunDecl, ullbc_ast::GlobalDecl>),
    LLBC(GCrateData<llbc_ast::FunDecl, llbc_ast::GlobalDecl>),
}

impl CrateData {
    pub fn new_ullbc(ctx: &TransformCtx) -> Self {
        Self::ULLBC(GCrateData::new(
            ctx,
            &ctx.translated.fun_decls,
            &ctx.translated.global_decls,
        ))
    }

    pub fn new_llbc(ctx: &TransformCtx) -> Self {
        Self::LLBC(GCrateData::new(
            ctx,
            &ctx.translated.structured_fun_decls,
            &ctx.translated.structured_global_decls,
        ))
    }

    /// Export the translated definitions to a JSON file.
    #[allow(clippy::result_unit_err)]
    pub fn serialize_to_file(&self, dest_file: &Path) -> Result<(), ()> {
        match self {
            CrateData::ULLBC(crate_data) => crate_data.serialize_to_file(dest_file),
            CrateData::LLBC(crate_data) => crate_data.serialize_to_file(dest_file),
        }
    }
}
