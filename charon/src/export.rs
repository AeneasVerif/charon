use crate::llbc_ast;
use crate::meta::{FileId, FileName};
use crate::reorder_decls::DeclarationGroup;
use crate::translate_ctx::*;
use crate::types::*;
use crate::ullbc_ast;
use crate::ullbc_ast::{FunDeclId, GlobalDeclId, TraitDecl, TraitImpl};
use serde::Serialize;
use std::fs::File;
use std::path::PathBuf;

/// The data of a generic crate. We serialize this to pass it to `charon-ml`, so this must be as
/// stable as possible. This is used for both ULLBC and LLBC.
#[derive(Serialize)]
#[serde(rename = "Crate")]
pub struct GCrateData<FD, GD> {
    name: String,
    /// The `id_to_file` map is serialized as a vector.
    /// We use this map for the spans: the spans only store the file ids, not
    /// the file names, in order to save space.
    id_to_file: Vec<(FileId::Id, FileName)>,
    declarations: Vec<DeclarationGroup>,
    types: Vec<TypeDecl>,
    functions: Vec<FD>,
    globals: Vec<GD>,
    trait_decls: Vec<TraitDecl>,
    trait_impls: Vec<TraitImpl>,
    #[serde(skip_serializing)]
    /// If there were errors, this contains only a partial description of the input crate.
    has_errors: bool,
}

impl<FD: Serialize + Clone, GD: Serialize + Clone> GCrateData<FD, GD> {
    fn new(
        ctx: &TransCtx,
        crate_name: String,
        fun_decls: &FunDeclId::Map<FD>,
        global_decls: &GlobalDeclId::Map<GD>,
    ) -> Self {
        // Transform the map file id -> file into a vector.
        // Sort the vector to make the serialized file as stable as possible.
        let id_to_file = &ctx.id_to_file;
        let mut file_ids: Vec<FileId::Id> = id_to_file.keys().copied().collect();
        file_ids.sort();
        let id_to_file: Vec<(FileId::Id, FileName)> = file_ids
            .into_iter()
            .map(|id| (id, id_to_file.get(&id).unwrap().clone()))
            .collect();

        // Note that we replace the maps with vectors (the declarations contain
        // their ids, so it is easy to reconstruct the maps from there).
        let declarations = ctx.ordered_decls.clone().unwrap();
        let types = ctx.type_decls.iter().cloned().collect();
        let functions = fun_decls.iter().cloned().collect();
        let globals = global_decls.iter().cloned().collect();
        let trait_decls = ctx.trait_decls.iter().cloned().collect();
        let trait_impls = ctx.trait_impls.iter().cloned().collect();
        GCrateData {
            name: crate_name,
            id_to_file,
            declarations,
            types,
            functions,
            globals,
            trait_decls,
            trait_impls,
            has_errors: ctx.error_count > 0,
        }
    }

    /// Export the translated definitions to a JSON file.
    #[allow(clippy::result_unit_err)]
    pub fn serialize_to_file(&self, dest_dir: &Option<PathBuf>, extension: &str) -> Result<(), ()> {
        // Generate the destination file - we use the crate name for the file name
        let mut target_filename = dest_dir
            .as_deref()
            .map_or_else(PathBuf::new, |d| d.to_path_buf());
        let crate_name = &self.name;
        target_filename.push(format!("{crate_name}.{extension}"));

        trace!("Target file: {:?}", target_filename);

        // Create the directory, if necessary (note that if the target directory
        // is not specified, there is no need to create it: otherwise we
        // couldn't have read the input file in the first place).
        match dest_dir {
            Option::None => (),
            Option::Some(dest_dir) => match std::fs::create_dir_all(dest_dir) {
                std::result::Result::Ok(()) => (),
                std::result::Result::Err(_) => {
                    error!("Could not create the directory: {:?}", dest_dir);
                    return Err(());
                }
            },
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
        // We canonicalize (i.e., make absolute) the path before printing it: this makes it clearer
        // to the user where to find the file.
        let path = std::fs::canonicalize(target_filename).unwrap();
        if self.has_errors {
            info!(
                "Generated the partial (because we encountered errors) file: {}",
                path.to_str().unwrap()
            );
        } else {
            info!("Generated the file: {}", path.to_str().unwrap());
        }
        Ok(())
    }
}

/// Export the translated ULLBC definitions to a JSON file.
#[allow(clippy::result_unit_err)]
pub fn export_ullbc(
    ctx: &TransCtx,
    crate_name: String,
    fun_decls: &ullbc_ast::FunDecls,
    global_decls: &ullbc_ast::GlobalDecls,
    dest_dir: &Option<PathBuf>,
) -> Result<(), ()> {
    GCrateData::new(ctx, crate_name, fun_decls, global_decls).serialize_to_file(dest_dir, "ullbc")
}

/// Export the translated LLBC definitions to a JSON file.
#[allow(clippy::result_unit_err)]
pub fn export_llbc(
    ctx: &TransCtx,
    crate_name: String,
    fun_decls: &llbc_ast::FunDecls,
    global_decls: &llbc_ast::GlobalDecls,
    dest_dir: &Option<PathBuf>,
) -> Result<(), ()> {
    GCrateData::new(ctx, crate_name, fun_decls, global_decls).serialize_to_file(dest_dir, "llbc")
}
