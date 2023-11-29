use crate::common::*;
use crate::llbc_ast;
use crate::meta::{FileId, FileName};
use crate::reorder_decls::{DeclarationGroup, DeclarationsGroups};
use crate::types::*;
use crate::ullbc_ast;
use crate::ullbc_ast::{FunDeclId, GlobalDeclId, TraitDecl, TraitDecls, TraitImpl, TraitImpls};
use serde::{Serialize, Serializer};
use std::collections::HashMap;
use std::fs::File;
use std::path::PathBuf;

/// A generic crate, which implements the [Serialize] trait
#[derive(Serialize)]
#[serde(rename = "Crate")]
struct GCrateSerializer<'a, FD, GD> {
    name: String,
    /// The `id_to_file` map is serialized as a vector.
    /// We use this map for the spans: the spans only store the file ids, not
    /// the file names, in order to save space.
    id_to_file: &'a Vec<(FileId::Id, FileName)>,
    declarations: &'a Vec<DeclarationGroup>,
    types: Vec<TypeDecl>,
    functions: Vec<FD>,
    globals: Vec<GD>,
    trait_decls: Vec<TraitDecl>,
    trait_impls: Vec<TraitImpl>,
}

/// Export the translated definitions to a JSON file.
///
/// This is a generic function, used both for LLBC and ULLBC.
pub fn gexport<FD: Serialize + Clone, GD: Serialize + Clone>(
    errors: bool,
    crate_name: String,
    id_to_file: &HashMap<FileId::Id, FileName>,
    ordered_decls: &DeclarationsGroups,
    type_defs: &TypeDecls,
    fun_defs: &FunDeclId::Map<FD>,
    global_defs: &GlobalDeclId::Map<GD>,
    trait_decls: &TraitDeclId::Map<TraitDecl>,
    trait_impls: &TraitImplId::Map<TraitImpl>,
    dest_dir: &Option<PathBuf>,
    extension: &str,
) -> Result<(), ()> {
    // Generate the destination file - we use the crate name for the file name
    let mut target_filename = dest_dir
        .as_deref()
        .map_or_else(PathBuf::new, |d| d.to_path_buf());
    target_filename.push(format!("{crate_name}.{extension}"));

    trace!("Target file: {:?}", target_filename);

    // Transform the map file id -> file into a vector.
    // Sort the vector to make the serialized file as stable as possible.
    let mut file_ids: Vec<FileId::Id> = id_to_file.keys().copied().collect();
    file_ids.sort();
    let id_to_file: Vec<(FileId::Id, FileName)> = file_ids
        .into_iter()
        .map(|id| (id, id_to_file.get(&id).unwrap().clone()))
        .collect();
    let id_to_file = &id_to_file;

    // Serialize
    // Note that we replace the maps with vectors (the declarations contain
    // their ids, so it is easy to reconstruct the maps from there).
    let types = type_defs.iter().cloned().collect();
    let functions = fun_defs.iter().cloned().collect();
    let globals = global_defs.iter().cloned().collect();
    let trait_decls = trait_decls.iter().cloned().collect();
    let trait_impls = trait_impls.iter().cloned().collect();
    let crate_serializer = GCrateSerializer {
        name: crate_name,
        id_to_file,
        declarations: ordered_decls,
        types,
        functions,
        globals,
        trait_decls,
        trait_impls,
    };

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

    // Write to the file
    match File::create(target_filename.clone()) {
        std::io::Result::Ok(outfile) => match serde_json::to_writer(&outfile, &crate_serializer) {
            std::result::Result::Ok(()) => {
                // We canonicalize (i.e., make absolute) the path before printing it:
                // this makes it clearer to the user where to find the file.
                let path = std::fs::canonicalize(target_filename).unwrap();
                if errors {
                    info!(
                        "Generated the partial (because we encountered errors) file: {}",
                        path.to_str().unwrap()
                    );
                } else {
                    info!("Generated the file: {}", path.to_str().unwrap());
                }
                Ok(())
            }
            std::result::Result::Err(_) => {
                error!("Could not write to: {:?}", target_filename);
                Err(())
            }
        },
        std::io::Result::Err(_) => {
            error!("Could not open: {:?}", target_filename);
            Err(())
        }
    }
}

/// Export the translated ULLBC definitions to a JSON file.
pub fn export_ullbc(
    errors: bool,
    crate_name: String,
    id_to_file: &HashMap<FileId::Id, FileName>,
    ordered_decls: &DeclarationsGroups,
    type_defs: &TypeDecls,
    fun_defs: &ullbc_ast::FunDecls,
    global_defs: &ullbc_ast::GlobalDecls,
    trait_decls: &TraitDecls,
    trait_impls: &TraitImpls,
    dest_dir: &Option<PathBuf>,
) -> Result<(), ()> {
    gexport(
        errors,
        crate_name,
        id_to_file,
        ordered_decls,
        type_defs,
        fun_defs,
        global_defs,
        trait_decls,
        trait_impls,
        dest_dir,
        "ullbc",
    )
}

/// Export the translated LLBC definitions to a JSON file.
pub fn export_llbc(
    errors: bool,
    crate_name: String,
    id_to_file: &HashMap<FileId::Id, FileName>,
    ordered_decls: &DeclarationsGroups,
    type_defs: &TypeDecls,
    fun_defs: &llbc_ast::FunDecls,
    global_defs: &llbc_ast::GlobalDecls,
    trait_decls: &TraitDecls,
    trait_impls: &TraitImpls,
    dest_dir: &Option<PathBuf>,
) -> Result<(), ()> {
    gexport(
        errors,
        crate_name,
        id_to_file,
        ordered_decls,
        type_defs,
        fun_defs,
        global_defs,
        trait_decls,
        trait_impls,
        dest_dir,
        "llbc",
    )
}
