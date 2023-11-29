use crate::common::*;
use crate::llbc_ast::*;
use crate::meta::{FileId, FileName};
use crate::rust_to_local_ids::*;
use crate::types::*;
use crate::ullbc_ast::FunDeclId;
use crate::ullbc_ast::GlobalDeclId;
use crate::ullbc_export::{CrateSerializer, DeclarationSerializer, VecSW};
use serde::{Serialize, Serializer};
use std::fs::File;
use std::path::PathBuf;

type CrateSerializer<'a> = GCrateSerializer<'a, FunDecl, GlobalDecl>;

/// Export the translated definitions to a JSON file.
pub fn export(
    crate_name: String,
    ordered_decls: &OrderedDecls,
    type_defs: &TypeDecls,
    fun_defs: &FunDecls,
    global_defs: &GlobalDecls,
    dest_dir: &Option<PathBuf>,
) -> Result<(),()> {
    // Generate the destination file - we use the crate name for the file name
    let mut target_filename = dest_dir
        .as_deref()
        .map_or_else(|| PathBuf::new(), |d| d.to_path_buf().clone());
    target_filename.push(format!("{}.llbc", crate_name));

    trace!("Target file: {:?}", target_filename);

    // Transform the map file id -> file into a vector.
    // Sort the vector to make the serialized file as stable as possible.
    let mut file_ids: Vec<FileId::Id> = ordered_decls.id_to_file.keys().map(|k| *k).collect();
    file_ids.sort();
    let id_to_file: Vec<(FileId::Id, FileName)> = file_ids
        .into_iter()
        .map(|id| (id, ordered_decls.id_to_file.get(&id).unwrap().clone()))
        .collect();
    let id_to_file = VecSW::new(&id_to_file);

    // Serialize
    let crate_serializer = CrateSerializer {
        name: crate_name,
        id_to_file,
        declarations: VecSW::new(&ordered_decls.decls),
        types: &type_defs.types,
        functions: &fun_defs,
        globals: &global_defs,
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
                info!("Generated the file: {}", path.to_str().unwrap());
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
