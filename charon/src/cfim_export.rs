use crate::cfim_ast::*;
use crate::common::*;
use crate::im_ast::FunDefId;
use crate::rust_to_local_ids::*;
use crate::types::*;
use serde::{Serialize, Serializer};
use std::fs::File;

/// Serialization wrapper for vectors
pub struct VecSW<'a, T> {
    pub vector: &'a Vec<T>,
}

impl<'a, T> VecSW<'a, T> {
    pub fn new(vector: &'a Vec<T>) -> Self {
        VecSW { vector }
    }
}

impl<'a, T: Serialize> Serialize for VecSW<'a, T> {
    fn serialize<S>(&self, serializer: S) -> std::result::Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serialize_vec(self.vector, serializer)
    }
}

/// An auxiliary type used for serialization of declaration groups
type DeclarationsSerializer<'a> = VecSW<'a, DeclarationGroup>;

#[derive(Serialize)]
#[serde(rename = "Module")]
struct ModSerializer<'a> {
    declarations: DeclarationsSerializer<'a>,
    types: &'a TypeDefId::Vector<TypeDef>,
    functions: &'a FunDefId::Vector<FunDef>,
}

/// Export the translated definitions to a JSON file.
pub fn export(
    ordered_decls: &OrderedDecls,
    type_defs: &TypeDefs,
    fun_defs: &FunDefs,
    sourcefile: &str,
) -> Result<()> {
    // Generate the destination file
    // TODO: make this clean
    let target_filename = {
        let len = sourcefile.len();
        assert!(len > 3);
        assert!(&sourcefile[len - 3..] == ".rs");
        let mut target = sourcefile[..len - 2].to_string();
        target.push_str("cfim");
        target
    };

    // Serialize
    let mod_serializer = ModSerializer {
        declarations: VecSW::new(&ordered_decls.decls),
        types: &type_defs.types,
        functions: &fun_defs,
    };

    match File::create(target_filename) {
        std::io::Result::Ok(outfile) => match serde_json::to_writer(&outfile, &mod_serializer) {
            std::result::Result::Ok(()) => Ok(()),
            std::result::Result::Err(_) => Err(()),
        },
        std::io::Result::Err(_) => Err(()),
    }
}
