use crate::cfim_ast::*;
use crate::common::*;
use crate::reorder_decls::*;
use crate::types::*;
use crate::values::*;
use serde::{Serialize, Serializer};
use std::collections::HashMap;
use std::fs::File;

/// Serialization wrapper for vectors
pub struct VecSW<T> {
    pub vector: Vec<T>,
}

impl<T> VecSW<T> {
    pub fn new(vector: Vec<T>) -> Self {
        VecSW { vector }
    }
}

impl<T: Serialize> Serialize for VecSW<T> {
    fn serialize<S>(&self, serializer: S) -> std::result::Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serialize_vec(&self.vector, serializer)
    }
}

/// An auxiliary type used for serialization of declarations
#[derive(Serialize)]
#[serde(rename = "DeclarationGroup")]
enum DeclarationSerializer {
    Type(TypeDefId::Id),
    Fun(DefId::Id),
    RecTypes(VecSW<TypeDefId::Id>),
    RecFuns(VecSW<DefId::Id>),
}

type DeclarationsSerializer = VecSW<DeclarationSerializer>;

fn map_declaration(
    type_rid_to_id: &HashMap<rustc_hir::def_id::DefId, TypeDefId::Id>,
    fun_rid_to_id: &HashMap<rustc_hir::def_id::DefId, DefId::Id>,
    decl: &Declaration,
) -> DeclarationSerializer {
    match decl {
        Declaration::Type(id) => DeclarationSerializer::Type(*type_rid_to_id.get(id).unwrap()),
        Declaration::Fun(id) => DeclarationSerializer::Fun(*fun_rid_to_id.get(id).unwrap()),
        Declaration::RecTypes(ids) => {
            let vec = VecSW::new(
                ids.iter()
                    .map(|id| *type_rid_to_id.get(id).unwrap())
                    .collect(),
            );
            DeclarationSerializer::RecTypes(vec)
        }
        Declaration::RecFuns(ids) => {
            let vec = VecSW::new(
                ids.iter()
                    .map(|id| *fun_rid_to_id.get(id).unwrap())
                    .collect(),
            );
            DeclarationSerializer::RecFuns(vec)
        }
    }
}

fn map_declarations(
    type_rid_to_id: &HashMap<rustc_hir::def_id::DefId, TypeDefId::Id>,
    fun_rid_to_id: &HashMap<rustc_hir::def_id::DefId, DefId::Id>,
    decls: &Declarations,
) -> DeclarationsSerializer {
    VecSW::new(
        decls
            .decls
            .iter()
            .map(|decl| map_declaration(type_rid_to_id, fun_rid_to_id, decl))
            .collect(),
    )
}

#[derive(Serialize)]
#[serde(rename = "Module")]
struct ModSerializer<'a> {
    declarations: DeclarationsSerializer,
    types: &'a TypeDefId::Vector<TypeDef>,
    functions: &'a DefId::Vector<FunDef>,
}

/// Export the translated definitions to a JSON file.
pub fn export(
    ordered_decls: &Declarations,
    type_rid_to_id: &HashMap<rustc_hir::def_id::DefId, TypeDefId::Id>,
    type_defs: &TypeDefs,
    fun_rid_to_id: &HashMap<rustc_hir::def_id::DefId, DefId::Id>,
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

    // The groups of declarations use rustc def ids: map them to declarations
    // using our own def ids
    let declarations = map_declarations(type_rid_to_id, fun_rid_to_id, ordered_decls);

    // Serialize
    let mod_serializer = ModSerializer {
        declarations,
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
