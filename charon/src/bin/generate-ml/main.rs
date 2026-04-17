//! Generate ocaml deserialization code for our types.
//!
//! This binary runs charon on itself and generates the appropriate `<type>_of_json` functions for
//! our types. The generated functions are inserted into `./generate-ml/GAstOfJson.template.ml` to
//! construct the final `GAstOfJson.ml`.
//!
//! To run it, call `cargo run --bin generate-ml`. It is also run by `make generate-ml` in the
//! crate root. Don't forget to format the output code after regenerating.
#![feature(if_let_guard)]

use anyhow::{Context, Result, bail};
use assert_cmd::cargo::CommandCargoExt;
use charon_lib::ast::*;
use indoc::indoc;
use itertools::Itertools;
use std::collections::{HashMap, HashSet};
use std::fs;
use std::path::PathBuf;
use std::process::Command;

use crate::to_ocaml_ty::DeriveVisitors;
use crate::util::*;

mod of_json;
mod to_ocaml_ty;
mod util;

struct GenerateCtx<'a> {
    crate_data: &'a TranslatedCrate,
    name_to_type: HashMap<String, &'a TypeDecl>,
    /// For each type, list the types it contains.
    type_tree: HashMap<TypeDeclId, HashSet<TypeDeclId>>,
    manual_type_impls: HashMap<TypeDeclId, String>,
    manual_json_impls: HashMap<TypeDeclId, String>,
    opaque_for_visitor: HashSet<TypeDeclId>,
}

impl<'a> GenerateCtx<'a> {
    fn new(
        crate_data: &'a TranslatedCrate,
        manual_type_impls: &[(&str, &str)],
        manual_json_impls: &[(&str, &str)],
        opaque_for_visitor: &[&str],
    ) -> Self {
        let mut name_to_type: HashMap<String, &TypeDecl> = Default::default();
        let mut type_tree = HashMap::default();
        for ty in &crate_data.type_decls {
            let long_name = repr_name(&ty.item_meta.name);
            if long_name.starts_with("charon_lib") {
                let short_name = ty
                    .item_meta
                    .name
                    .name
                    .last()
                    .unwrap()
                    .as_ident()
                    .unwrap()
                    .0
                    .clone();
                name_to_type.insert(short_name, ty);
            }
            name_to_type.insert(long_name, ty);

            let mut contained = HashSet::new();
            ty.dyn_visit(|id: &TypeDeclId| {
                contained.insert(*id);
            });
            type_tree.insert(ty.def_id, contained);
        }

        let mut ctx = GenerateCtx {
            crate_data,
            name_to_type,
            type_tree,
            manual_type_impls: Default::default(),
            manual_json_impls: Default::default(),
            opaque_for_visitor: Default::default(),
        };
        ctx.manual_type_impls = manual_type_impls
            .iter()
            .map(|(name, def)| (ctx.id_from_name(name), def.to_string()))
            .collect();
        ctx.manual_json_impls = manual_json_impls
            .iter()
            .map(|(name, def)| (ctx.id_from_name(name), def.to_string()))
            .collect();
        ctx.opaque_for_visitor = opaque_for_visitor
            .iter()
            .map(|name| ctx.id_from_name(name))
            .collect();
        ctx
    }
}

/// The kind of code generation to perform.
#[derive(Clone, Copy)]
enum GenerationKind {
    OfJson,
    TypeDecl(Option<DeriveVisitors>),
}

/// Replace markers in `template` with auto-generated code.
struct GenerateCodeFor {
    template: PathBuf,
    target: PathBuf,
    /// Each list corresponds to a marker. We replace the ith `__REPLACE{i}__` marker with
    /// generated code for each definition in the ith list.
    ///
    /// Eventually we should reorder definitions so the generated ones are all in one block.
    /// Keeping the order is important while we migrate away from hand-written code.
    markers: Vec<(GenerationKind, HashSet<TypeDeclId>)>,
}

impl GenerateCodeFor {
    fn generate(&self, ctx: &GenerateCtx) -> Result<()> {
        let mut template = fs::read_to_string(&self.template)
            .with_context(|| format!("Failed to read template file {}", self.template.display()))?;
        for (i, (kind, names)) in self.markers.iter().enumerate() {
            let tys = names
                .iter()
                .map(|&id| &ctx.crate_data[id])
                .sorted_by_key(|tdecl| {
                    (
                        tdecl
                            .item_meta
                            .name
                            .name
                            .last()
                            .unwrap()
                            .as_ident()
                            .unwrap(),
                        tdecl.def_id,
                    )
                })
                .collect::<Vec<_>>();
            let generated = match kind {
                GenerationKind::OfJson => ctx.type_decls_to_json(tys),
                GenerationKind::TypeDecl(visitors) => ctx.type_decls_to_ocaml(visitors, tys),
            };
            let placeholder = format!("(* __REPLACE{i}__ *)");
            template = template.replace(&placeholder, &generated);
        }

        fs::write(&self.target, template)
            .with_context(|| format!("Failed to write generated file {}", self.target.display()))?;
        Ok(())
    }
}

fn main() -> Result<()> {
    let dir = PathBuf::from("src/bin/generate-ml");
    let charon_llbc = dir.join("charon-itself.ullbc");
    let reuse_llbc = std::env::var("CHARON_ML_REUSE_LLBC").is_ok(); // Useful when developping
    if !reuse_llbc {
        // Call charon on itself
        let mut cmd = Command::cargo_bin("charon")?;
        cmd.arg("cargo");
        cmd.arg("--hide-marker-traits");
        cmd.arg("--hide-allocator");
        cmd.arg("--treat-box-as-builtin");
        cmd.arg("--ullbc");
        cmd.arg("--start-from=charon_lib::ast::krate::TranslatedCrate");
        cmd.arg("--start-from=charon_lib::ast::ullbc_ast::BodyContents");
        cmd.arg("--exclude=charon_lib::common::hash_by_addr::HashByAddr");
        cmd.arg("--unbind-item-vars");
        cmd.arg("--dest-file");
        cmd.arg(&charon_llbc);
        cmd.arg("--");
        cmd.arg("--lib");
        let output = cmd.output()?;

        if !output.status.success() {
            let stderr = String::from_utf8(output.stderr.clone())?;
            bail!("Compilation failed: {stderr}")
        }
    }

    let crate_data: TranslatedCrate = charon_lib::deserialize_llbc(&charon_llbc)?;
    let output_dir = if std::env::var("IN_CI").as_deref() == Ok("1") {
        dir.join("generated")
    } else {
        dir.join("../../../../charon-ml/src/generated")
    };
    generate_ml(crate_data, dir.join("templates"), output_dir)
}

fn generate_ml(
    crate_data: TranslatedCrate,
    template_dir: PathBuf,
    output_dir: PathBuf,
) -> anyhow::Result<()> {
    let manual_type_impls = &[
        // Hand-written because we replace the `FileId` with the corresponding file.
        ("FileId", "file"),
        (
            "HashConsed",
            "'a0 (* Not actually hash-consed on the OCaml side *)",
        ),
    ];
    let manual_json_impls = &[
        // Hand-written because we interpret it as a list.
        (
            "charon_lib::ids::index_vec::IndexVec",
            "list_of_json arg1_of_json ctx json",
        ),
        // Hand-written because we interpret it as a list.
        (
            "charon_lib::ids::index_map::IndexMap",
            indoc!(
                r#"
                let* list = list_of_json (option_of_json arg1_of_json) ctx json in
                Ok (List.filter_map (fun x -> x) list)
                "#
            ),
        ),
        // Hand-written because we turn it into a list of pairs.
        (
            "indexmap::map::IndexMap",
            "list_of_json (key_value_pair_of_json arg0_of_json arg1_of_json) ctx json",
        ),
        // Hand-written because we replace the `FileId` with the corresponding file name.
        (
            "FileId",
            indoc!(
                r#"
                let* file_id = FileId.id_of_json ctx json in
                let file = FileId.Map.find file_id ctx.id_to_file_map in
                Ok file
                "#,
            ),
        ),
        (
            "HashConsed",
            r#"Error "use `hash_consed_val_of_json` instead""#,
        ), // Not actually used
        (
            "Ty",
            "hash_consed_val_of_json ctx.ty_hashcons_map ty_kind_of_json ctx json",
        ),
        (
            "TraitRef",
            "hash_consed_val_of_json ctx.tref_hashcons_map trait_ref_contents_of_json ctx json",
        ),
    ];
    // Types for which we don't want to generate a type at all.
    let dont_generate_ty = &[
        "ItemOpacity",
        "PredicateOrigin",
        "TraitTypeConstraintId",
        "charon_lib::ids::index_vec::IndexVec",
        "charon_lib::ids::index_map::IndexMap",
    ];
    // Types that we don't want visitors to go into.
    let opaque_for_visitor = &["Name"];
    let ctx = GenerateCtx::new(
        &crate_data,
        manual_type_impls,
        manual_json_impls,
        opaque_for_visitor,
    );

    // Items that we don't want to emit in the generated output.
    let manually_implemented: HashSet<_> = [
        "ItemOpacity",
        "PredicateOrigin",
        "Body",
        "FunDecl",
        "TranslatedCrate",
    ]
    .iter()
    .map(|name| ctx.id_from_name(name))
    .collect();

    // Compute type sets for json deserializers.
    let (gast_types, llbc_types, ullbc_types) = {
        let mut all_types: HashSet<_> = ctx.children_of("TranslatedCrate");
        all_types.insert(ctx.id_from_name("indexmap::map::IndexMap")); // Add this one foreign type

        // (u)llbc types are those that are dominated by the entrypoint of the corresponding
        // module, i.e. those that can't be reached if you remove these entrypoints.
        let non_llbc_types: HashSet<_> =
            ctx.children_of_except("TranslatedCrate", &["charon_lib::ast::llbc_ast::Block"]);
        let non_ullbc_types: HashSet<_> = ctx.children_of_except(
            "TranslatedCrate",
            &[
                "charon_lib::ast::ullbc_ast::BlockData",
                "charon_lib::ast::ullbc_ast::BlockId",
            ],
        );
        let llbc_types: HashSet<_> = all_types.difference(&non_llbc_types).copied().collect();
        let ullbc_types: HashSet<_> = all_types.difference(&non_ullbc_types).copied().collect();

        let shared_types: HashSet<_> = llbc_types.intersection(&ullbc_types).copied().collect();
        let llbc_types: HashSet<_> = llbc_types.difference(&shared_types).copied().collect();
        let ullbc_types: HashSet<_> = ullbc_types.difference(&shared_types).copied().collect();

        let body_specific_types: HashSet<_> = llbc_types.union(&ullbc_types).copied().collect();
        let gast_types: HashSet<_> = all_types
            .difference(&body_specific_types)
            .copied()
            .collect();

        let gast_types: HashSet<_> = gast_types
            .difference(&manually_implemented)
            .copied()
            .collect();
        let llbc_types: HashSet<_> = llbc_types
            .difference(&manually_implemented)
            .copied()
            .collect();
        let ullbc_types: HashSet<_> = ullbc_types
            .difference(&manually_implemented)
            .copied()
            .collect();
        (gast_types, llbc_types, ullbc_types)
    };

    let mut processed_tys: HashSet<TypeDeclId> = dont_generate_ty
        .iter()
        .map(|name| ctx.id_from_name(name))
        .collect();
    // Each call to this will return the children of the listed types that haven't been returned
    // yet. By calling it in dependency order, this allows to organize types into files without
    // having to list them all.
    let mut markers_from_children = |ctx: &GenerateCtx, markers: &[_]| {
        markers
            .iter()
            .copied()
            .map(|(kind, type_names)| {
                let unprocessed_types: HashSet<_> = ctx
                    .children_of_many(type_names)
                    .into_iter()
                    .filter(|&id| processed_tys.insert(id))
                    .collect();
                (kind, unprocessed_types)
            })
            .collect_vec()
    };

    #[rustfmt::skip]
    let generate_code_for = vec![
        GenerateCodeFor {
            template: template_dir.join("Meta.ml"),
            target: output_dir.join("Generated_Meta.ml"),
            markers: markers_from_children(&ctx, &[
                (GenerationKind::TypeDecl(None), &[
                    "File",
                    "Span",
                    "AttrInfo",
                ]),
            ]),
        },
        GenerateCodeFor {
            template: template_dir.join("Values.ml"),
            target: output_dir.join("Generated_Values.ml"),
            markers: markers_from_children(&ctx, &[
                (GenerationKind::TypeDecl(Some(DeriveVisitors {
                    ancestors: &["big_int"],
                    name: "literal",
                    reduce: true,
                    extra_types: &[],
                })), &[
                    "Literal",
                    "IntegerTy",
                    "LiteralTy",
                ]),
            ]),
        },
        GenerateCodeFor {
            template: template_dir.join("Types.ml"),
            target: output_dir.join("Generated_Types.ml"),
            markers: markers_from_children(&ctx, &[
                (GenerationKind::TypeDecl(Some(DeriveVisitors {
                    ancestors: &["literal"],
                    name: "type_vars",
                    reduce: true,
                    extra_types: &[],
                })), &[
                    "TypeVarId",
                    "TraitClauseId",
                    "DeBruijnVar",
                    "ItemId",
                ]),
                // Can't merge into above because aeneas uses the above alongside their own partial
                // copy of `ty`, which causes method type clashes.
                (GenerationKind::TypeDecl(Some(DeriveVisitors {
                    ancestors: &["type_vars"],
                    name: "ty",
                    reduce: false,
                    extra_types: &["span"],
                })), &[
                    "ConstantExpr",
                    "TyKind",
                    "TraitImplRef",
                    "FunDeclRef",
                    "GlobalDeclRef",
                ]),
                // TODO: can't merge into above because of field name clashes (`types`, `regions` etc).
                (GenerationKind::TypeDecl(Some(DeriveVisitors {
                    ancestors: &["ty"],
                    name: "type_decl",
                    reduce: false,
                    extra_types: &[
                        "attr_info"
                    ],
                })), &[
                    "Binder",
                    "TypeDecl",
                ]),
            ]),
        },
        GenerateCodeFor {
            template: template_dir.join("Expressions.ml"),
            target: output_dir.join("Generated_Expressions.ml"),
            markers: markers_from_children(&ctx, &[
                (GenerationKind::TypeDecl(Some(DeriveVisitors {
                    ancestors: &["type_decl"],
                    name: "rvalue",
                    reduce: false,
                    extra_types: &[],
                })), &[
                    "Rvalue",
                ]),
            ]),
        },
        GenerateCodeFor {
            template: template_dir.join("GAst.ml"),
            target: output_dir.join("Generated_GAst.ml"),
            markers: markers_from_children(&ctx, &[
                (GenerationKind::TypeDecl(Some(DeriveVisitors {
                    ancestors: &["rvalue"],
                    name: "fun_sig",
                    reduce: false,
                    extra_types: &[],
                })), &[
                    "Call",
                    "DropKind",
                    "Assert",
                    "ItemSource",
                    "Locals",
                    "FunSig",
                    "CopyNonOverlapping",
                    "Error",
                    "AbortKind",
                ]),
                // These have to be kept separate to avoid field name clashes
                (GenerationKind::TypeDecl(Some(DeriveVisitors {
                    ancestors: &["fun_sig"],
                    name: "global_decl",
                    reduce: false,
                    extra_types: &[],
                })), &[
                    "GlobalDecl",
                ]),
                (GenerationKind::TypeDecl(Some(DeriveVisitors {
                    ancestors: &["global_decl"],
                    name: "trait_decl",
                    reduce: false,
                    extra_types: &[],
                })), &[
                    "TraitDecl",
                ]),
                (GenerationKind::TypeDecl(Some(DeriveVisitors {
                    ancestors: &["trait_decl"],
                    name: "trait_impl",
                    reduce: false,
                    extra_types: &[],
                })), &[
                    "TraitImpl",
                ]),
                (GenerationKind::TypeDecl(None), &[
                    "CliOpts",
                    "GExprBody",
                    "DeclarationGroup",
                ]),
            ]),
        },
        GenerateCodeFor {
            template: template_dir.join("LlbcAst.ml"),
            target: output_dir.join("Generated_LlbcAst.ml"),
            markers: markers_from_children(&ctx, &[
                (GenerationKind::TypeDecl(Some(DeriveVisitors {
                    name: "statement_base",
                    ancestors: &["trait_impl"],
                    reduce: false,
                    extra_types: &[],
                })), &[
                    "charon_lib::ast::llbc_ast::Statement",
                ]),
            ]),
        },
        GenerateCodeFor {
            template: template_dir.join("UllbcAst.ml"),
            target: output_dir.join("Generated_UllbcAst.ml"),
            markers: markers_from_children(&ctx, &[
                (GenerationKind::TypeDecl(Some(DeriveVisitors {
                    ancestors: &["trait_impl"],
                    name: "ullbc_ast",
                    reduce: false,
                    extra_types: &[],
                })), &[
                    "charon_lib::ast::ullbc_ast::BodyContents",
                ]),
            ]),
        },
        GenerateCodeFor {
            template: template_dir.join("GAstOfJson.ml"),
            target: output_dir.join("Generated_GAstOfJson.ml"),
            markers: vec![(GenerationKind::OfJson, gast_types)],
        },
        GenerateCodeFor {
            template: template_dir.join("LlbcOfJson.ml"),
            target: output_dir.join("Generated_LlbcOfJson.ml"),
            markers: vec![(GenerationKind::OfJson, llbc_types)],
        },
        GenerateCodeFor {
            template: template_dir.join("UllbcOfJson.ml"),
            target: output_dir.join("Generated_UllbcOfJson.ml"),
            markers: vec![(GenerationKind::OfJson, ullbc_types)],
        },
    ];
    for file in generate_code_for {
        file.generate(&ctx)?;
    }
    Ok(())
}
