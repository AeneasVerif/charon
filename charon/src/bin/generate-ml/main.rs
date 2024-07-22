//! Generate ocaml deserialization code for our types.
//!
//! This binary runs charon on itself and generates the appropriate `<type>_of_json` functions for
//! our types. The generated functions are inserted into `./generate-ml/GAstOfJson.template.ml` to
//! construct the final `GAstOfJson.ml`.
//!
//! To run it, call `cargo run --bin generate-ml`. It is also run by `make generate-ml` in the
//! crate root. Don't forget to format the output code after regenerating.
use anyhow::{bail, Context, Result};
use assert_cmd::cargo::CommandCargoExt;
use charon_lib::export::CrateData;
use charon_lib::meta::ItemMeta;
use charon_lib::names::{Name, PathElem};
use charon_lib::types::{
    AssumedTy, Field, LiteralTy, Ty, TypeDecl, TypeDeclId, TypeDeclKind, TypeId,
};
use convert_case::{Case, Casing};
use derive_visitor::Drive;
use itertools::Itertools;
use std::collections::HashMap;
use std::fs;
use std::fs::File;
use std::io::BufReader;
use std::path::PathBuf;
use std::process::Command;

/// `Name` is a complex datastructure; to inspect it we serialize it a little bit.
fn repr_name(_crate_data: &CrateData, n: &Name) -> String {
    n.name
        .iter()
        .map(|path_elem| match path_elem {
            PathElem::Ident(i, _) => i.clone(),
            PathElem::Impl(..) => "<impl>".to_string(),
        })
        .join("::")
}

fn make_ocaml_ident(name: &str) -> String {
    let mut name = name.to_case(Case::Snake);
    if matches!(
        &*name,
        "virtual" | "bool" | "char" | "struct" | "type" | "let" | "fun" | "open" | "rec"
    ) {
        name += "_";
    }
    name
}
fn type_name_to_ocaml_ident(item_meta: &ItemMeta) -> String {
    let name = item_meta
        .attr_info
        .rename
        .as_ref()
        .unwrap_or(item_meta.name.name.last().unwrap().as_ident().0);
    make_ocaml_ident(name)
}

/// Traverse all types to figure out which ones transitively contain the given id.
fn contains_id(crate_data: &CrateData, haystack: TypeDeclId) -> HashMap<TypeDeclId, bool> {
    enum ContainsRawSpan {
        Yes,
        No,
        Processing,
    }
    use ContainsRawSpan::*;
    fn traverse_ty(
        crate_data: &CrateData,
        ty: &TypeDecl,
        map: &mut HashMap<TypeDeclId, ContainsRawSpan>,
    ) -> bool {
        match map.get(&ty.def_id) {
            Some(Yes) => return true,
            Some(No | Processing) => return false,
            None => {}
        }
        map.insert(ty.def_id, Processing);
        let mut contains = false;
        ty.drive(&mut derive_visitor::visitor_enter_fn(|id: &TypeDeclId| {
            if let Some(ty) = crate_data.types.iter().find(|ty| ty.def_id == *id) {
                if traverse_ty(crate_data, ty, map) {
                    contains = true;
                }
            }
        }));
        map.insert(ty.def_id, if contains { Yes } else { No });
        contains
    }
    let mut map = HashMap::new();
    map.insert(haystack, Yes);
    for ty in &crate_data.types {
        traverse_ty(crate_data, ty, &mut map);
    }
    map.into_iter()
        .map(|(id, x)| (id, matches!(x, Yes)))
        .collect()
}

struct GenerateCtx {
    crate_data: CrateData,
    contains_raw_span: HashMap<TypeDeclId, bool>,
}

/// Converts a type to the appropriate `*_of_json` call. In case of generics, this combines several
/// functions, e.g. `list_of_json bool_of_json`.
fn type_to_ocaml_call(ctx: &GenerateCtx, ty: &Ty) -> String {
    match ty {
        Ty::Literal(LiteralTy::Bool) => "bool_of_json".to_string(),
        Ty::Literal(LiteralTy::Char) => "char_of_json".to_string(),
        Ty::Literal(LiteralTy::Integer(_)) => "int_of_json".to_string(),
        Ty::Adt(adt_kind, generics) => {
            let mut expr = Vec::new();
            let mut types = generics.types.as_slice();
            match adt_kind {
                TypeId::Adt(id) => {
                    let adt: &TypeDecl = &ctx.crate_data.types[id.index()];
                    let mut first = type_name_to_ocaml_ident(&adt.item_meta);
                    if first == "vec" {
                        first = "list".to_string();
                        types = &types[0..1]; // Remove the allocator generic param
                    }
                    expr.push(first + "_of_json");
                }
                TypeId::Assumed(AssumedTy::Box) => {
                    types = &types[0..1]; // Remove the allocator generic param
                }
                TypeId::Tuple => {
                    let name = match types.len() {
                        2 => "pair_of_json".to_string(),
                        3 => "triple_of_json".to_string(),
                        len => format!("tuple_{len}_of_json"),
                    };
                    expr.push(name);
                }
                _ => unimplemented!("{ty:?}"),
            }
            for ty in types {
                expr.push(type_to_ocaml_call(ctx, ty))
            }
            if let TypeId::Adt(id) = adt_kind {
                if *ctx.contains_raw_span.get(&id).unwrap() {
                    expr.push("id_to_file".to_string())
                }
            }
            expr.into_iter().map(|f| format!("({f})")).join(" ")
        }
        Ty::TypeVar(var_id) => format!("arg{}_of_json", var_id.index()),
        // Ty::Ref(_, _, _) => todo!(),
        _ => unimplemented!("{ty:?}"),
    }
}

fn convert_vars<'a>(ctx: &GenerateCtx, fields: impl IntoIterator<Item = &'a Field>) -> String {
    fields
        .into_iter()
        .filter(|f| !f.is_opaque())
        .map(|f| {
            let name = f.name.as_deref().unwrap();
            let rename = f.renamed_name().unwrap();
            let convert = type_to_ocaml_call(ctx, &f.ty);
            format!("let* {rename} = {convert} {name} in")
        })
        .join("\n")
}

fn build_branch<'a>(
    ctx: &GenerateCtx,
    pat: &str,
    fields: impl IntoIterator<Item = &'a Field>,
    construct: &str,
) -> String {
    let convert = convert_vars(ctx, fields);
    format!("| {pat} -> {convert} Ok ({construct})")
}

fn build_function(ctx: &GenerateCtx, decl: &TypeDecl, branches: &str) -> String {
    let ty_name = type_name_to_ocaml_ident(&decl.item_meta);
    let contains_raw_span = *ctx.contains_raw_span.get(&decl.def_id).unwrap();
    let signature = if decl.generics.types.is_empty() {
        let id_to_file = if contains_raw_span {
            "(id_to_file : id_to_file_map) "
        } else {
            ""
        };
        format!("{ty_name}_of_json {id_to_file}(js : json) : ({ty_name}, string) result =")
    } else {
        let types = &decl.generics.types;
        let gen_vars_space = types
            .iter()
            .enumerate()
            .map(|(i, _)| format!("'a{i}"))
            .join(" ");
        let gen_vars_comma = types
            .iter()
            .enumerate()
            .map(|(i, _)| format!("'a{i}"))
            .join(", ");

        let mut args = Vec::new();
        let mut ty_args = Vec::new();
        for (i, _) in types.iter().enumerate() {
            args.push(format!("arg{i}_of_json"));
            ty_args.push(format!("(json -> ('a{i}, string) result)"));
        }
        if contains_raw_span {
            args.push("id_to_file".to_string());
            ty_args.push("id_to_file_map".to_string());
        }
        args.push("js".to_string());
        ty_args.push("json".to_string());

        let ty_args = ty_args.into_iter().join(" -> ");
        let args = args.into_iter().join(" ");
        let fun_ty =
            format!("{gen_vars_space}. {ty_args} -> (({gen_vars_comma}) {ty_name}, string) result");
        format!("{ty_name}_of_json : {fun_ty} = fun {args} ->")
    };
    format!(
        r#"
        and {signature}
          combine_error_msgs js __FUNCTION__
            (match js with{branches} | _ -> Error "")
        "#
    )
}

fn type_decl_to_json_deserializer(ctx: &GenerateCtx, decl: &TypeDecl) -> String {
    let branches = match &decl.kind {
        TypeDeclKind::Struct(fields) if fields.is_empty() => {
            build_branch(ctx, "`Null", fields, "()")
        }
        TypeDeclKind::Struct(fields)
            if fields.len() == 1
                && decl
                    .item_meta
                    .attr_info
                    .attributes
                    .iter()
                    .any(|a| a.is_unknown() && a.as_unknown() == "serde(transparent)") =>
        {
            let ty = &fields[0].ty;
            let call = type_to_ocaml_call(ctx, ty);
            format!("| x -> {call} x")
        }
        TypeDeclKind::Alias(ty) => {
            let call = type_to_ocaml_call(ctx, ty);
            format!("| x -> {call} x")
        }
        TypeDeclKind::Struct(fields) if fields.iter().all(|f| f.name.is_none()) => {
            let mut fields = fields.clone();
            for (i, f) in fields.iter_mut().enumerate() {
                f.name = Some(format!("x{i}"));
            }
            let pat: String = fields.iter().map(|f| f.name.as_deref().unwrap()).join(";");
            let pat = format!("`List [ {pat} ]");
            let construct = fields.iter().map(|f| f.renamed_name().unwrap()).join(", ");
            let construct = format!("( {construct} )");
            build_branch(ctx, &pat, &fields, &construct)
        }
        TypeDeclKind::Struct(fields) => {
            let pat: String = fields
                .iter()
                .map(|f| {
                    let name = f.name.as_ref().unwrap();
                    let var = if f.is_opaque() { "_" } else { name };
                    format!("(\"{name}\", {var});")
                })
                .join("\n");
            let pat = format!("`Assoc [ {pat} ]");
            let construct = fields
                .iter()
                .filter(|f| !f.is_opaque())
                .map(|f| f.renamed_name().unwrap())
                .join("; ");
            let construct = format!("{{ {construct} }}");
            build_branch(ctx, &pat, fields, &construct)
        }
        TypeDeclKind::Enum(variants) => {
            variants
                .iter()
                .filter(|v| !v.is_opaque())
                .map(|variant| {
                    let name = &variant.name;
                    let rename = variant.renamed_name();
                    if variant.fields.is_empty() {
                        // Unit variant
                        let pat = format!("`String \"{name}\"");
                        build_branch(ctx, &pat, &variant.fields, rename)
                    } else {
                        let mut fields = variant.fields.clone();
                        let inner_pat = if fields.iter().all(|f| f.name.is_none()) {
                            // Tuple variant
                            if variant.fields.len() == 1 {
                                let var = make_ocaml_ident(&variant.name);
                                fields[0].name = Some(var.clone());
                                var
                            } else {
                                for (i, f) in fields.iter_mut().enumerate() {
                                    f.name = Some(format!("x{i}"));
                                }
                                let pat =
                                    fields.iter().map(|f| f.name.as_ref().unwrap()).join("; ");
                                format!("`List [ {pat} ]")
                            }
                        } else {
                            // Struct variant
                            let pat = fields
                                .iter()
                                .map(|f| {
                                    let name = f.name.as_ref().unwrap();
                                    let var = if f.is_opaque() { "_" } else { name };
                                    format!("(\"{name}\", {var});")
                                })
                                .join(" ");
                            format!("`Assoc [ {pat} ]")
                        };
                        let pat = format!("`Assoc [ (\"{name}\", {inner_pat}) ]");
                        let construct_fields =
                            fields.iter().map(|f| f.name.as_ref().unwrap()).join(", ");
                        let construct = format!("{rename} ({construct_fields})");
                        build_branch(ctx, &pat, &fields, &construct)
                    }
                })
                .join("\n")
        }
        TypeDeclKind::Opaque => todo!(),
        TypeDeclKind::Error(_) => todo!(),
    };
    build_function(ctx, decl, &branches)
}

fn main() -> Result<()> {
    let dir = PathBuf::from("src/bin/generate-ml");
    let charon_llbc = dir.join("charon-itself.llbc");
    const RUN_CHARON: bool = true;
    if RUN_CHARON {
        // Call charon on itself
        let mut cmd = Command::cargo_bin("charon")?;
        cmd.arg("--cargo-arg=--lib");
        cmd.arg("--errors-as-warnings");
        cmd.arg("--dest-file");
        cmd.arg(&charon_llbc);
        let output = cmd.output()?;

        if !output.status.success() {
            let stderr = String::from_utf8(output.stderr.clone())?;
            bail!("Compilation failed: {stderr}")
        }
    }

    let crate_data: CrateData = {
        use serde::Deserialize;
        let file = File::open(&charon_llbc)
            .with_context(|| format!("Failed to read llbc file {}", charon_llbc.display()))?;
        let reader = BufReader::new(file);
        let mut deserializer = serde_json::Deserializer::from_reader(reader);
        // Deserialize without recursion limit.
        deserializer.disable_recursion_limit();
        // Grow stack space as needed.
        let deserializer = serde_stacker::Deserializer::new(&mut deserializer);
        CrateData::deserialize(deserializer)?
    };

    let mut ctx = GenerateCtx {
        crate_data,
        contains_raw_span: Default::default(),
    };

    let mut name_to_type: HashMap<String, &TypeDecl> = Default::default();
    for ty in &ctx.crate_data.types {
        let long_name = repr_name(&ctx.crate_data, &ty.item_meta.name);
        if long_name.starts_with("charon_lib") {
            let short_name = ty.item_meta.name.name.last().unwrap().as_ident().0.clone();
            name_to_type.insert(short_name, ty);
        }
        name_to_type.insert(long_name, ty);
    }
    let raw_span = name_to_type.get("RawSpan").unwrap();
    ctx.contains_raw_span = contains_id(&ctx.crate_data, raw_span.def_id);

    // This lists items in the order we want to generate code for them. The ith list of this slice
    // will be used to generate code into the `__REPLACE{i}__` comment in `GAstOfJson.template.ml`.
    // Eventually we should reorder definitions so the generated ones are all in one block. eping
    // the order is important while we migrate from hand-written code.
    let names: &[&[&str]] = &[
        &[
            "Span",
            "InlineAttr",
            "Attribute",
            "AttrInfo",
            "TypeVar",
            "RegionVar",
            "Region",
            "IntegerTy",
            "LiteralTy",
            "ConstGenericVar",
            "RefKind",
            "AssumedTy",
            "TypeId",
        ],
        &[
            "ConstGeneric",
            "Ty",
            "ExistentialPredicate",
            "TraitRef",
            "TraitDeclRef",
            "GlobalDeclRef",
            "GenericArgs",
            "TraitRefKind",
            "Field",
            "Variant",
            "TypeDeclKind",
        ],
        &["Loc"],
        &["FileId", "FileName"],
        &[
            "TraitClause",
            "OutlivesPred",
            "RegionOutlives",
            "TypeOutlives",
            "TraitTypeConstraint",
            "GenericParams",
            "ImplElem",
            "PathElem",
            "Name",
            "ItemMeta",
            "TypeDecl",
            "Var",
            "FieldProjKind",
            "ProjectionElem",
            "Projection",
            "Place",
            "BorrowKind",
            "CastKind",
            "UnOp",
            "BinOp",
            "Literal",
            "AssumedFunId",
            "FunId",
            "FunIdOrTraitMethodRef",
            "FnPtr",
            "FnOperand",
            "ConstantExpr",
            "RawConstantExpr",
            "Operand",
            "AggregateKind",
            "Rvalue",
            "ParamsInfo",
            "ClosureKind",
            "ClosureInfo",
            "FunSig",
            "Call",
            "GExprBody",
            "ItemKind",
        ],
        &[
            "TraitDecl",
            "TraitImpl",
            "GDeclarationGroup",
            "DeclarationGroup",
        ],
    ];
    let template_path = dir.join("GAstOfJson.template.ml");
    let mut template = fs::read_to_string(&template_path)
        .with_context(|| format!("Failed to read template file {}", template_path.display()))?;
    for (i, names) in names.iter().enumerate() {
        let generated = names
            .iter()
            .map(|name| {
                type_decl_to_json_deserializer(
                    &ctx,
                    name_to_type
                        .get(*name)
                        .expect(&format!("Name not found: `{name}`")),
                )
            })
            .join("\n");
        let placeholder = format!("(* __REPLACE{i}__ *)");
        template = template.replace(&placeholder, &generated);
    }

    let generated_path = dir.join("GAstOfJson.ml");
    fs::write(&generated_path, template).with_context(|| {
        format!(
            "Failed to write generated file {}",
            generated_path.display()
        )
    })?;
    Ok(())
}
