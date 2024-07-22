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

struct GenerateCtx<'a> {
    crate_data: &'a CrateData,
    contains_raw_span: HashMap<TypeDeclId, bool>,
    name_to_type: HashMap<String, &'a TypeDecl>,
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

/// Converts a type to the appropriate ocaml name. In case of generics, this provides appropriate
/// parameters.
fn type_to_ocaml_name(ctx: &GenerateCtx, ty: &Ty) -> String {
    match ty {
        Ty::Literal(LiteralTy::Bool) => "bool".to_string(),
        Ty::Literal(LiteralTy::Char) => "char".to_string(),
        Ty::Literal(LiteralTy::Integer(_)) => "int".to_string(),
        Ty::Adt(adt_kind, generics) => {
            let mut args = generics
                .types
                .iter()
                .map(|ty| type_to_ocaml_name(ctx, ty))
                .map(|name| {
                    if !name.chars().all(|c| c.is_alphanumeric()) {
                        format!("({name})")
                    } else {
                        name
                    }
                })
                .collect_vec();
            match adt_kind {
                TypeId::Adt(id) => {
                    let adt: &TypeDecl = &ctx.crate_data.types[id.index()];
                    let mut base_ty = type_name_to_ocaml_ident(&adt.item_meta);
                    if base_ty == "vec" {
                        base_ty = "list".to_string();
                        args.pop(); // Remove the allocator generic param
                    }
                    let args = match args.as_slice() {
                        [] => String::new(),
                        [arg] => arg.clone(),
                        args => format!("({})", args.iter().join(",")),
                    };
                    format!("{args} {base_ty}")
                }
                TypeId::Assumed(AssumedTy::Box) => args[0].clone(),
                TypeId::Tuple => args.iter().join("*"),
                _ => unimplemented!("{ty:?}"),
            }
        }
        Ty::TypeVar(var_id) => format!("'a{}", var_id.index()),
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

fn build_type(_ctx: &GenerateCtx, decl: &TypeDecl, body: &str) -> String {
    let ty_name = type_name_to_ocaml_ident(&decl.item_meta);
    let generics = decl
        .generics
        .types
        .iter()
        .enumerate()
        .map(|(i, _)| format!("'a{i}"))
        .collect_vec();
    let generics = match generics.as_slice() {
        [] => String::new(),
        [ty] => ty.clone(),
        generics => format!("({})", generics.iter().join(",")),
    };
    format!("and {generics} {ty_name} = {body}")
}

fn type_decl_to_ocaml_decl(ctx: &GenerateCtx, decl: &TypeDecl) -> String {
    let body = match &decl.kind {
        TypeDeclKind::Struct(fields) if fields.is_empty() => {
            todo!()
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
            todo!()
        }
        TypeDeclKind::Alias(_ty) => {
            todo!()
        }
        TypeDeclKind::Struct(fields) if fields.iter().all(|f| f.name.is_none()) => {
            todo!()
        }
        TypeDeclKind::Struct(fields) => {
            let fields = fields
                .iter()
                .filter(|f| !f.is_opaque())
                .map(|f| {
                    let name = f.renamed_name().unwrap();
                    let ty = type_to_ocaml_name(ctx, &f.ty);
                    format!("{name} : {ty}")
                })
                .join(";");
            format!("{{ {fields} }}")
        }
        TypeDeclKind::Enum(variants) => {
            variants
                .iter()
                .filter(|v| !v.is_opaque())
                .map(|variant| {
                    let rename = variant.renamed_name();
                    let ty = if variant.fields.is_empty() {
                        // Unit variant
                        String::new()
                    } else {
                        let fields = variant
                            .fields
                            .clone()
                            .iter()
                            .map(|f| type_to_ocaml_name(ctx, &f.ty))
                            .join("*");
                        format!(" of {fields}")
                    };
                    format!("{rename}{ty}")
                })
                .join("|")
        }
        TypeDeclKind::Opaque => todo!(),
        TypeDeclKind::Error(_) => todo!(),
    };
    build_type(ctx, decl, &body)
}

/// The kind of code generation to perform.
enum GenerationKind {
    OfJson,
    TypeDecl,
}

/// Replace markers in `template` with auto-generated code.
struct GenerateCodeFor<'a> {
    kind: GenerationKind,
    template: PathBuf,
    target: PathBuf,
    /// Each list corresponds to a marker. We replace the ith `__REPLACE{i}__` marker with
    /// generated code for each definition in the ith list.
    ///
    /// Eventually we should reorder definitions so the generated ones are all in one block.
    /// Keeping the order is important while we migrate away from hand-written code.
    markers: &'a [&'a [&'a str]],
}

impl GenerateCodeFor<'_> {
    fn generate(&self, ctx: &GenerateCtx) -> Result<()> {
        let mut template = fs::read_to_string(&self.template)
            .with_context(|| format!("Failed to read template file {}", self.template.display()))?;
        for (i, names) in self.markers.iter().enumerate() {
            let generated = names
                .iter()
                .map(|name| {
                    ctx.name_to_type
                        .get(*name)
                        .expect(&format!("Name not found: `{name}`"))
                })
                .map(|ty| match self.kind {
                    GenerationKind::OfJson => type_decl_to_json_deserializer(&ctx, ty),
                    GenerationKind::TypeDecl => type_decl_to_ocaml_decl(&ctx, ty),
                })
                .join("\n");
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

    let mut name_to_type: HashMap<String, &TypeDecl> = Default::default();
    for ty in &crate_data.types {
        let long_name = repr_name(&crate_data, &ty.item_meta.name);
        if long_name.starts_with("charon_lib") {
            let short_name = ty.item_meta.name.name.last().unwrap().as_ident().0.clone();
            name_to_type.insert(short_name, ty);
        }
        name_to_type.insert(long_name, ty);
    }
    let contains_raw_span = {
        let raw_span = name_to_type.get("RawSpan").unwrap();
        contains_id(&crate_data, raw_span.def_id)
    };

    let ctx = GenerateCtx {
        crate_data: &crate_data,
        contains_raw_span,
        name_to_type,
    };

    let generate_code_for = vec![
        GenerateCodeFor {
            kind: GenerationKind::TypeDecl,
            template: dir.join("GAst.template.ml"),
            target: dir.join("GAst.ml"),
            markers: &[
                &["FnOperand", "Call"],
                &[
                    "ParamsInfo",
                    "ClosureKind",
                    "ClosureInfo",
                    "FunSig",
                    "ItemKind",
                    "GExprBody",
                ],
                &["TraitDecl", "TraitImpl", "GDeclarationGroup"],
                &["DeclarationGroup"],
                &["Var"],
                &["AnyTransId"],
            ],
        },
        GenerateCodeFor {
            kind: GenerationKind::OfJson,
            template: dir.join("GAstOfJson.template.ml"),
            target: dir.join("GAstOfJson.ml"),
            markers: &[
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
            ],
        },
    ];
    for file in generate_code_for {
        file.generate(&ctx)?;
    }
    Ok(())
}
