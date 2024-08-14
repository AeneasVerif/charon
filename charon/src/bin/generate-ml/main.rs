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
use charon_lib::ast::{AttrInfo, Attribute, TranslatedCrate};
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
fn repr_name(_crate_data: &TranslatedCrate, n: &Name) -> String {
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
fn contains_id(crate_data: &TranslatedCrate, haystack: TypeDeclId) -> HashMap<TypeDeclId, bool> {
    enum ContainsRawSpan {
        Yes,
        No,
        Processing,
    }
    use ContainsRawSpan::*;
    fn traverse_ty(
        crate_data: &TranslatedCrate,
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
            if let Some(ty) = crate_data.type_decls.get(*id) {
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
    for ty in &crate_data.type_decls {
        traverse_ty(crate_data, ty, &mut map);
    }
    map.into_iter()
        .map(|(id, x)| (id, matches!(x, Yes)))
        .collect()
}

struct GenerateCtx<'a> {
    crate_data: &'a TranslatedCrate,
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
                    let adt: &TypeDecl = &ctx.crate_data.type_decls[*id];
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
                    let adt: &TypeDecl = &ctx.crate_data.type_decls[*id];
                    let mut base_ty = type_name_to_ocaml_ident(&adt.item_meta);
                    if base_ty == "vec" {
                        base_ty = "list".to_string();
                        args.pop(); // Remove the allocator generic param
                    }
                    if base_ty == "vector" {
                        base_ty = "list".to_string();
                        args.remove(0); // Remove the index generic param
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
            let fields = fields
                .iter()
                .filter(|field| {
                    !field
                        .attr_info
                        .attributes
                        .iter()
                        .any(|a| a.is_unknown() && a.as_unknown() == "serde(skip)")
                })
                .collect_vec();
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

fn extract_doc_comments(attr_info: &AttrInfo) -> String {
    let comments = attr_info
        .attributes
        .iter()
        .filter(|a| a.is_doc_comment())
        .map(|a| a.as_doc_comment())
        .collect_vec();
    comments.into_iter().join("\n")
}

/// Make a doc comment that contains the given string, indenting it if necessary.
fn build_doc_comment(comment: String, indent_level: usize) -> String {
    if comment == "" {
        return comment;
    }
    let is_multiline = comment.contains("\n");
    if !is_multiline {
        format!("(**{comment} *)")
    } else {
        let indent = "  ".repeat(indent_level);
        let comment = comment
            .lines()
            .enumerate()
            .map(|(i, line)| {
                // Remove one leading space if there is one (there usually is because we write `///
                // comment` and not `///comment`).
                let line = line.strip_prefix(" ").unwrap_or(line);
                // The first line follows the `(**` marker, it does not need to be indented.
                // Neither do empty lines.
                if i == 0 || line.is_empty() {
                    line.to_string()
                } else {
                    format!("{indent}    {line}")
                }
            })
            .join("\n");
        format!("(** {comment}\n{indent} *)")
    }
}

fn build_type(_ctx: &GenerateCtx, decl: &TypeDecl, co_rec: bool, body: &str) -> String {
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
    let comment = extract_doc_comments(&decl.item_meta.attr_info);
    let comment = build_doc_comment(comment, 0);
    let keyword = if co_rec { "and" } else { "type" };
    format!("\n{comment} {keyword} {generics} {ty_name} = {body}")
}

/// Generate an ocaml type declaration that mirrors `decl`.
///
/// `co_rec` indicates whether this definition is co-recursive with the ones that come before (i.e.
/// should be declared with `and` instead of `type`).
fn type_decl_to_ocaml_decl(ctx: &GenerateCtx, decl: &TypeDecl, co_rec: bool) -> String {
    let body = match &decl.kind {
        TypeDeclKind::Struct(fields) if fields.is_empty() => "unit".to_string(),
        TypeDeclKind::Struct(fields)
            if fields.len() == 1
                && decl
                    .item_meta
                    .attr_info
                    .attributes
                    .iter()
                    .any(|a| a.is_unknown() && a.as_unknown() == "serde(transparent)") =>
        {
            type_to_ocaml_name(ctx, &fields[0].ty)
        }
        TypeDeclKind::Alias(ty) => type_to_ocaml_name(ctx, ty),
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
                    let comment = extract_doc_comments(&f.attr_info);
                    let comment = build_doc_comment(comment, 2);
                    format!("{name} : {ty} {comment}")
                })
                .join(";");
            format!("{{ {fields} }}")
        }
        TypeDeclKind::Enum(variants) => {
            variants
                .iter()
                .filter(|v| !v.is_opaque())
                .map(|variant| {
                    let mut attr_info = variant.attr_info.clone();
                    let rename = variant.renamed_name();
                    let ty = if variant.fields.is_empty() {
                        // Unit variant
                        String::new()
                    } else {
                        if variant.fields.iter().all(|f| f.name.is_some()) {
                            let fields = variant
                                .fields
                                .iter()
                                .map(|f| {
                                    let comment = extract_doc_comments(&f.attr_info);
                                    let description = if comment.is_empty() {
                                        comment
                                    } else {
                                        format!(": {comment}")
                                    };
                                    format!("\n - [{}]{description}", f.name.as_ref().unwrap())
                                })
                                .join("");
                            let field_descriptions = format!("\n Fields:{fields}");
                            // Add a constructed doc-comment
                            attr_info
                                .attributes
                                .push(Attribute::DocComment(field_descriptions));
                        }
                        let fields = variant
                            .fields
                            .iter()
                            .map(|f| type_to_ocaml_name(ctx, &f.ty))
                            .join("*");
                        format!(" of {fields}")
                    };
                    let comment = extract_doc_comments(&attr_info);
                    let comment = build_doc_comment(comment, 3);
                    format!("\n\n | {rename}{ty} {comment}")
                })
                .join("")
        }
        TypeDeclKind::Opaque => todo!(),
        TypeDeclKind::Error(_) => todo!(),
    };
    build_type(ctx, decl, co_rec, &body)
}

/// The kind of code generation to perform.
enum GenerationKind {
    OfJson,
    /// The boolean indicates whether this is an open recursion group (i.e. shuold start with `and
    /// ty = ...`). If `false`, the first element of the group will be `type ty = ...` instead of
    /// `and ty = ...`;
    TypeDecl(bool),
}

/// Replace markers in `template` with auto-generated code.
struct GenerateCodeFor<'a> {
    template: PathBuf,
    target: PathBuf,
    /// Each list corresponds to a marker. We replace the ith `__REPLACE{i}__` marker with
    /// generated code for each definition in the ith list.
    ///
    /// Eventually we should reorder definitions so the generated ones are all in one block.
    /// Keeping the order is important while we migrate away from hand-written code.
    markers: &'a [(GenerationKind, &'a [&'a str])],
}

impl GenerateCodeFor<'_> {
    fn generate(&self, ctx: &GenerateCtx) -> Result<()> {
        let mut template = fs::read_to_string(&self.template)
            .with_context(|| format!("Failed to read template file {}", self.template.display()))?;
        for (i, (kind, names)) in self.markers.iter().enumerate() {
            let generated = names
                .iter()
                .map(|name| {
                    ctx.name_to_type
                        .get(*name)
                        .expect(&format!("Name not found: `{name}`"))
                })
                .enumerate()
                .map(|(i, ty)| match kind {
                    GenerationKind::OfJson => type_decl_to_json_deserializer(&ctx, ty),
                    GenerationKind::TypeDecl(open_rec) => {
                        let co_recursive = *open_rec || i != 0;
                        type_decl_to_ocaml_decl(&ctx, ty, co_recursive)
                    }
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
    let reuse_llbc = std::env::var("CHARON_ML_REUSE_LLBC").is_ok(); // Useful when developping
    if !reuse_llbc {
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

    let crate_data: TranslatedCrate = {
        use serde::Deserialize;
        let file = File::open(&charon_llbc)
            .with_context(|| format!("Failed to read llbc file {}", charon_llbc.display()))?;
        let reader = BufReader::new(file);
        let mut deserializer = serde_json::Deserializer::from_reader(reader);
        // Deserialize without recursion limit.
        deserializer.disable_recursion_limit();
        // Grow stack space as needed.
        let deserializer = serde_stacker::Deserializer::new(&mut deserializer);
        CrateData::deserialize(deserializer)?.translated
    };

    let mut name_to_type: HashMap<String, &TypeDecl> = Default::default();
    for ty in &crate_data.type_decls {
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

    #[rustfmt::skip]
    let generate_code_for = vec![
        GenerateCodeFor {
            template: dir.join("templates/GAst.ml"),
            target: dir.join("generated/GAst.ml"),
            markers: &[
                (GenerationKind::TypeDecl(true), &["FnOperand", "Call"]),
                (GenerationKind::TypeDecl(false), &[
                    "ParamsInfo",
                    "ClosureKind",
                    "ClosureInfo",
                    "FunSig",
                    "ItemKind",
                    "GExprBody",
                ]),
                (GenerationKind::TypeDecl(false), &["TraitDecl", "TraitImpl", "GDeclarationGroup"]),
                (GenerationKind::TypeDecl(false), &["DeclarationGroup"]),
                (GenerationKind::TypeDecl(false), &["Var"]),
                (GenerationKind::TypeDecl(false), &["AnyTransId"]),
            ],
        },
        GenerateCodeFor {
            template: dir.join("templates/Expressions.ml"),
            target: dir.join("generated/Expressions.ml"),
            markers: &[
                (GenerationKind::TypeDecl(false), &["AssumedFunId"]),
                (GenerationKind::TypeDecl(false), &["FieldProjKind", "ProjectionElem", "Projection", "Place"]),
                (GenerationKind::TypeDecl(false), &["BorrowKind", "BinOp"]),
                (GenerationKind::TypeDecl(false), &[
                    "CastKind",
                    "UnOp",
                    "RawConstantExpr",
                    "ConstantExpr",
                    "FnPtr",
                    "FunIdOrTraitMethodRef",
                    "FunId",
                ]),
                (GenerationKind::TypeDecl(false), &["Operand", "AggregateKind", "Rvalue"]),
            ],
        },
        GenerateCodeFor {
            template: dir.join("templates/Meta.ml"),
            target: dir.join("generated/Meta.ml"),
            markers: &[
                (GenerationKind::TypeDecl(false), &["Loc", "FileName"]),
                (GenerationKind::TypeDecl(false), &["Span", "InlineAttr", "Attribute", "AttrInfo"]),
            ],
        },
        GenerateCodeFor {
            template: dir.join("templates/Types.ml"),
            target: dir.join("generated/Types.ml"),
            markers: &[
                (GenerationKind::TypeDecl(false), &[
                    "AssumedTy",
                    "TypeId",
                    "ExistentialPredicate",
                    "Ty",
                    "TraitRef",
                    "TraitDeclRef",
                    "GlobalDeclRef",
                    "GenericArgs",
                ]),
                (GenerationKind::TypeDecl(true), &["TraitClause"]),
                (GenerationKind::TypeDecl(true), &["TraitTypeConstraint"]),
                (GenerationKind::TypeDecl(false), &["ImplElem", "PathElem", "Name", "ItemMeta"]),
                (GenerationKind::TypeDecl(false), &["Field", "Variant", "TypeDeclKind", "TypeDecl"]),
            ],
        },
        GenerateCodeFor {
            template: dir.join("templates/GAstOfJson.ml"),
            target: dir.join("generated/GAstOfJson.ml"),
            markers: &[
                (GenerationKind::OfJson, &[
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
                ]),
                (GenerationKind::OfJson, &[
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
                ]),
                (GenerationKind::OfJson, &["Loc"]),
                (GenerationKind::OfJson, &["FileName"]),
                (GenerationKind::OfJson, &[
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
                ]),
                (GenerationKind::OfJson, &[
                    "TraitDecl",
                    "TraitImpl",
                    "GDeclarationGroup",
                    "DeclarationGroup",
                    "AnyTransId",
                ]),
            ],
        },
    ];
    for file in generate_code_for {
        file.generate(&ctx)?;
    }
    Ok(())
}
