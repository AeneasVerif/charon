//! Generate ocaml deserialization code for our types.
//!
//! This binary runs charon on itself and generates the appropriate `<type>_of_json` functions for
//! our types. The generated functions are inserted into `./generate-ml/GAstOfJson.template.ml` to
//! construct the final `GAstOfJson.ml`.
//!
//! To run it, call `cargo run --bin generate-ml`. It is also run by `make generate-ml` in the
//! crate root. Don't forget to format the output code after regenerating.
#![feature(rustc_private)]
#![feature(if_let_guard)]

use anyhow::{bail, Context, Result};
use assert_cmd::cargo::CommandCargoExt;
use charon_lib::ast::*;
use charon_lib::export::CrateData;
use convert_case::{Case, Casing};
use derive_visitor::{visitor_enter_fn, Drive};
use indoc::indoc;
use itertools::Itertools;
use std::collections::{HashMap, HashSet};
use std::fmt::Write;
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
        "virtual"
            | "bool"
            | "char"
            | "struct"
            | "type"
            | "let"
            | "fun"
            | "open"
            | "rec"
            | "assert"
            | "float"
            | "end"
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
        .unwrap_or(item_meta.name.name.last().unwrap().as_ident().unwrap().0);
    make_ocaml_ident(name)
}

/// Traverse all types to figure out which ones transitively contain the given id.
fn contains_id(crate_data: &TranslatedCrate, haystack: TypeDeclId) -> HashMap<TypeDeclId, bool> {
    fn traverse_ty(
        crate_data: &TranslatedCrate,
        ty: &TypeDecl,
        stack: &mut Vec<TypeDeclId>,
        map: &mut HashMap<TypeDeclId, bool>,
    ) -> Result<bool, TypeDeclId> {
        if let Some(x) = map.get(&ty.def_id) {
            return Ok(*x);
        }
        if stack.contains(&ty.def_id) {
            return Err(ty.def_id);
        }

        stack.push(ty.def_id);
        let exploring_def_id = ty.def_id;
        let mut contains = false;
        let mut requires_parent = None;
        ty.drive(&mut Ty::visit_inside(derive_visitor::visitor_enter_fn(
            |id: &TypeDeclId| {
                if let Some(ty) = crate_data.type_decls.get(*id) {
                    match traverse_ty(crate_data, ty, stack, map) {
                        Ok(true) => contains = true,
                        Err(loop_id) if loop_id != exploring_def_id && stack.contains(&loop_id) => {
                            requires_parent = Some(loop_id)
                        }
                        _ => {}
                    }
                }
            },
        )));
        stack.pop();

        if contains {
            map.insert(ty.def_id, true);
            Ok(true)
        } else if let Some(id) = requires_parent {
            Err(id)
        } else {
            map.insert(ty.def_id, false);
            Ok(false)
        }
    }
    let mut map = HashMap::new();
    map.insert(haystack, true);
    for ty in &crate_data.type_decls {
        let _ = traverse_ty(crate_data, ty, &mut Vec::new(), &mut map);
    }
    map.into_iter().map(|(id, x)| (id, x)).collect()
}

struct GenerateCtx<'a> {
    crate_data: &'a TranslatedCrate,
    contains_raw_span: HashMap<TypeDeclId, bool>,
    name_to_type: HashMap<String, &'a TypeDecl>,
    /// For each type, list the types it contains.
    type_tree: HashMap<TypeDeclId, HashSet<TypeDeclId>>,
    manual_type_impls: HashMap<TypeDeclId, String>,
    manual_json_impls: HashMap<TypeDeclId, String>,
}

impl<'a> GenerateCtx<'a> {
    fn new(
        crate_data: &'a TranslatedCrate,
        manual_type_impls: &[(&str, &str)],
        manual_json_impls: &[(&str, &str)],
    ) -> Self {
        let mut name_to_type: HashMap<String, &TypeDecl> = Default::default();
        let mut type_tree = HashMap::default();
        for ty in &crate_data.type_decls {
            let long_name = repr_name(crate_data, &ty.item_meta.name);
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
            ty.drive(&mut Ty::visit_inside(visitor_enter_fn(
                |id: &TypeDeclId| {
                    contained.insert(*id);
                },
            )));
            type_tree.insert(ty.def_id, contained);
        }
        let contains_raw_span = {
            let raw_span = name_to_type.get("RawSpan").unwrap();
            contains_id(crate_data, raw_span.def_id)
        };

        let mut ctx = GenerateCtx {
            crate_data: &crate_data,
            contains_raw_span,
            name_to_type,
            type_tree,
            manual_type_impls: Default::default(),
            manual_json_impls: Default::default(),
        };
        ctx.manual_type_impls = manual_type_impls
            .iter()
            .map(|(name, def)| (ctx.id_from_name(name), def.to_string()))
            .collect();
        ctx.manual_json_impls = manual_json_impls
            .iter()
            .map(|(name, def)| (ctx.id_from_name(name), def.to_string()))
            .collect();
        ctx
    }

    fn id_from_name(&self, name: &str) -> TypeDeclId {
        self.name_to_type
            .get(name)
            .expect(&format!("Name not found: `{name}`"))
            .def_id
    }

    /// List the (recursive) children of this type.
    fn children_of(&self, name: &str) -> HashSet<TypeDeclId> {
        let start_id = self.id_from_name(name);
        self.children_of_inner(vec![start_id])
    }

    fn children_of_inner(&self, ty: Vec<TypeDeclId>) -> HashSet<TypeDeclId> {
        let mut children = HashSet::new();
        let mut stack = ty.to_vec();
        while let Some(id) = stack.pop() {
            if !children.contains(&id)
                && self
                    .crate_data
                    .type_decls
                    .get(id)
                    .is_some_and(|decl| decl.item_meta.is_local)
            {
                children.insert(id);
                if let Some(contained) = self.type_tree.get(&id) {
                    stack.extend(contained);
                }
            }
        }
        children
    }

    fn markers_from_names(
        &self,
        markers: &'a [(GenerationKind, &'a [&'a str])],
    ) -> Vec<(GenerationKind, HashSet<TypeDeclId>)> {
        markers
            .iter()
            .copied()
            .map(|(kind, type_names)| {
                let types = type_names
                    .iter()
                    .map(|name| self.id_from_name(*name))
                    .collect();
                (kind, types)
            })
            .collect()
    }
}

/// Converts a type to the appropriate `*_of_json` call. In case of generics, this combines several
/// functions, e.g. `list_of_json bool_of_json`.
fn type_to_ocaml_call(ctx: &GenerateCtx, ty: &Ty) -> String {
    match ty.kind() {
        TyKind::Literal(LiteralTy::Bool) => "bool_of_json".to_string(),
        TyKind::Literal(LiteralTy::Char) => "char_of_json".to_string(),
        TyKind::Literal(LiteralTy::Integer(_)) => "int_of_json".to_string(),
        TyKind::Literal(LiteralTy::Float(_)) => "float_of_json".to_string(),
        TyKind::Adt(adt_kind, generics) => {
            let mut expr = Vec::new();
            for ty in &generics.types {
                expr.push(type_to_ocaml_call(ctx, ty))
            }
            match adt_kind {
                TypeId::Adt(id) => {
                    let mut first = if let Some(tdecl) = ctx.crate_data.type_decls.get(*id) {
                        type_name_to_ocaml_ident(&tdecl.item_meta)
                    } else {
                        format!("missing_type_{id}")
                    };
                    if first == "vec" {
                        first = "list".to_string();
                        expr.pop(); // Remove the allocator generic param
                    }
                    expr.insert(0, first + "_of_json");
                }
                TypeId::Builtin(BuiltinTy::Box) => {}
                TypeId::Tuple => {
                    let name = match generics.types.len() {
                        2 => "pair_of_json".to_string(),
                        3 => "triple_of_json".to_string(),
                        len => format!("tuple_{len}_of_json"),
                    };
                    expr.insert(0, name);
                }
                _ => unimplemented!("{ty:?}"),
            }
            if let TypeId::Adt(id) = adt_kind {
                if *ctx.contains_raw_span.get(&id).unwrap_or(&false) {
                    expr.push("id_to_file".to_string())
                }
            }
            expr.into_iter().map(|f| format!("({f})")).join(" ")
        }
        TyKind::TypeVar(var_id) => format!("arg{}_of_json", var_id.index()),
        // TyKind::Ref(_, _, _) => todo!(),
        _ => unimplemented!("{ty:?}"),
    }
}

/// Converts a type to the appropriate ocaml name. In case of generics, this provides appropriate
/// parameters.
fn type_to_ocaml_name(ctx: &GenerateCtx, ty: &Ty) -> String {
    match ty.kind() {
        TyKind::Literal(LiteralTy::Bool) => "bool".to_string(),
        TyKind::Literal(LiteralTy::Char) => "char".to_string(),
        TyKind::Literal(LiteralTy::Integer(_)) => "int".to_string(),
        TyKind::Literal(LiteralTy::Float(_)) => "float_of_json".to_string(),
        TyKind::Adt(adt_kind, generics) => {
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
                    let mut base_ty = if let Some(tdecl) = ctx.crate_data.type_decls.get(*id) {
                        type_name_to_ocaml_ident(&tdecl.item_meta)
                    } else if let Some(name) = ctx.crate_data.item_name(*id) {
                        eprintln!(
                            "Warning: type {} missing from llbc",
                            repr_name(ctx.crate_data, name)
                        );
                        name.name
                            .last()
                            .unwrap()
                            .as_ident()
                            .unwrap()
                            .0
                            .to_lowercase()
                    } else {
                        format!("missing_type_{id}")
                    };
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
                TypeId::Builtin(BuiltinTy::Box) => args[0].clone(),
                TypeId::Tuple => args.iter().join("*"),
                _ => unimplemented!("{ty:?}"),
            }
        }
        TyKind::TypeVar(var_id) => format!("'a{}", var_id.index()),
        _ => unimplemented!("{ty:?}"),
    }
}

fn convert_vars<'a>(ctx: &GenerateCtx, fields: impl IntoIterator<Item = &'a Field>) -> String {
    fields
        .into_iter()
        .filter(|f| !f.is_opaque())
        .map(|f| {
            let name = make_ocaml_ident(f.name.as_deref().unwrap());
            let rename = make_ocaml_ident(f.renamed_name().unwrap());
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
    let return_ty = type_name_to_ocaml_ident(&decl.item_meta);
    let return_ty = if decl.generics.types.is_empty() {
        return_ty
    } else {
        format!("_ {return_ty}")
    };

    let branches = match &decl.kind {
        _ if let Some(def) = ctx.manual_json_impls.get(&decl.def_id) => def.clone(),
        TypeDeclKind::Struct(fields) if fields.is_empty() => {
            build_branch(ctx, "`Null", fields, "()")
        }
        TypeDeclKind::Struct(fields)
            if fields.len() == 1 && fields[0].name.as_ref().is_some_and(|name| name == "_raw") =>
        {
            // These are the special strongly-typed integers.
            let short_name = decl
                .item_meta
                .name
                .name
                .last()
                .unwrap()
                .as_ident()
                .unwrap()
                .0
                .clone();
            format!("| x -> {short_name}.id_of_json x")
        }
        TypeDeclKind::Struct(fields)
            if fields.len() == 1
                && (fields[0].name.is_none()
                    || decl
                        .item_meta
                        .attr_info
                        .attributes
                        .iter()
                        .filter_map(|a| a.as_unknown())
                        .any(|a| a.to_string() == "serde(transparent)")) =>
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
            let pat: String = fields
                .iter()
                .map(|f| f.name.as_deref().unwrap())
                .map(|n| make_ocaml_ident(n))
                .join(";");
            let pat = format!("`List [ {pat} ]");
            let construct = fields
                .iter()
                .map(|f| f.renamed_name().unwrap())
                .map(|n| make_ocaml_ident(n))
                .join(", ");
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
                        .filter_map(|a| a.as_unknown())
                        .any(|a| a.to_string() == "serde(skip)")
                })
                .collect_vec();
            let pat: String = fields
                .iter()
                .map(|f| {
                    let name = f.name.as_ref().unwrap();
                    let var = if f.is_opaque() {
                        "_"
                    } else {
                        &make_ocaml_ident(name)
                    };
                    format!("(\"{name}\", {var});")
                })
                .join("\n");
            let pat = format!("`Assoc [ {pat} ]");
            let construct = fields
                .iter()
                .filter(|f| !f.is_opaque())
                .map(|f| f.renamed_name().unwrap())
                .map(|n| make_ocaml_ident(n))
                .join("; ");
            let construct = format!("({{ {construct} }} : {return_ty})");
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
                                    f.name = Some(format!("x_{i}"));
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
                                    let var = if f.is_opaque() {
                                        "_"
                                    } else {
                                        &make_ocaml_ident(name)
                                    };
                                    format!("(\"{name}\", {var});")
                                })
                                .join(" ");
                            format!("`Assoc [ {pat} ]")
                        };
                        let pat = format!("`Assoc [ (\"{name}\", {inner_pat}) ]");
                        let construct_fields = fields
                            .iter()
                            .map(|f| f.name.as_ref().unwrap())
                            .map(|n| make_ocaml_ident(n))
                            .join(", ");
                        let construct = format!("{rename} ({construct_fields})");
                        build_branch(ctx, &pat, &fields, &construct)
                    }
                })
                .join("\n")
        }
        TypeDeclKind::Union(..) => todo!(),
        TypeDeclKind::Opaque => todo!(),
        TypeDeclKind::Error(_) => todo!(),
    };
    build_function(ctx, decl, &branches)
}

fn extract_doc_comments(attr_info: &AttrInfo) -> String {
    attr_info
        .attributes
        .iter()
        .filter_map(|a| a.as_doc_comment())
        .join("\n")
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
        _ if let Some(def) = ctx.manual_type_impls.get(&decl.def_id) => def.clone(),
        TypeDeclKind::Alias(ty) => type_to_ocaml_name(ctx, ty),
        TypeDeclKind::Struct(fields) if fields.is_empty() => "unit".to_string(),
        TypeDeclKind::Struct(fields)
            if fields.len() == 1 && fields[0].name.as_ref().is_some_and(|name| name == "_raw") =>
        {
            // These are the special strongly-typed integers.
            let short_name = decl
                .item_meta
                .name
                .name
                .last()
                .unwrap()
                .as_ident()
                .unwrap()
                .0
                .clone();
            format!("{short_name}.id")
        }
        TypeDeclKind::Struct(fields)
            if fields.len() == 1
                && (fields[0].name.is_none()
                    || decl
                        .item_meta
                        .attr_info
                        .attributes
                        .iter()
                        .filter_map(|a| a.as_unknown())
                        .any(|a| a.to_string() == "serde(transparent)")) =>
        {
            type_to_ocaml_name(ctx, &fields[0].ty)
        }
        TypeDeclKind::Struct(fields) if fields.iter().all(|f| f.name.is_none()) => fields
            .iter()
            .filter(|f| !f.is_opaque())
            .map(|f| {
                let ty = type_to_ocaml_name(ctx, &f.ty);
                format!("{ty}")
            })
            .join("*"),
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
        TypeDeclKind::Union(..) => todo!(),
        TypeDeclKind::Opaque => todo!(),
        TypeDeclKind::Error(_) => todo!(),
    };
    build_type(ctx, decl, co_rec, &body)
}

fn generate_visitor_bases(
    _ctx: &GenerateCtx,
    name: &str,
    inherits: Option<&str>,
    reduce: bool,
    ty_names: &[String],
) -> String {
    let mut out = String::new();
    let make_inherit = |variety| {
        if let Some(ancestor) = inherits {
            if let [module, name] = ancestor.split(".").collect_vec().as_slice() {
                format!("{module}.{variety}_{name}")
            } else {
                format!("{variety}_{ancestor}")
            }
        } else {
            format!("VisitorsRuntime.{variety}")
        }
    };

    let iter_methods = ty_names
        .iter()
        .map(|ty| format!("method visit_{ty} : 'env -> {ty} -> unit = fun _ _ -> ()"))
        .format("\n");
    let _ = write!(
        &mut out,
        "
        class ['self] iter_{name} =
          object (self : 'self)
            inherit [_] {}
            {iter_methods}
          end
        ",
        make_inherit("iter")
    );

    let map_methods = ty_names
        .iter()
        .map(|ty| format!("method visit_{ty} : 'env -> {ty} -> {ty} = fun _ x -> x"))
        .format("\n");
    let _ = write!(
        &mut out,
        "
        class ['self] map_{name} =
          object (self : 'self)
            inherit [_] {}
            {map_methods}
          end
        ",
        make_inherit("map")
    );

    if reduce {
        let reduce_methods = ty_names
            .iter()
            .map(|ty| format!("method visit_{ty} : 'env -> {ty} -> 'a = fun _ _ -> self#zero"))
            .format("\n");
        let _ = write!(
            &mut out,
            "
            class virtual ['self] reduce_{name} =
              object (self : 'self)
                inherit [_] {}
                {reduce_methods}
              end
            ",
            make_inherit("reduce")
        );

        let mapreduce_methods = ty_names
            .iter()
            .map(|ty| {
                format!("method visit_{ty} : 'env -> {ty} -> {ty} * 'a = fun _ x -> (x, self#zero)")
            })
            .format("\n");
        let _ = write!(
            &mut out,
            "
            class virtual ['self] mapreduce_{name} =
              object (self : 'self)
                inherit [_] {}
                {mapreduce_methods}
              end
            ",
            make_inherit("mapreduce")
        );
    }

    out
}

#[derive(Clone, Copy)]
struct DeriveVisitors {
    name: &'static str,
    ancestor: Option<&'static str>,
    reduce: bool,
    extra_types: &'static [&'static str],
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
            let tys = names.iter().copied().sorted().map(|id| &ctx.crate_data[id]);
            let generated = match kind {
                GenerationKind::OfJson => {
                    let fns = tys
                        .map(|ty| type_decl_to_json_deserializer(ctx, ty))
                        .format("\n");
                    format!("let rec ___ = ()\n{fns}")
                }
                GenerationKind::TypeDecl(visitors) => {
                    let mut decls = tys
                        .enumerate()
                        .map(|(i, ty)| {
                            let co_recursive = i != 0;
                            type_decl_to_ocaml_decl(ctx, ty, co_recursive)
                        })
                        .join("\n");
                    if let Some(visitors) = visitors {
                        let DeriveVisitors {
                            name,
                            mut ancestor,
                            reduce,
                            extra_types,
                        } = visitors;
                        let varieties: &[_] = if *reduce {
                            &["iter", "map", "reduce", "mapreduce"]
                        } else {
                            &["iter", "map"]
                        };
                        let intermediate_visitor_name;
                        if !extra_types.is_empty() {
                            intermediate_visitor_name = format!("{name}_base");
                            let intermediate_visitor = generate_visitor_bases(
                                ctx,
                                &intermediate_visitor_name,
                                ancestor,
                                *reduce,
                                extra_types
                                    .iter()
                                    .map(|s| s.to_string())
                                    .collect_vec()
                                    .as_slice(),
                            );
                            ancestor = Some(&intermediate_visitor_name);
                            decls = format!("(* Ancestors for the {name} visitors *){intermediate_visitor}\n{decls}");
                        }
                        let visitors = varieties
                            .iter()
                            .map(|variety| {
                                let ancestors = if let Some(ancestor) = ancestor {
                                    format!(
                                        r#"
                                        ancestors = [ "{variety}_{ancestor}" ];
                                        nude = true (* Don't inherit VisitorsRuntime *);
                                    "#
                                    )
                                } else {
                                    String::new()
                                };
                                format!(
                                    r#"
                                    visitors {{
                                        name = "{variety}_{name}";
                                        variety = "{variety}";
                                        {ancestors}
                                    }}
                                "#
                                )
                            })
                            .format(", ");
                        let _ = write!(&mut decls, "\n[@@deriving show, ord, {visitors}]");
                    };
                    decls
                }
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
    let charon_llbc = dir.join("charon-itself.llbc");
    let reuse_llbc = std::env::var("CHARON_ML_REUSE_LLBC").is_ok(); // Useful when developping
    if !reuse_llbc {
        // Call charon on itself
        let mut cmd = Command::cargo_bin("charon")?;
        cmd.arg("--cargo-arg=--lib");
        cmd.arg("--hide-marker-traits");
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

    let output_dir = if std::env::var("IN_CI").as_deref() == Ok("1") {
        dir.join("generated")
    } else {
        dir.join("../../../../charon-ml/src")
    };
    generate_ml(crate_data, dir.join("templates"), output_dir)
}

fn generate_ml(
    crate_data: TranslatedCrate,
    template_dir: PathBuf,
    output_dir: PathBuf,
) -> anyhow::Result<()> {
    let manual_type_impls = &[
        // Hand-written because we replace the `FileId` with the corresponding file name.
        (
            "RawSpan",
            "{ file : file_name; beg_loc : loc; end_loc : loc }",
        ),
        // Hand-written because the rust version is an enum with custom (de)serialization
        // functions.
        (
            "ScalarValue",
            indoc!(
                "
                (* Note that we use unbounded integers everywhere.
                   We then harcode the boundaries for the different types.
                 *)
                { value : big_int; int_ty : integer_type }
                "
            ),
        ),
        // Hand-written because we encode sequences differently.
        // TODO: encode sequences identically.
        (
            "charon_lib::ast::llbc_ast::RawStatement",
            indoc!(
                "
                | Assign of place * rvalue
                | FakeRead of place
                | SetDiscriminant of place * variant_id
                | Drop of place
                | Assert of assertion
                | Call of call
                (* FIXME: rename to `Abort` *)
                | Panic
                | Return
                | Break of int
                    (** Break to (outer) loop. The [int] identifies the loop to break to:
                        * 0: break to the first outer loop (the current loop)
                        * 1: break to the second outer loop
                        * ...
                        *)
                | Continue of int
                    (** Continue to (outer) loop. The loop identifier works
                        the same way as for {!Break} *)
                | Nop
                | Sequence of statement * statement
                | Switch of switch
                | Loop of statement
                | Error of string
                "
            ),
        ),
        // Hand-written because we encode sequences differently.
        ("charon_lib::ast::llbc_ast::Block", "statement"),
        // Hand-written because we're keeping some now-removed variants around.
        // TODO: remove these variants.
        (
            "TraitRefKind",
            indoc!(
                "
                | Self
                    (** Reference to *self*, in case of trait declarations/implementations *)
                | TraitImpl of trait_impl_id * generic_args  (** A specific implementation *)
                | BuiltinOrAuto of trait_decl_ref region_binder
                | Clause of trait_clause_id
                | ParentClause of trait_instance_id * trait_decl_id * trait_clause_id
                | FnPointer of ty
                | Closure of fun_decl_id * generic_args
                | Dyn of trait_decl_ref region_binder
                | Unsolved of trait_decl_id * generic_args
                | UnknownTrait of string
                "
            ),
        ),
        // Hand-written because we add an extra variant not present on the rust side.
        // TODO: either add this variant to the rust side or duplicate this code on the aeneas
        // side.
        (
            "Region",
            indoc!(
                "
                | RStatic  (** Static region *)
                | RBVar of region_db_id * region_var_id
                    (** Bound region. We use those in function signatures, type definitions, etc. *)
                | RFVar of region_id
                    (** Free region. We use those during the symbolic execution. *)
                | RErased  (** Erased region *)
                "
            ),
        ),
        // Handwritten because we use `indexed_var` as a hack to be able to reuse field names.
        // TODO: remove the need for this hack.
        ("RegionVar", "(region_var_id, string option) indexed_var"),
        ("TypeVar", "(type_var_id, string) indexed_var"),
    ];
    let manual_json_impls = &[
        // Hand-written because we filter out `None` values.
        (
            "Vector",
            indoc!(
                r#"
                | js ->
                    let* list = list_of_json (option_of_json arg1_of_json) js in
                    Ok (List.filter_map (fun x -> x) list)
                "#
            ),
        ),
        // Hand-written because we replace the `FileId` with the corresponding file name.
        (
            "RawSpan",
            indoc!(
                r#"
                | `Assoc [ ("file_id", file_id); ("beg", beg_loc); ("end", end_loc) ] ->
                    let* file_id = file_id_of_json file_id in
                    let file = FileId.Map.find file_id id_to_file in
                    let* beg_loc = loc_of_json beg_loc in
                    let* end_loc = loc_of_json end_loc in
                    Ok { file; beg_loc; end_loc }
                "#,
            ),
        ),
        // Hand-written because the rust version is an enum with custom (de)serialization
        // functions.
        (
            "ScalarValue",
            indoc!(
                r#"
                | `Assoc [ (ty, bi) ] ->
                    let big_int_of_json (js : json) : (big_int, string) result =
                      combine_error_msgs js __FUNCTION__
                        (match js with
                        | `Int i -> Ok (Z.of_int i)
                        | `String is -> Ok (Z.of_string is)
                        | _ -> Error "")
                    in
                    let* value = big_int_of_json bi in
                    let* int_ty = integer_type_of_json (`String ty) in
                    let sv = { value; int_ty } in
                    if not (check_scalar_value_in_range sv) then
                      raise (Failure ("Scalar value not in range: " ^ show_scalar_value sv));
                    Ok sv
                "#
            ),
        ),
        // Hand-written because the `Panic` aka `Abort` variant differs..
        // TODO: fix that.
        (
            "charon_lib::ast::llbc_ast::RawStatement",
            indoc!(
                r#"
                | `Assoc [ ("Assign", `List [ place; rvalue ]) ] ->
                    let* place = place_of_json place in
                    let* rvalue = rvalue_of_json rvalue in
                    Ok (Assign (place, rvalue))
                | `Assoc [ ("FakeRead", place) ] ->
                    let* place = place_of_json place in
                    Ok (FakeRead place)
                | `Assoc [ ("SetDiscriminant", `List [ place; variant_id ]) ] ->
                    let* place = place_of_json place in
                    let* variant_id = VariantId.id_of_json variant_id in
                    Ok (SetDiscriminant (place, variant_id))
                | `Assoc [ ("Drop", place) ] ->
                    let* place = place_of_json place in
                    Ok (Drop place)
                | `Assoc [ ("Assert", assertion) ] ->
                    let* assertion = assertion_of_json assertion in
                    Ok (Assert assertion)
                | `Assoc [ ("Call", call) ] ->
                    let* call = call_of_json call in
                    Ok (Call call)
                | `Assoc [ ("Abort", _) ] -> Ok Panic
                | `String "Return" -> Ok Return
                | `Assoc [ ("Break", i) ] ->
                    let* i = int_of_json i in
                    Ok (Break i)
                | `Assoc [ ("Continue", i) ] ->
                    let* i = int_of_json i in
                    Ok (Continue i)
                | `String "Nop" -> Ok Nop
                | `Assoc [ ("Switch", tgt) ] ->
                    let* switch = switch_of_json id_to_file tgt in
                    Ok (Switch switch)
                | `Assoc [ ("Loop", st) ] ->
                    let* st = block_of_json id_to_file st in
                    Ok (Loop st)
                | `Assoc [ ("Error", s) ] ->
                    let* s = string_of_json s in
                    Ok (Error s)
                "#
            ),
        ),
        // Hand-written because we encode sequences differently.
        (
            "charon_lib::ast::llbc_ast::Block",
            indoc!(
                r#"
                | `Assoc [ ("span", span); ("statements", statements) ] -> begin
                    let* span = span_of_json id_to_file span in
                    let* statements =
                      list_of_json (statement_of_json id_to_file) statements
                    in
                    match List.rev statements with
                    | [] -> Ok { span; content = Nop; comments_before = [] }
                    | last :: rest ->
                        let seq =
                          List.fold_left
                            (fun acc st -> { span = st.span; content = Sequence (st, acc); comments_before = [] })
                            last rest
                        in
                        Ok seq
                  end
                "#
            ),
        ),
    ];
    let ctx = GenerateCtx::new(&crate_data, manual_type_impls, manual_json_impls);

    // Compute the sets of types to be put in each module.
    let manually_implemented: HashSet<_> = [
        "ItemOpacity",
        "DeBruijnId",
        "RegionId",
        "PredicateOrigin",
        "Ty", // We exclude it since `TyKind` is renamed to `ty`
        "Opaque",
        "Body",
        "BodyId",
        "FunDecl",
        "TranslatedCrate",
    ]
    .iter()
    .map(|name| ctx.id_from_name(name))
    .collect();

    let (gast_types, llbc_types, ullbc_types) = {
        let llbc_types: HashSet<_> = ctx.children_of("charon_lib::ast::llbc_ast::Statement");
        let ullbc_types: HashSet<_> = ctx.children_of("charon_lib::ast::ullbc_ast::BodyContents");
        let common_types: HashSet<_> = llbc_types.intersection(&ullbc_types).copied().collect();

        let llbc_types: HashSet<_> = llbc_types
            .difference(&common_types.union(&manually_implemented).copied().collect())
            .copied()
            .collect();
        let ullbc_types: HashSet<_> = ullbc_types
            .difference(&common_types.union(&manually_implemented).copied().collect())
            .copied()
            .collect();

        let body_specific_types: HashSet<_> = llbc_types.union(&ullbc_types).copied().collect();
        let gast_types: HashSet<_> = ctx
            .children_of("TranslatedCrate")
            .difference(
                &body_specific_types
                    .union(&manually_implemented)
                    .copied()
                    .collect(),
            )
            .copied()
            .collect();

        (gast_types, llbc_types, ullbc_types)
    };

    #[rustfmt::skip]
    let generate_code_for = vec![
        GenerateCodeFor {
            template: template_dir.join("GAst.ml"),
            target: output_dir.join("GAst.ml"),
            markers: ctx.markers_from_names(&[
                (GenerationKind::TypeDecl(Some(DeriveVisitors {
                    name: "statement_base",
                    ancestor: Some("rvalue"),
                    reduce: false,
                    extra_types: &[
                        "abort_kind",
                    ],
                })), &[
                    "FnOperand",
                    "Call",
                    "Assert",
                ]),
                (GenerationKind::TypeDecl(None), &[
                    "ParamsInfo",
                    "ClosureKind",
                    "ClosureInfo",
                    "FunSig",
                    "ItemKind",
                    "Locals",
                    "GExprBody",
                    "GlobalDecl",
                    "TraitDecl",
                    "TraitImpl",
                    "GDeclarationGroup",
                    "DeclarationGroup",
                ]),
                (GenerationKind::TypeDecl(None), &["Var", "AnyTransId", "FunDeclId"]),
            ]),
        },
        GenerateCodeFor {
            template: template_dir.join("Expressions.ml"),
            target: output_dir.join("Expressions.ml"),
            markers: ctx.markers_from_names(&[
                (GenerationKind::TypeDecl(None), &[
                    "VarId",
                    // TODO: can't move because of variant name clash with `raw_statement::Panic`
                    "AbortKind",
                ]),
                (GenerationKind::TypeDecl(Some(DeriveVisitors {
                    name: "rvalue",
                    ancestor: Some("generic_params"),
                    reduce: false,
                    extra_types: &[
                        "var_id",
                        "variant_id",
                        "field_id",
                    ],
                })), &[
                    "BuiltinIndexOp",
                    "BuiltinFunId",
                    "BorrowKind",
                    "BinOp",
                    "FieldProjKind",
                    "ProjectionElem",
                    "PlaceKind",
                    "Place",
                    "CastKind",
                    "UnOp",
                    "NullOp",
                    "RawConstantExpr",
                    "ConstantExpr",
                    "FnPtr",
                    "FunIdOrTraitMethodRef",
                    "FunId",
                    "Operand",
                    "AggregateKind",
                    "Rvalue",
                ]),
            ]),
        },
        GenerateCodeFor {
            template: template_dir.join("Meta.ml"),
            target: output_dir.join("Meta.ml"),
            markers: ctx.markers_from_names(&[
                (GenerationKind::TypeDecl(None), &[
                    "Loc",
                    "FileName",
                    "RawSpan",
                    "Span",
                    "InlineAttr",
                    "Attribute",
                    "RawAttribute",
                    "AttrInfo",
                ]),
            ]),
        },
        GenerateCodeFor {
            template: template_dir.join("Types.ml"),
            target: output_dir.join("Types.ml"),
            markers: ctx.markers_from_names(&[
                (GenerationKind::TypeDecl(None), &[
                    "ConstGenericVarId",
                    "Disambiguator",
                    "FieldId",
                    "FunDeclId",
                    "GlobalDeclId",
                    "RegionId",
                    "TraitClauseId",
                    "TraitDeclId",
                    "TraitImplId",
                    "TypeDeclId",
                    "TypeVarId",
                    "VariantId",
                ]),
                (GenerationKind::TypeDecl(Some(DeriveVisitors {
                    name: "const_generic",
                    ancestor: Some("literal"),
                    reduce: true,
                    extra_types: &[
                        "const_generic_var_id",
                        "fun_decl_id",
                        "global_decl_id",
                        "region_db_id",
                        "region_id",
                        "region_var_id",
                        "trait_clause_id",
                        "trait_decl_id",
                        "trait_impl_id",
                        "type_decl_id",
                        "type_var_id",
                    ],
                })), &[
                    "ConstGeneric",
                ]),
                // Can't merge into above because aeneas uses the above alongside their own partial
                // copy of `ty`, which causes method type clashes.
                (GenerationKind::TypeDecl(Some(DeriveVisitors {
                    name: "ty",
                    ancestor: Some("ty_base_base"),
                    reduce: false,
                    extra_types: &[],
                })), &[
                    "TraitItemName",
                    "BuiltinTy",
                    "TypeId",
                    "ExistentialPredicate",
                    "RefKind",
                    "TyKind",
                    "Region",
                    "TraitRef",
                    "TraitRefKind",
                    "TraitDeclRef",
                    "GlobalDeclRef",
                    "GenericArgs",
                ]),
                // TODO: can't merge into above because of field name clashes (`types`, `regions` etc).
                (GenerationKind::TypeDecl(Some(DeriveVisitors {
                    name: "generic_params",
                    ancestor: Some("ty"),
                    reduce: false,
                    extra_types: &[
                        "span",
                    ],
                })), &[
                    "TraitClause",
                    "TypeVar",
                    "RegionOutlives",
                    "TypeOutlives",
                    "GenericParams",
                    "ConstGenericVar",
                    "TraitTypeConstraint",
                ]),
                (GenerationKind::TypeDecl(None), &[
                    "ImplElem",
                    "PathElem",
                    "Name",
                    "ItemMeta",
                    "Field",
                    "Variant",
                    "TypeDeclKind",
                    "TypeDecl",
                ]),
            ]),
        },
        GenerateCodeFor {
            template: template_dir.join("Values.ml"),
            target: output_dir.join("Values.ml"),
            markers: ctx.markers_from_names(&[
                (GenerationKind::TypeDecl(Some(DeriveVisitors {
                    name: "literal",
                    ancestor: None,
                    reduce: true,
                    extra_types: &[
                        "big_int",
                    ],
                })), &[
                    "IntegerTy",
                    "FloatTy",
                    "FloatValue",
                    "LiteralTy",
                    "ScalarValue",
                    "Literal",
                ]),
            ]),
        },
        GenerateCodeFor {
            template: template_dir.join("LlbcAst.ml"),
            target: output_dir.join("LlbcAst.ml"),
            markers: vec![
                (GenerationKind::TypeDecl(Some(DeriveVisitors {
                    name: "statement",
                    ancestor: Some("statement_base"),
                    reduce: false,
                    extra_types: &[],
                })), llbc_types.clone()),
            ],
        },
        GenerateCodeFor {
            template: template_dir.join("UllbcAst.ml"),
            target: output_dir.join("UllbcAst.ml"),
            markers: ctx.markers_from_names(&[
                (GenerationKind::TypeDecl(Some(DeriveVisitors {
                    name: "statement",
                    ancestor: Some("GAst.statement_base"),
                    reduce: false,
                    extra_types: &[
                        "block_id",
                    ],
                })), &[
                    "charon_lib::ast::ullbc_ast::Statement",
                    "charon_lib::ast::ullbc_ast::RawStatement",
                    "charon_lib::ast::ullbc_ast::SwitchTargets",
                ]),
                // TODO: Can't merge with above because of field name clashes (`content` and `span`).
                (GenerationKind::TypeDecl(Some(DeriveVisitors {
                    name: "ullbc_ast",
                    ancestor: Some("statement"),
                    reduce: false,
                    extra_types: &[],
                })), &[
                    "charon_lib::ast::ullbc_ast::Terminator",
                    "charon_lib::ast::ullbc_ast::RawTerminator",
                    "charon_lib::ast::ullbc_ast::BlockData",
                    "charon_lib::ast::ullbc_ast::BodyContents",
                ]),
            ]),
        },
        GenerateCodeFor {
            template: template_dir.join("GAstOfJson.ml"),
            target: output_dir.join("GAstOfJson.ml"),
            markers: vec![(GenerationKind::OfJson, gast_types)],
        },
        GenerateCodeFor {
            template: template_dir.join("LlbcOfJson.ml"),
            target: output_dir.join("LlbcOfJson.ml"),
            markers: vec![(GenerationKind::OfJson, llbc_types)],
        },
        GenerateCodeFor {
            template: template_dir.join("UllbcOfJson.ml"),
            target: output_dir.join("UllbcOfJson.ml"),
            markers: vec![(GenerationKind::OfJson, ullbc_types)],
        },
    ];
    for file in generate_code_for {
        file.generate(&ctx)?;
    }
    Ok(())
}
