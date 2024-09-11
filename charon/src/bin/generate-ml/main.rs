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
    BuiltinTy, Field, LiteralTy, Ty, TypeDecl, TypeDeclId, TypeDeclKind, TypeId,
};
use convert_case::{Case, Casing};
use derive_visitor::{visitor_enter_fn, Drive};
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
        .unwrap_or(item_meta.name.name.last().unwrap().as_ident().0);
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
        ty.drive(&mut derive_visitor::visitor_enter_fn(|id: &TypeDeclId| {
            if let Some(ty) = crate_data.type_decls.get(*id) {
                match traverse_ty(crate_data, ty, stack, map) {
                    Ok(true) => contains = true,
                    Err(loop_id) if loop_id != exploring_def_id && stack.contains(&loop_id) => {
                        requires_parent = Some(loop_id)
                    }
                    _ => {}
                }
            }
        }));
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
}

impl<'a> GenerateCtx<'a> {
    fn new(crate_data: &'a TranslatedCrate) -> Self {
        let mut name_to_type: HashMap<String, &TypeDecl> = Default::default();
        let mut type_tree = HashMap::default();
        for ty in &crate_data.type_decls {
            let long_name = repr_name(crate_data, &ty.item_meta.name);
            if long_name.starts_with("charon_lib") {
                let short_name = ty.item_meta.name.name.last().unwrap().as_ident().0.clone();
                name_to_type.insert(short_name, ty);
            }
            name_to_type.insert(long_name, ty);

            let mut contained = HashSet::new();
            ty.drive(&mut visitor_enter_fn(|id: &TypeDeclId| {
                contained.insert(*id);
            }));
            type_tree.insert(ty.def_id, contained);
        }
        let contains_raw_span = {
            let raw_span = name_to_type.get("RawSpan").unwrap();
            contains_id(crate_data, raw_span.def_id)
        };

        GenerateCtx {
            crate_data: &crate_data,
            contains_raw_span,
            name_to_type,
            type_tree,
        }
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
    match ty {
        Ty::Literal(LiteralTy::Bool) => "bool_of_json".to_string(),
        Ty::Literal(LiteralTy::Char) => "char_of_json".to_string(),
        Ty::Literal(LiteralTy::Integer(_)) => "int_of_json".to_string(),
        Ty::Literal(LiteralTy::Float(_)) => "float_of_json".to_string(),
        Ty::Adt(adt_kind, generics) => {
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
        Ty::Literal(LiteralTy::Float(_)) => "float_of_json".to_string(),
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
                    let mut base_ty = if let Some(tdecl) = ctx.crate_data.type_decls.get(*id) {
                        type_name_to_ocaml_ident(&tdecl.item_meta)
                    } else if let Some(name) = ctx.crate_data.item_names.get(&(*id).into()) {
                        eprintln!(
                            "Warning: type {} missing from llbc",
                            repr_name(ctx.crate_data, name)
                        );
                        name.name.last().unwrap().as_ident().0.to_lowercase()
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
        Ty::TypeVar(var_id) => format!("'a{}", var_id.index()),
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
                .0
                .clone();
            format!("| x -> {short_name}.id_of_json x")
        }
        TypeDeclKind::Struct(fields) if fields.len() == 1 => {
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
                        .any(|a| a.is_unknown() && a.as_unknown().to_string() == "serde(skip)")
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
                && decl.item_meta.attr_info.attributes.iter().any(|a| {
                    a.is_unknown() && a.as_unknown().to_string() == "serde(transparent)"
                }) =>
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
    ord: bool,
    reduce: bool,
    extra_types: &'static [&'static str],
}

/// The kind of code generation to perform.
#[derive(Clone, Copy)]
enum GenerationKind {
    OfJson,
    /// The boolean indicates whether this is an open recursion group (i.e. shuold start with `and
    /// ty = ...`). If `false`, the first element of the group will be `type ty = ...` instead of
    /// `and ty = ...`;
    TypeDecl(bool, Option<DeriveVisitors>),
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
                GenerationKind::OfJson => tys
                    .map(|ty| type_decl_to_json_deserializer(ctx, ty))
                    .join("\n"),
                GenerationKind::TypeDecl(open_rec, visitors) => {
                    let mut decls = tys
                        .enumerate()
                        .map(|(i, ty)| {
                            let co_recursive = *open_rec || i != 0;
                            type_decl_to_ocaml_decl(ctx, ty, co_recursive)
                        })
                        .join("\n");
                    if let Some(visitors) = visitors {
                        let DeriveVisitors {
                            name,
                            mut ancestor,
                            ord,
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
                        let ord = if *ord { ", ord" } else { "" };
                        let _ = write!(&mut decls, "\n[@@deriving show {ord}, {visitors}]");
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
        cmd.arg("--errors-as-warnings");
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

    generate_ml(crate_data, dir)
}

fn generate_ml(crate_data: TranslatedCrate, output_dir: PathBuf) -> anyhow::Result<()> {
    let ctx = GenerateCtx::new(&crate_data);

    // Compute the sets of types to be put in each module.
    let manually_implemented: HashSet<_> = [
        "Vector",
        "ScalarValue",
        "RawSpan",
        "ItemOpacity",
        "DeBruijnId",
        "RegionId",
        "PredicateOrigin",
        "charon_lib::ast::llbc_ast::RawStatement",
        "Opaque",
        "Body",
        "BodyId",
        "FunDecl",
        "GlobalDecl",
        "TranslatedCrate",
    ]
    .iter()
    .map(|name| ctx.id_from_name(name))
    .collect();
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

    // TODO: give handwritten versions through rust
    // TODO: that way we can generate all the visitor boilerplate
    // TODO: try to move everything else from the template files to the rust side
    // TODO: merge visitors as convenient
    #[rustfmt::skip]
    let generate_code_for = vec![
        GenerateCodeFor {
            template: output_dir.join("templates/GAst.ml"),
            target: output_dir.join("generated/GAst.ml"),
            markers: ctx.markers_from_names(&[
                (GenerationKind::TypeDecl(false, Some(DeriveVisitors {
                    name: "call",
                    ancestor: Some("ast_base"),
                    reduce: false,
                    ord: false,
                    extra_types: &[],
                })), &[
                    "FnOperand",
                    "Call",
                    "Assert",
                ]),
                (GenerationKind::TypeDecl(false, None), &[
                    "ParamsInfo",
                    "ClosureKind",
                    "ClosureInfo",
                    "FunSig",
                    "ItemKind",
                    "GExprBody",
                ]),
                (GenerationKind::TypeDecl(false, None), &["TraitDecl", "TraitImpl", "GDeclarationGroup"]),
                (GenerationKind::TypeDecl(false, None), &["DeclarationGroup"]),
                (GenerationKind::TypeDecl(false, None), &["Var"]),
                (GenerationKind::TypeDecl(false, None), &["AnyTransId"]),
            ]),
        },
        GenerateCodeFor {
            template: output_dir.join("templates/Expressions.ml"),
            target: output_dir.join("generated/Expressions.ml"),
            markers: ctx.markers_from_names(&[
                (GenerationKind::TypeDecl(false, None), &[
                    "BuiltinFunId",
                    "BuiltinIndexOp",
                    "AbortKind",
                ]),
                (GenerationKind::TypeDecl(false, Some(DeriveVisitors {
                    name: "place",
                    ancestor: Some("ty"),
                    reduce: false,
                    ord: true,
                    extra_types: &[
                        "var_id",
                        "variant_id",
                        "field_id",
                    ],
                })), &[
                    "FieldProjKind",
                    "ProjectionElem",
                    "Projection",
                    "Place",
                ]),
                (GenerationKind::TypeDecl(false, None), &[
                    "BorrowKind",
                    "BinOp",
                ]),
                (GenerationKind::TypeDecl(false, Some(DeriveVisitors {
                    name: "constant_expr",
                    ancestor: Some("place"),
                    reduce: false,
                    ord: true,
                    extra_types: &["assumed_fun_id"],
                })), &[
                    "CastKind",
                    "UnOp",
                    "NullOp",
                    "RawConstantExpr",
                    "ConstantExpr",
                    "FnPtr",
                    "FunIdOrTraitMethodRef",
                    "FunId",
                ]),
                (GenerationKind::TypeDecl(false, Some(DeriveVisitors {
                    name: "rvalue",
                    ancestor: Some("constant_expr"),
                    reduce: false,
                    ord: false,
                    extra_types: &["binop", "borrow_kind"],
                })), &[
                    "Operand",
                    "AggregateKind",
                    "Rvalue",
                ]),
            ]),
        },
        GenerateCodeFor {
            template: output_dir.join("templates/Meta.ml"),
            target: output_dir.join("generated/Meta.ml"),
            markers: ctx.markers_from_names(&[
                (GenerationKind::TypeDecl(false, None), &[
                    "Loc",
                    "FileName",
                ]),
                (GenerationKind::TypeDecl(false, None), &[
                    "Span",
                    "InlineAttr",
                    "Attribute",
                    "RawAttribute",
                    "AttrInfo",
                ]),
            ]),
        },
        GenerateCodeFor {
            template: output_dir.join("templates/Types.ml"),
            target: output_dir.join("generated/Types.ml"),
            markers: ctx.markers_from_names(&[
                (GenerationKind::TypeDecl(false, None), &[
                    "BuiltinTy",
                    "TypeId",
                    "ExistentialPredicate",
                    "Ty",
                    "TraitRef",
                    "TraitDeclRef",
                    "GlobalDeclRef",
                    "GenericArgs",
                ]),
                (GenerationKind::TypeDecl(true, None), &[
                    "TraitClause",
                ]),
                (GenerationKind::TypeDecl(true, Some(DeriveVisitors {
                    name: "generic_params",
                    ancestor: Some("generic_params_base"),
                    reduce: false,
                    ord: true,
                    extra_types: &[],
                })), &[
                    "TraitTypeConstraint",
                ]),
                (GenerationKind::TypeDecl(false, None), &["ImplElem", "PathElem", "Name", "ItemMeta"]),
                (GenerationKind::TypeDecl(false, None), &["Field", "Variant", "TypeDeclKind", "TypeDecl"]),
                (GenerationKind::TypeDecl(false, Some(DeriveVisitors {
                    name: "const_generic",
                    ancestor: Some("literal"),
                    reduce: true,
                    ord: true,
                    extra_types: &[
                        "type_decl_id",
                        "global_decl_id",
                        "const_generic_var_id",
                    ],
                })), &[
                    "ConstGeneric",
                ]),
                (GenerationKind::TypeDecl(false, Some(DeriveVisitors {
                    name: "ty",
                    ancestor: Some("ty_base"),
                    reduce: false,
                    ord: true,
                    extra_types: &[],
                })), &[
                ]),
            ]),
        },
        GenerateCodeFor {
            template: output_dir.join("templates/Values.ml"),
            target: output_dir.join("generated/Values.ml"),
            markers: ctx.markers_from_names(&[
                (GenerationKind::TypeDecl(true, Some(DeriveVisitors {
                    name: "literal",
                    ancestor: Some("literal_base"),
                    reduce: true,
                    ord: true,
                    extra_types: &[],
                })), &[
                    "IntegerTy",
                    "FloatTy",
                    "FloatValue",
                    "LiteralTy",
                    "Literal",
                ]),
            ]),
        },
        GenerateCodeFor {
            template: output_dir.join("templates/LlbcAst.ml"),
            target: output_dir.join("generated/LlbcAst.ml"),
            markers: ctx.markers_from_names(&[
                (GenerationKind::TypeDecl(true, Some(DeriveVisitors {
                    name: "statement",
                    ancestor: Some("statement_base"),
                    reduce: false,
                    ord: false,
                    extra_types: &[],
                })), &[
                    "charon_lib::ast::llbc_ast::Statement",
                    "charon_lib::ast::llbc_ast::Switch",
                ]),
            ]),
        },
        GenerateCodeFor {
            template: output_dir.join("templates/UllbcAst.ml"),
            target: output_dir.join("generated/UllbcAst.ml"),
            markers: ctx.markers_from_names(&[
                (GenerationKind::TypeDecl(false, Some(DeriveVisitors {
                    name: "statement",
                    ancestor: Some("GAst.statement_base"),
                    reduce: false,
                    ord: false,
                    extra_types: &[
                        "block_id",
                    ],
                })), &[
                    "charon_lib::ast::ullbc_ast::Statement",
                    "charon_lib::ast::ullbc_ast::RawStatement",
                ]),
                (GenerationKind::TypeDecl(false, Some(DeriveVisitors {
                    name: "switch",
                    ancestor: Some("statement"),
                    reduce: false,
                    ord: false,
                    extra_types: &[],
                })), &[
                    "charon_lib::ast::ullbc_ast::SwitchTargets",
                ]),
                (GenerationKind::TypeDecl(false, Some(DeriveVisitors {
                    name: "terminator",
                    ancestor: Some("switch"),
                    reduce: false,
                    ord: false,
                    extra_types: &[],
                })), &[
                    "charon_lib::ast::ullbc_ast::Terminator",
                    "charon_lib::ast::ullbc_ast::RawTerminator",
                ]),
                (GenerationKind::TypeDecl(false, None), &[
                    "charon_lib::ast::ullbc_ast::BlockData",
                    "charon_lib::ast::ullbc_ast::BodyContents",
                ]),
            ]),
        },
        GenerateCodeFor {
            template: output_dir.join("templates/GAstOfJson.ml"),
            target: output_dir.join("generated/GAstOfJson.ml"),
            markers: vec![(GenerationKind::OfJson, gast_types)],
        },
        GenerateCodeFor {
            template: output_dir.join("templates/LlbcOfJson.ml"),
            target: output_dir.join("generated/LlbcOfJson.ml"),
            markers: vec![(GenerationKind::OfJson, llbc_types)],
        },
        GenerateCodeFor {
            template: output_dir.join("templates/UllbcOfJson.ml"),
            target: output_dir.join("generated/UllbcOfJson.ml"),
            markers: vec![(GenerationKind::OfJson, ullbc_types)],
        },
    ];
    for file in generate_code_for {
        file.generate(&ctx)?;
    }
    Ok(())
}
