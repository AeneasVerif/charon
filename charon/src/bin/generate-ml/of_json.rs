use std::collections::HashMap;

use charon_lib::ast::*;
use indoc::indoc;
use itertools::Itertools;

use crate::GenerateCtx;
use crate::util::*;

const MANUAL_IMPLS: &[(&str, &str)] = &[
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
            let file = FileTbl.find ctx.id_to_file_map file_id in
            Ok file
            "#,
        ),
    ),
    (
        "File",
        indoc!(
            r#"
            (match json with
            | `Assoc
                [ ("id", id); ("name", name); ("crate_name", crate_name); ("contents", contents) ]
            ->
                let* id = FileId.id_of_json ctx id in
                let* name = file_name_of_json ctx name in
                let* crate_name = string_of_json ctx crate_name in
                let* contents = option_of_json string_of_json ctx contents in
                let file: file = { name; crate_name; contents } in
                FileTbl.add ctx.id_to_file_map id file;
                Ok file
            | _ -> Error "")
            "#
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

impl<'a> GenerateCtx<'a> {
    fn build_function(&self, decl: &TypeDecl, branches: &str) -> String {
        let ty = TyKind::Adt(TypeDeclRef {
            id: TypeId::Adt(decl.def_id),
            generics: decl.generics.identity_args().into(),
        })
        .into_ty();
        let (ty_name, _) = self.type_to_ocaml_ident_raw(decl);
        let ty = self.type_to_ocaml_name(&ty);
        let signature = if decl.generics.types.is_empty() {
            format!("{ty_name}_of_json (ctx : of_json_ctx) (js : json) : ({ty}, string) result =")
        } else {
            let types = &decl.generics.types;
            let gen_vars_space = types
                .iter()
                .enumerate()
                .map(|(i, _)| format!("'a{i}"))
                .join(" ");

            let mut args = Vec::new();
            let mut ty_args = Vec::new();
            for (i, _) in types.iter().enumerate() {
                args.push(format!("arg{i}_of_json"));
                ty_args.push(format!("(of_json_ctx -> json -> ('a{i}, string) result)"));
            }
            args.push("ctx".to_string());
            ty_args.push("of_json_ctx".to_string());
            args.push("js".to_string());
            ty_args.push("json".to_string());

            let ty_args = ty_args.into_iter().join(" -> ");
            let args = args.into_iter().join(" ");
            let fun_ty = format!("{gen_vars_space}. {ty_args} -> ({ty}, string) result");
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

    /// Converts a type to the appropriate `*_of_json` call. In case of generics, this combines several
    /// functions, e.g. `list_of_json bool_of_json`.
    fn type_to_ocaml_call(&self, ty: &Ty) -> String {
        match ty.kind() {
            TyKind::Literal(LiteralTy::Bool) => "bool_of_json".to_string(),
            TyKind::Literal(LiteralTy::Char) => "char_of_json".to_string(),
            TyKind::Literal(LiteralTy::Int(int_ty)) => match int_ty {
                // Even though OCaml ints are only 63 bits, only scalars with their 128 bits should be able to become too large
                IntTy::I128 => "big_int_of_json".to_string(),
                _ => "int_of_json".to_string(),
            },
            TyKind::Literal(LiteralTy::UInt(uint_ty)) => match uint_ty {
                // Even though OCaml ints are only 63 bits, only scalars with their 128 bits should be able to become too large
                UIntTy::U128 => "big_int_of_json".to_string(),
                _ => "int_of_json".to_string(),
            },
            TyKind::Literal(LiteralTy::Float(_)) => "float_of_json".to_string(),
            TyKind::Adt(tref) => {
                let mut expr = Vec::new();
                for ty in &tref.generics.types {
                    expr.push(self.type_to_ocaml_call(ty))
                }
                match tref.id {
                    TypeId::Adt(id) => {
                        let mut first = if let Some(tdecl) = self.crate_data.type_decls.get(id) {
                            let (name, module) = self.type_to_ocaml_ident_raw(tdecl);
                            match module {
                                Some((_, short)) if !self.current_ids.contains(&id) => {
                                    format!("{short}.{name}")
                                }
                                _ => name,
                            }
                        } else {
                            format!("missing_type_{id}")
                        };
                        if first == "vec" {
                            first = "list".to_string();
                        }
                        if first == "ustr" {
                            first = "string".to_string();
                        }
                        if first == "index_map" {
                            // That's the `indexmap::IndexMap` case. Pass something dummy for the
                            // `RandomState` parameter.
                            expr[2] = "int_of_json".to_string();
                        }

                        if first == "indexed_map" && self.use_opt_index_map() {
                            first = format!("opt_{first}");
                        }

                        expr.insert(0, first + "_of_json");
                    }
                    TypeId::Builtin(BuiltinTy::Box) => expr.insert(0, "box_of_json".to_owned()),
                    TypeId::Tuple => {
                        let name = match tref.generics.types.len() {
                            2 => "pair_of_json".to_string(),
                            3 => "triple_of_json".to_string(),
                            len => format!("tuple_{len}_of_json"),
                        };
                        expr.insert(0, name);
                    }
                    _ => unimplemented!("{ty:?}"),
                }
                expr.into_iter().map(|f| format!("({f})")).join(" ")
            }
            TyKind::TypeVar(DeBruijnVar::Free(id)) => format!("arg{id}_of_json"),
            _ => unimplemented!("{ty:?}"),
        }
    }

    fn convert_vars<'b>(&self, fields: impl IntoIterator<Item = &'b Field>) -> String {
        fields
            .into_iter()
            .filter(|f| !f.is_opaque())
            .map(|f| {
                let name = make_ocaml_ident(f.name.as_deref().unwrap());
                let rename = make_ocaml_ident(f.renamed_name().unwrap());
                let convert = self.type_to_ocaml_call(&f.ty);
                format!("let* {rename} = {convert} ctx {name} in")
            })
            .join("\n")
    }

    fn build_branch<'b>(
        &self,
        pat: &str,
        fields: impl IntoIterator<Item = &'b Field>,
        construct: &str,
    ) -> String {
        let convert = self.convert_vars(fields);
        format!("| {pat} -> {convert} Ok ({construct})")
    }

    fn type_decl_to_json_deserializer(
        &self,
        manual_impls: &HashMap<TypeDeclId, String>,
        decl: &TypeDecl,
    ) -> String {
        let return_ty = self.type_to_ocaml_ident(decl);
        let return_ty = if decl.generics.types.is_empty() {
            return_ty
        } else {
            format!("_ {return_ty}")
        };

        let branches = match &decl.kind {
            _ if let Some(def) = manual_impls.get(&decl.def_id) => {
                format!("| json -> {def}")
            }
            TypeDeclKind::Struct(fields) if fields.is_empty() => {
                self.build_branch("`Null", fields, "()")
            }
            TypeDeclKind::Struct(fields)
                if fields.len() == 1
                    && fields[0].name.as_ref().is_some_and(|name| name == "_raw") =>
            {
                // These are the special strongly-typed integers.
                let short_name = name_str(&decl.item_meta.name).clone();
                format!("| x -> {short_name}.id_of_json ctx x")
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
                let call = self.type_to_ocaml_call(ty);
                format!("| x -> {call} ctx x")
            }
            TypeDeclKind::Alias(ty) => {
                let call = self.type_to_ocaml_call(ty);
                format!("| x -> {call} ctx x")
            }
            TypeDeclKind::Struct(fields) if fields.iter().all(|f| f.name.is_none()) => {
                let mut fields = fields.clone();
                for (i, f) in fields.iter_mut().enumerate() {
                    f.name = Some(format!("x{i}"));
                }
                let pat: String = fields
                    .iter()
                    .map(|f| f.name.as_deref().unwrap())
                    .map(make_ocaml_ident)
                    .join(";");
                let pat = format!("`List [ {pat} ]");
                let construct = fields
                    .iter()
                    .map(|f| f.renamed_name().unwrap())
                    .map(make_ocaml_ident)
                    .join(", ");
                let construct = format!("( {construct} )");
                self.build_branch(&pat, &fields, &construct)
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
                    .map(make_ocaml_ident)
                    .join("; ");
                let construct = format!("({{ {construct} }} : {return_ty})");
                self.build_branch(&pat, fields, &construct)
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
                            self.build_branch(&pat, &variant.fields, rename)
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
                            self.build_branch(&pat, &fields, &construct)
                        }
                    })
                    .join("\n")
            }
            TypeDeclKind::Union(..) => todo!(),
            TypeDeclKind::Opaque => todo!(),
            TypeDeclKind::Error(_) => todo!(),
        };
        self.build_function(decl, &branches)
    }

    pub fn type_decls_to_json(&mut self, tys: Vec<&TypeDecl>) -> String {
        let manual_impls = self.names_to_type_id_map(MANUAL_IMPLS);
        let fns = tys
            .iter()
            .map(|ty| {
                self.with_item(ty, |ctx| {
                    ctx.type_decl_to_json_deserializer(&manual_impls, ty)
                })
            })
            .format("\n");
        format!("let rec ___ = ()\n{fns}")
    }
}
