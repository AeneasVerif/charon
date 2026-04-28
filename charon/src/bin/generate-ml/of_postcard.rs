use std::collections::HashMap;

use charon_lib::ast::*;
use indoc::indoc;
use itertools::Itertools;

use crate::GenerateCtx;
use crate::util::*;

const MANUAL_IMPLS: &[(&str, &str)] = &[
    (
        "charon_lib::ids::index_vec::IndexVec",
        "list_of_postcard arg1_of_postcard ctx st",
    ),
    (
        "charon_lib::ids::index_map::IndexMap",
        indoc!(
            r#"
            let* list = list_of_postcard (option_of_postcard arg1_of_postcard) ctx st in
            Ok (List.filter_map (fun x -> x) list)
            "#
        ),
    ),
    (
        "indexmap::map::IndexMap",
        "list_of_postcard (key_value_pair_of_postcard arg0_of_postcard arg1_of_postcard) ctx st",
    ),
    (
        "FileId",
        indoc!(
            r#"
            let* file_id = FileId.id_of_postcard ctx st in
            try Ok (FileTbl.find ctx.id_to_file_map file_id)
            with Not_found ->
              let valid_keys = FileTbl.fold (fun key _ acc -> FileId.to_string key :: acc) ctx.id_to_file_map [] in
              Error ("unknown file id: " ^ FileId.to_string file_id ^ ". valid ids are: " ^ String.concat ", " valid_keys)
            "#
        ),
    ),
    (
        "File",
        indoc!(
            r#"
            let* id = FileId.id_of_postcard ctx st in
            let* name = file_name_of_postcard ctx st in
            let* crate_name = string_of_postcard ctx st in
            let* contents = option_of_postcard string_of_postcard ctx st in
            let file: file = { name; crate_name; contents } in
            FileTbl.add ctx.id_to_file_map id file;
            Ok file
            "#
        ),
    ),
    (
        "HashConsed",
        r#"Error "use `hash_consed_val_of_postcard` instead""#,
    ),
    (
        "Ty",
        "hash_consed_val_of_postcard ctx.ty_hashcons_map ty_kind_of_postcard ctx st",
    ),
    (
        "TraitRef",
        "hash_consed_val_of_postcard ctx.tref_hashcons_map trait_ref_contents_of_postcard ctx st",
    ),
];

impl<'a> GenerateCtx<'a> {
    fn build_postcard_function(&self, decl: &TypeDecl, body: &str) -> String {
        let ty = TyKind::Adt(TypeDeclRef {
            id: TypeId::Adt(decl.def_id),
            generics: decl.generics.identity_args().into(),
        })
        .into_ty();
        let (ty_name, _) = self.type_to_ocaml_ident_raw(decl);
        let ty = self.type_to_ocaml_name(&ty);
        let signature = if decl.generics.types.is_empty() {
            format!(
                "{ty_name}_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) : ({ty}, string) result ="
            )
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
                args.push(format!("arg{i}_of_postcard"));
                ty_args.push(format!(
                    "(of_postcard_ctx -> postcard_state -> ('a{i}, string) result)"
                ));
            }
            args.push("ctx".to_string());
            ty_args.push("of_postcard_ctx".to_string());
            args.push("st".to_string());
            ty_args.push("postcard_state".to_string());

            let ty_args = ty_args.into_iter().join(" -> ");
            let args = args.into_iter().join(" ");
            let fun_ty = format!("{gen_vars_space}. {ty_args} -> ({ty}, string) result");
            format!("{ty_name}_of_postcard : {fun_ty} = fun {args} ->")
        };
        format!(
            r#"
        and {signature}
          combine_error_msgs st __FUNCTION__
            ({body})
        "#
        )
    }

    fn type_to_ocaml_postcard_call(&self, ty: &Ty) -> String {
        match ty.kind() {
            TyKind::Literal(LiteralTy::Bool) => "bool_of_postcard".to_string(),
            TyKind::Literal(LiteralTy::Char) => "char_of_postcard".to_string(),
            TyKind::Literal(LiteralTy::Int(int_ty)) => match int_ty {
                IntTy::Isize => "isize_of_postcard".to_string(),
                IntTy::I8 => "i8_of_postcard".to_string(),
                IntTy::I16 => "i16_of_postcard".to_string(),
                IntTy::I32 => "i32_of_postcard".to_string(),
                IntTy::I64 => "i64_of_postcard".to_string(),
                IntTy::I128 => "big_int_of_postcard".to_string(),
            },
            TyKind::Literal(LiteralTy::UInt(uint_ty)) => match uint_ty {
                UIntTy::Usize => "usize_of_postcard".to_string(),
                UIntTy::U8 => "u8_of_postcard".to_string(),
                UIntTy::U16 => "u16_of_postcard".to_string(),
                UIntTy::U32 => "u32_of_postcard".to_string(),
                UIntTy::U64 => "u64_of_postcard".to_string(),
                UIntTy::U128 => "big_uint_of_postcard".to_string(),
            },
            TyKind::Literal(LiteralTy::Float(FloatTy::F32)) => "f32_of_postcard".to_string(),
            TyKind::Literal(LiteralTy::Float(_)) => "float_of_postcard".to_string(),
            TyKind::Adt(tref) => {
                let mut expr = Vec::new();
                for ty in &tref.generics.types {
                    expr.push(self.type_to_ocaml_postcard_call(ty))
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
                            expr[2] = "int_of_postcard".to_string();
                        }

                        if first == "indexed_map" && self.use_opt_index_map() {
                            first = format!("opt_{first}");
                        }

                        expr.insert(0, first + "_of_postcard");
                    }
                    TypeId::Builtin(BuiltinTy::Box) => expr.insert(0, "box_of_postcard".to_owned()),
                    TypeId::Tuple => {
                        let name = match tref.generics.types.len() {
                            2 => "pair_of_postcard".to_string(),
                            3 => "triple_of_postcard".to_string(),
                            len => format!("tuple_{len}_of_postcard"),
                        };
                        expr.insert(0, name);
                    }
                    _ => unimplemented!("{ty:?}"),
                }
                expr.into_iter().map(|f| format!("({f})")).join(" ")
            }
            TyKind::TypeVar(DeBruijnVar::Free(id)) => format!("arg{id}_of_postcard"),
            _ => unimplemented!("{ty:?}"),
        }
    }

    fn convert_postcard_vars<'b>(&self, fields: impl IntoIterator<Item = &'b Field>) -> String {
        fields
            .into_iter()
            .map(|f| {
                let rename = if f.is_opaque() {
                    "_".to_string()
                } else {
                    make_ocaml_ident(f.renamed_name().unwrap())
                };
                let convert = self.type_to_ocaml_postcard_call(&f.ty);
                format!("let* {rename} = {convert} ctx st in")
            })
            .join("\n")
    }

    fn type_decl_to_postcard_deserializer(
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

        let body = match &decl.kind {
            _ if let Some(def) = manual_impls.get(&decl.def_id) => def.clone(),
            TypeDeclKind::Struct(fields) if fields.is_empty() => "Ok ()".to_string(),
            TypeDeclKind::Struct(fields)
                if fields.len() == 1
                    && fields[0].name.as_ref().is_some_and(|name| name == "_raw") =>
            {
                let short_name = &decl.item_meta.name.short_str();
                format!("{short_name}.id_of_postcard ctx st")
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
                let call = self.type_to_ocaml_postcard_call(&fields[0].ty);
                format!("{call} ctx st")
            }
            TypeDeclKind::Alias(ty) => {
                let call = self.type_to_ocaml_postcard_call(ty);
                format!("{call} ctx st")
            }
            TypeDeclKind::Struct(fields) if fields.iter().all(|f| f.name.is_none()) => {
                let mut fields = fields.clone();
                for (i, f) in fields.iter_mut().enumerate() {
                    f.name = Some(format!("x{i}"));
                }
                let convert = self.convert_postcard_vars(&fields);
                let construct = fields
                    .iter()
                    .map(|f| f.renamed_name().unwrap())
                    .map(make_ocaml_ident)
                    .join(", ");
                format!("{convert}\nOk ({construct})")
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
                let convert = self.convert_postcard_vars(fields.iter().copied());
                let construct = fields
                    .iter()
                    .filter(|f| !f.is_opaque())
                    .map(|f| f.renamed_name().unwrap())
                    .map(make_ocaml_ident)
                    .join("; ");
                format!("{convert}\nOk (({{ {construct} }} : {return_ty}))")
            }
            TypeDeclKind::Enum(variants) => {
                let branches = variants
                    .iter()
                    .enumerate()
                    .filter_map(|(i, variant)| {
                        if variant.is_opaque() {
                            return None;
                        }
                        let rename = variant.renamed_name();
                        let idx = i as u32;
                        if variant.fields.is_empty() {
                            Some(format!("| {idx} -> Ok {rename}"))
                        } else {
                            let mut fields = variant.fields.clone();
                            if fields.iter().all(|f| f.name.is_none()) {
                                for (j, f) in fields.iter_mut().enumerate() {
                                    f.name = Some(format!("x_{j}"));
                                }
                            }
                            let convert = self.convert_postcard_vars(&fields);
                            let construct_fields = fields
                                .iter()
                                .map(|f| f.name.as_ref().unwrap())
                                .map(|n| make_ocaml_ident(n))
                                .join(", ");
                            let construct = format!("{rename} ({construct_fields})");
                            Some(format!("| {idx} -> {convert}\n  Ok ({construct})"))
                        }
                    })
                    .join("\n");
                format!(
                    "let* __tag = int_of_postcard ctx st in\nmatch __tag with\n{branches}\n| _ -> Error (\"unknown enum variant tag: \" ^ string_of_int __tag)"
                )
            }
            TypeDeclKind::Union(..) => todo!(),
            TypeDeclKind::Opaque => todo!(),
            TypeDeclKind::Error(_) => todo!(),
        };
        self.build_postcard_function(decl, &body)
    }

    pub fn type_decls_to_postcard(&mut self, tys: Vec<&TypeDecl>) -> String {
        let manual_impls = self.names_to_type_id_map(MANUAL_IMPLS);
        let fns = tys
            .iter()
            .map(|ty| {
                self.with_item(ty, |ctx| {
                    ctx.type_decl_to_postcard_deserializer(&manual_impls, ty)
                })
            })
            .format("\n");
        format!("let rec ___ = ()\n{fns}")
    }
}
