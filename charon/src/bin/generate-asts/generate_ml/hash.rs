use std::collections::HashMap;

use charon_lib::ast::*;
use itertools::Itertools;

use super::GenerateCtx;

/// Hand-written bodies, for the types that have a hand-written definition in `to_ocaml_ty.rs`.
/// The value to hash is bound to `x`.
const MANUAL_IMPLS: &[(&str, &str)] = &[
    ("FileId", "hash_file x"),
    (
        "ConstantExpr",
        "HashBasic.combine (hash_constant_expr_kind x.kind) (hash_ty x.ty)",
    ),
    ("HashConsed", "hash_a0 x"),
];

/// Combine the hashes of the components of a value, starting from `start`.
fn combine_hashes(start: String, hashes: impl IntoIterator<Item = String>) -> String {
    hashes
        .into_iter()
        .fold(start, |acc, h| format!("HashBasic.combine ({acc}) ({h})"))
}

impl<'a> GenerateCtx<'a> {
    /// Converts a type to an expression that hashes values of that type. This mirrors
    /// `type_to_ocaml_name`.
    fn type_to_hash_fn(&self, ty: &Ty) -> String {
        match ty.kind() {
            TyKind::Scalar(ScalarTy::Bool) => "HashBasic.hash_bool".to_string(),
            TyKind::Scalar(ScalarTy::Char) => "hash_char_value".to_string(),
            TyKind::Scalar(ScalarTy::Integer(
                IntegerTy::Signed(IntTy::I128) | IntegerTy::Unsigned(UIntTy::U128),
            )) => "hash_big_int".to_string(),
            TyKind::Scalar(ScalarTy::Integer(_)) => "HashBasic.hash_int".to_string(),
            TyKind::Adt(tref) => {
                let mut args = tref
                    .generics
                    .types
                    .iter()
                    .map(|ty| self.type_to_hash_fn(ty))
                    .collect_vec();
                let base = match tref.as_builtin() {
                    None => {
                        let tdecl = &self.crate_data.type_decls[tref.id];
                        let base_ty = self.type_to_ocaml_ident(tdecl);
                        match base_ty.as_str() {
                            "vec" => "HashBasic.hash_list".to_string(),
                            "ustr" | "string" => "HashBasic.hash_string".to_string(),
                            "option" => "HashBasic.hash_option".to_string(),
                            "with_cached_type_info" => return args.remove(0),
                            "indexed_map" => {
                                args.remove(0);
                                let index_name = self.type_to_ocaml_name(&tref.generics.types[0]);
                                format!("hash_{index_name}_map")
                            }
                            "index_vec" => {
                                args.remove(0);
                                "HashBasic.hash_list".to_string()
                            }
                            "index_map" => {
                                // That's the `indexmap::IndexMap` case, which is a list of pairs.
                                let (hash_k, hash_v) = (&args[0], &args[1]);
                                return format!(
                                    "(HashBasic.hash_list (fun (k, v) -> \
                                     HashBasic.combine ({hash_k} k) ({hash_v} v)))"
                                );
                            }
                            _ => match base_ty.rsplit_once('.') {
                                Some((module, name)) => format!("{module}.hash_{name}"),
                                None => format!("hash_{base_ty}"),
                            },
                        }
                    }
                    Some(BuiltinAdt::Box) => return args.remove(0),
                    Some(BuiltinAdt::Tuple) => {
                        let vars = (0..args.len()).map(|i| format!("x{i}")).join(", ");
                        let hashes = args
                            .iter()
                            .enumerate()
                            .map(|(i, hash)| format!("{hash} x{i}"));
                        return format!(
                            "(fun ({vars}) -> {})",
                            combine_hashes("0".to_string(), hashes)
                        );
                    }
                    _ => unimplemented!("{ty:?}"),
                };
                if args.is_empty() {
                    base
                } else {
                    format!(
                        "({base} {})",
                        args.iter().map(|a| format!("({a})")).join(" ")
                    )
                }
            }
            TyKind::TypeVar(DeBruijnVar::Free(id) | DeBruijnVar::Bound(_, id)) => {
                format!("hash_a{id}")
            }
            _ => unimplemented!("{ty:?}"),
        }
    }

    /// Generate the hash function for `decl`. This mirrors `type_decl_to_ocaml_decl`.
    fn type_decl_to_hash(
        &self,
        manual_impls: &HashMap<TypeDeclId, String>,
        decl: &TypeDecl,
        co_rec: bool,
    ) -> String {
        let body = match &decl.kind {
            _ if let Some(def) = manual_impls.get(&decl.def_id) => def.clone(),
            TypeDeclKind::Alias(ty) => format!("{} x", self.type_to_hash_fn(ty)),
            TypeDeclKind::Struct(fields) if fields.is_empty() => "0".to_string(),
            TypeDeclKind::Struct(fields) if fields.len() == 1 && fields[0].name == "_raw" => {
                // These are the special strongly-typed integers.
                let short_name = decl.item_meta.name.short_str().unwrap();
                format!("{short_name}.hash_id x")
            }
            TypeDeclKind::Struct(fields)
                if fields.len() == 1
                    && (fields[0].is_positional
                        || decl
                            .item_meta
                            .attr_info
                            .attributes
                            .iter()
                            .any(|a| a.is_transparent())) =>
            {
                format!("{} x", self.type_to_hash_fn(&fields[0].ty))
            }
            TypeDeclKind::Struct(fields) if fields.iter().all(|field| field.is_positional) => {
                let fields = fields.iter().filter(|f| !f.is_opaque()).collect_vec();
                let vars = (0..fields.len()).map(|i| format!("x{i}")).join(", ");
                let hashes = fields
                    .iter()
                    .enumerate()
                    .map(|(i, f)| format!("{} x{i}", self.type_to_hash_fn(&f.ty)));
                format!(
                    "let ({vars}) = x in {}",
                    combine_hashes("0".to_string(), hashes)
                )
            }
            TypeDeclKind::Struct(fields) => {
                let hashes = fields.iter().filter(|f| !f.is_opaque()).map(|f| {
                    let name = f.renamed_name();
                    format!("{} x.{name}", self.type_to_hash_fn(&f.ty))
                });
                combine_hashes("0".to_string(), hashes)
            }
            TypeDeclKind::Enum(variants) => {
                let branches = variants
                    .iter()
                    .filter(|v| !v.is_opaque())
                    .enumerate()
                    .map(|(i, variant)| {
                        let rename = variant.renamed_name();
                        let vars = (0..variant.fields.len())
                            .map(|i| format!("x{i}"))
                            .join(", ");
                        let pat = if variant.fields.is_empty() {
                            rename.to_string()
                        } else {
                            format!("{rename} ({vars})")
                        };
                        let hashes = variant
                            .fields
                            .iter()
                            .enumerate()
                            .map(|(i, f)| format!("{} x{i}", self.type_to_hash_fn(&f.ty)));
                        format!("| {pat} -> {}", combine_hashes(i.to_string(), hashes))
                    })
                    .join("\n");
                format!("match x with {branches}")
            }
            TypeDeclKind::Union(..) => todo!(),
            TypeDeclKind::Opaque => todo!(),
            TypeDeclKind::Error(_) => todo!(),
        };

        let (ty_name, _) = self.type_to_ocaml_ident_raw(decl);
        let num_generics = decl.generics.types.len();
        // The polymorphic annotation is needed because types can be used at several
        // instantiations within the same recursive group.
        let (poly, hash_args, hash_args_ty, ty, ty_pat) = if num_generics == 0 {
            (
                String::new(),
                String::new(),
                String::new(),
                ty_name.clone(),
                ty_name.clone(),
            )
        } else {
            let vars = (0..num_generics).map(|i| format!("'a{i}")).collect_vec();
            let poly = format!("{}.", vars.iter().join(" "));
            let hash_args = (0..num_generics).map(|i| format!("hash_a{i}")).join(" ");
            let hash_args_ty = vars.iter().map(|v| format!("({v} -> int) -> ")).join("");
            let (ty, ty_pat) = if num_generics == 1 {
                (format!("'a0 {ty_name}"), format!("_ {ty_name}"))
            } else {
                let underscores = vec!["_"; num_generics].join(", ");
                (
                    format!("({}) {ty_name}", vars.iter().join(", ")),
                    format!("({underscores}) {ty_name}"),
                )
            };
            (poly, hash_args, hash_args_ty, ty, ty_pat)
        };
        let keyword = if co_rec { "and" } else { "let rec" };
        format!(
            "\n{keyword} hash_{ty_name} : {poly} {hash_args_ty}{ty} -> int = \
             fun {hash_args} (x : {ty_pat}) -> {body}"
        )
    }

    pub fn type_decls_to_hash(&self, tys: &[&TypeDecl]) -> String {
        let manual_impls = self.names_to_type_id_map(MANUAL_IMPLS);
        tys.iter()
            .enumerate()
            .map(|(i, ty)| self.type_decl_to_hash(&manual_impls, ty, i != 0))
            .join("\n")
    }
}
