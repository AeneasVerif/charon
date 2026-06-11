//! Generate Rust definitions and translation code for rustc's parsed attributes.
//!
//! This binary runs Charon on `rustc_hir::attrs::AttributeKind`, then uses the translated type
//! declarations to generate Charon-owned attribute types and rustc-to-Charon conversion code.

use anyhow::{Context, Result, bail};
use assert_cmd::cargo::CommandCargoExt;
use charon_lib::ast::*;
use charon_lib::ids::IndexVec;
use charon_lib::options::SerializationFormat;
use convert_case::{Case, Casing};
use itertools::Itertools;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::fs;
use std::process::Command;

const ATTRIBUTE_KIND: &str = "rustc_hir::attrs::data_structures::AttributeKind";

/// Hand-selected list of attributes that feel user-facing enough and stable enough to expose.
/// Some of this info is better represented somewhere else, e.g. `repr` stuff belongs in `Layout`.
const ATTRIBUTE_KIND_VARIANTS: &[&str] = &[
    "AutomaticallyDerived",
    "Cold",
    "EiiDeclaration",
    "EiiImpls",
    "Fundamental",
    "Ignore",
    "Inline",
    "Lang",
    "MayDangle",
    "Naked",
    "NoLink",
    "NoMangle",
    "NonExhaustive",
    "Optimize",
    "RustcDiagnosticItem",
    "RustcIntrinsic",
    "TargetFeature",
    "TrackCaller",
];

pub(crate) fn main() -> Result<()> {
    let crate_data = translate_rustc_attributes()?;
    let generator = Generator::new(&crate_data)?;
    generator.write_files()?;
    Ok(())
}

fn translate_rustc_attributes() -> Result<TranslatedCrate> {
    let temp_dir = tempfile::tempdir().context("failed to create temp dir")?;
    let rust_file = temp_dir.path().join("rustc_hir_attr.rs");
    let llbc_file = temp_dir.path().join("rustc_hir_attr.ullbc");
    fs::write(
        &rust_file,
        indoc::indoc! {r#"
            #![feature(rustc_private)]
            extern crate rustc_hir;
            use rustc_hir::attrs::AttributeKind;

            fn main() {
                let _ = core::mem::size_of::<AttributeKind>();
            }
        "#},
    )
    .context("failed to write temporary rustc_hir input")?;

    let mut cmd = Command::cargo_bin("charon")?;
    cmd.arg("rustc");
    cmd.arg("--ullbc");
    cmd.arg("--hide-marker-traits");
    cmd.arg("--hide-allocator");
    cmd.arg("--treat-box-as-builtin");
    cmd.arg(format!("--start-from={ATTRIBUTE_KIND}"));
    cmd.arg("--sysroot=default");
    cmd.arg("--dest-file");
    cmd.arg(&llbc_file);
    cmd.arg("--");
    cmd.arg(&rust_file);

    let output = cmd.output().context("failed to run Charon on rustc_hir")?;
    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        bail!("failed to translate rustc_hir attributes:\n{stderr}");
    }

    charon_lib::deserialize_llbc_with_format(&llbc_file, SerializationFormat::Json)
        .context("failed to deserialize generated rustc_hir ULLBC")
}

struct Generator<'a> {
    crate_data: &'a TranslatedCrate,
    names: HashMap<TypeDeclId, String>,
    path_to_id: HashMap<String, TypeDeclId>,
    generated: BTreeSet<TypeDeclId>,
    local_names: HashMap<TypeDeclId, String>,
}

impl<'a> Generator<'a> {
    fn new(crate_data: &'a TranslatedCrate) -> Result<Self> {
        let mut names = HashMap::new();
        let mut path_to_id = HashMap::new();
        for decl in &crate_data.type_decls {
            let name = repr_name(&decl.item_meta.name);
            path_to_id.insert(name.clone(), decl.def_id);
            names.insert(decl.def_id, name);
        }

        let mut generator = Generator {
            crate_data,
            names,
            path_to_id,
            generated: BTreeSet::new(),
            local_names: HashMap::new(),
        };
        generator.generated = generator.compute_generated_decls()?;
        generator.local_names = generator.compute_local_names()?;
        Ok(generator)
    }

    fn write_files(&self) -> Result<()> {
        fs::write("src/ast/attributes.rs", self.generate_attributes_file())
            .context("failed to write src/ast/attributes.rs")?;
        fs::write(
            "src/bin/charon-driver/translate/translate_attrs.rs",
            self.generate_translate_attrs_file(),
        )
        .context("failed to write translate_attrs.rs")?;
        Ok(())
    }

    fn attribute_kind_id(&self) -> Result<TypeDeclId> {
        self.path_to_id
            .get(ATTRIBUTE_KIND)
            .copied()
            .with_context(|| format!("could not find translated `{ATTRIBUTE_KIND}`"))
    }

    fn compute_generated_decls(&self) -> Result<BTreeSet<TypeDeclId>> {
        let mut generated = BTreeSet::new();
        let mut stack = vec![self.attribute_kind_id()?];
        while let Some(id) = stack.pop() {
            if generated.contains(&id) || !self.should_generate_decl(id) {
                continue;
            }
            generated.insert(id);
            let decl = &self.crate_data[id];
            for field in self.fields(decl) {
                self.push_generated_dependencies(&field.ty, &mut stack);
            }
            if let TypeDeclKind::Alias(ty) = &decl.kind {
                self.push_generated_dependencies(ty, &mut stack);
            }
        }
        Ok(generated)
    }

    fn compute_local_names(&self) -> Result<HashMap<TypeDeclId, String>> {
        let mut by_name: BTreeMap<String, Vec<TypeDeclId>> = BTreeMap::new();
        for &id in &self.generated {
            by_name
                .entry(self.generated_type_name(id))
                .or_default()
                .push(id);
        }

        let duplicates = by_name
            .iter()
            .filter(|(_, ids)| ids.len() > 1)
            .map(|(name, ids)| {
                let paths = ids.iter().map(|id| self.name(*id)).join(", ");
                format!("{name}: {paths}")
            })
            .collect_vec();
        if !duplicates.is_empty() {
            bail!(
                "duplicate generated type names; add a disambiguation rule:\n{}",
                duplicates.join("\n")
            );
        }

        Ok(self
            .generated
            .iter()
            .map(|&id| (id, self.generated_type_name(id)))
            .collect())
    }

    fn generated_type_name(&self, id: TypeDeclId) -> String {
        if self.is_attribute_kind(id) {
            "BuiltinAttr".to_string()
        } else {
            self.short_name(id)
        }
    }

    fn should_generate_decl(&self, id: TypeDeclId) -> bool {
        let decl = &self.crate_data[id];
        if self.special_adt(id).is_some()
            || !decl.generics.regions.is_empty()
            || !decl.generics.types.is_empty()
            || !decl.generics.const_generics.is_empty()
            || !matches!(
                decl.kind,
                TypeDeclKind::Struct(_)
                    | TypeDeclKind::Enum(_)
                    | TypeDeclKind::Union(_)
                    | TypeDeclKind::Alias(_)
            )
        {
            return false;
        }

        let name = self.name(id);
        name.starts_with("rustc_hir::attrs::")
            || name.starts_with("rustc_hir::limit::")
            || name.starts_with("rustc_hir::stability::")
            || name.starts_with("rustc_hir::lang_items::")
            || name.starts_with("rustc_ast::attr::")
            || name.starts_with("rustc_ast::expand::autodiff_attrs::")
            || name.starts_with("rustc_ast::token::")
            || name.starts_with("rustc_ast_ir::")
            || name == "rustc_ast::ast::AttrStyle"
            || name == "rustc_span::symbol::Ident"
            || name == "rustc_span::hygiene::Transparency"
    }

    fn push_generated_dependencies(&self, ty: &Ty, stack: &mut Vec<TypeDeclId>) {
        match ty.kind() {
            TyKind::Adt(tref) => match tref.id {
                TypeId::Adt(id) => {
                    if self.special_adt(id).is_none() && self.should_generate_decl(id) {
                        stack.push(id);
                    }
                    for ty in &tref.generics.types {
                        self.push_generated_dependencies(ty, stack);
                    }
                }
                TypeId::Tuple | TypeId::Builtin(_) => {
                    for ty in &tref.generics.types {
                        self.push_generated_dependencies(ty, stack);
                    }
                }
            },
            TyKind::Array(ty, _) | TyKind::Slice(ty) | TyKind::RawPtr(ty, _) => {
                self.push_generated_dependencies(ty, stack);
            }
            TyKind::Ref(_, ty, _) => self.push_generated_dependencies(ty, stack),
            _ => {}
        }
    }

    fn is_attribute_kind(&self, id: TypeDeclId) -> bool {
        self.name(id) == ATTRIBUTE_KIND
    }

    fn variants<'b>(&self, decl: &'b TypeDecl) -> Vec<&'b Variant> {
        let TypeDeclKind::Enum(variants) = &decl.kind else {
            return vec![];
        };
        if !self.is_attribute_kind(decl.def_id) {
            return variants.iter().collect();
        }

        let supported = ATTRIBUTE_KIND_VARIANTS
            .iter()
            .copied()
            .collect::<HashSet<_>>();
        variants
            .iter()
            .filter(|variant| supported.contains(variant.name.as_str()))
            .collect()
    }

    fn fields<'b>(&self, decl: &'b TypeDecl) -> Vec<&'b Field> {
        match &decl.kind {
            TypeDeclKind::Struct(fields) | TypeDeclKind::Union(fields) => fields.iter().collect(),
            TypeDeclKind::Enum(_) => self
                .variants(decl)
                .into_iter()
                .flat_map(|variant| variant.fields.iter())
                .collect(),
            TypeDeclKind::Alias(_) | TypeDeclKind::Opaque | TypeDeclKind::Error(_) => vec![],
        }
    }

    fn generate_attributes_file(&self) -> String {
        let mut out = String::new();
        out.push_str(
            "// This file is automatically generated by `cargo run --bin generate-asts`.\n",
        );
        out.push_str("// Do not edit it by hand.\n\n");
        out.push_str(
            "#![allow(clippy::doc_lazy_continuation, clippy::enum_variant_names, clippy::large_enum_variant)]\n\n",
        );
        out.push_str("use crate::ast::meta::Span;\n");
        out.push_str("use derive_generic_visitor::{Drive, DriveMut};\n");
        out.push_str("use serde::{Deserialize, Serialize};\n\n");
        out.push_str("use ustr::Ustr;\n\n");

        for &id in &self.generated {
            let decl = &self.crate_data[id];
            out.push_str(&self.generate_decl(decl));
            out.push('\n');
        }
        out
    }

    fn generate_decl(&self, decl: &TypeDecl) -> String {
        match &decl.kind {
            TypeDeclKind::Struct(fields) => self.generate_struct(decl.def_id, fields),
            TypeDeclKind::Union(fields) => self.generate_struct(decl.def_id, fields),
            TypeDeclKind::Enum(_) => self.generate_enum(decl),
            TypeDeclKind::Alias(ty) => {
                let docs = self.doc_attrs(&decl.item_meta.attr_info, 0);
                let alias = format!(
                    "pub type {} = {};",
                    self.local_name(decl.def_id),
                    self.charon_ty(ty),
                );
                if docs.is_empty() {
                    alias
                } else {
                    format!("{docs}\n{alias}")
                }
            }
            TypeDeclKind::Opaque | TypeDeclKind::Error(_) => unreachable!(),
        }
    }

    fn generate_struct(&self, id: TypeDeclId, fields: &IndexVec<FieldId, Field>) -> String {
        let name = self.local_name(id);
        let attrs = self.type_attrs(&self.crate_data[id], false);
        match fields.iter().collect_vec().as_slice() {
            [] => format!("{attrs}\npub struct {name};\n"),
            fields if fields.iter().all(|field| field.name.is_some()) => {
                let fields = fields
                    .iter()
                    .map(|field| self.generate_named_field(field, 4, "pub "))
                    .join("\n");
                format!("{attrs}\npub struct {name} {{\n{fields}\n}}\n")
            }
            fields => {
                if fields
                    .iter()
                    .any(|field| !self.field_attrs(field, 4).is_empty())
                {
                    let fields = fields
                        .iter()
                        .map(|field| self.generate_tuple_field(field, 4, "pub "))
                        .join("\n");
                    format!("{attrs}\npub struct {name}(\n{fields}\n);\n")
                } else {
                    let fields = fields
                        .iter()
                        .map(|field| format!("pub {}", self.charon_ty(&field.ty)))
                        .join(", ");
                    format!("{attrs}\npub struct {name}({fields});\n")
                }
            }
        }
    }

    fn generate_enum(&self, decl: &TypeDecl) -> String {
        let name = self.local_name(decl.def_id);
        let variants = self
            .variants(decl)
            .into_iter()
            .map(|variant| self.generate_variant(variant))
            .join("\n");
        format!(
            "{}\npub enum {name} {{\n{variants}\n}}\n",
            self.type_attrs(decl, true)
        )
    }

    fn generate_variant(&self, variant: &Variant) -> String {
        let name = rust_ident(&variant.name);
        let fields = variant.fields.iter().collect_vec();
        let docs = self.doc_attrs(&variant.attr_info, 4);
        let prefix = if docs.is_empty() {
            String::new()
        } else {
            format!("{docs}\n")
        };
        match fields.as_slice() {
            [] => format!("{prefix}    {name},"),
            fields if fields.iter().all(|field| field.name.is_some()) => {
                let fields = fields
                    .iter()
                    .map(|field| self.generate_named_field(field, 8, ""))
                    .join("\n");
                format!("{prefix}    {name} {{\n{fields}\n    }},")
            }
            fields => {
                if fields
                    .iter()
                    .any(|field| !self.field_attrs(field, 8).is_empty())
                {
                    let fields = fields
                        .iter()
                        .map(|field| self.generate_tuple_field(field, 8, ""))
                        .join("\n");
                    format!("{prefix}    {name}(\n{fields}\n    ),")
                } else {
                    let fields = fields
                        .iter()
                        .map(|field| self.charon_ty(&field.ty))
                        .join(", ");
                    format!("{prefix}    {name}({fields}),")
                }
            }
        }
    }

    fn generate_named_field(&self, field: &Field, indent: usize, visibility: &str) -> String {
        let pad = " ".repeat(indent);
        let attrs = self.field_attrs(field, indent);
        let field = format!(
            "{pad}{visibility}{}: {},",
            rust_ident(field.name.as_ref().unwrap()),
            self.charon_ty(&field.ty),
        );
        if attrs.is_empty() {
            field
        } else {
            format!("{attrs}\n{field}")
        }
    }

    fn generate_tuple_field(&self, field: &Field, indent: usize, visibility: &str) -> String {
        let pad = " ".repeat(indent);
        let attrs = self.field_attrs(field, indent);
        let field = format!("{pad}{visibility}{},", self.charon_ty(&field.ty));
        if attrs.is_empty() {
            field
        } else {
            format!("{attrs}\n{field}")
        }
    }

    fn field_attrs(&self, field: &Field, indent: usize) -> String {
        self.doc_attrs(&field.attr_info, indent)
    }

    fn generate_translate_attrs_file(&self) -> String {
        let mut out = String::new();
        out.push_str(
            "// This file is automatically generated by `cargo run --bin generate-asts`.\n",
        );
        out.push_str("// Do not edit it by hand.\n\n");
        out.push_str(
            "#![allow(clippy::deref_addrof, clippy::large_enum_variant, clippy::needless_borrow, unreachable_patterns)]\n\n",
        );
        out.push_str("use super::translate_ctx::TranslateCtx;\n");
        out.push_str("use charon_lib::ast::attributes as attrs;\n");
        out.push_str("use itertools::Itertools;\n\n");
        out.push_str("use ustr::Ustr;\n\n");
        out.push_str("impl<'tcx> TranslateCtx<'tcx> {\n");
        out.push_str(&self.generate_helper_functions());
        for &id in &self.generated {
            let decl = &self.crate_data[id];
            out.push_str(&self.generate_translate_decl(decl));
        }
        out.push_str("}\n");
        out
    }

    fn generate_helper_functions(&self) -> String {
        indoc::indoc! {r#"
                pub(crate) fn translate_attribute_kind(
                    &mut self,
                    value: &rustc_hir::attrs::AttributeKind,
                ) -> Option<attrs::BuiltinAttr> {
                    self.translate_builtin_attr_inner(value)
                }

                #[expect(dead_code)]
                fn translate_rustc_path_attr(&mut self, value: &rustc_ast::ast::Path) -> Ustr {
                    value
                        .segments
                        .iter()
                        .map(|segment| segment.ident.name.to_string())
                        .join("::")
                        .into()
                }

                fn translate_attr_span(&mut self, value: &rustc_span::Span) -> charon_lib::ast::Span {
                    self.translate_span(value)
                }

        "#}
        .to_string()
    }

    fn generate_translate_decl(&self, decl: &TypeDecl) -> String {
        match &decl.kind {
            TypeDeclKind::Struct(fields) => self.generate_translate_struct(decl, fields),
            TypeDeclKind::Union(fields) => self.generate_translate_struct(decl, fields),
            TypeDeclKind::Enum(_) => self.generate_translate_enum(decl),
            TypeDeclKind::Alias(ty) => {
                let fn_name = self.translate_fn_name(decl.def_id);
                let rust_ty = self.rust_ty_for_decl(decl.def_id);
                let charon_ty = self.local_name(decl.def_id);
                let expr = self.convert_expr(ty, "value");
                format!(
                    "    fn {fn_name}(&mut self, value: &{rust_ty}) -> attrs::{charon_ty} {{\n        {expr}\n    }}\n\n"
                )
            }
            TypeDeclKind::Opaque | TypeDeclKind::Error(_) => unreachable!(),
        }
    }

    fn generate_translate_struct(
        &self,
        decl: &TypeDecl,
        fields: &IndexVec<FieldId, Field>,
    ) -> String {
        let fn_name = self.translate_fn_name(decl.def_id);
        let rust_ty = self.rust_ty_for_decl(decl.def_id);
        let charon_ty = self.local_name(decl.def_id);
        let fields = fields.iter().collect_vec();
        let body = match fields.as_slice() {
            [] => format!("attrs::{charon_ty}"),
            fields if fields.iter().all(|field| field.name.is_some()) => {
                let fields = fields
                    .iter()
                    .map(|field| {
                        let name = field.name.as_ref().unwrap();
                        let ident = rust_ident(name);
                        let expr = self.convert_expr(&field.ty, &format!("&value.{ident}"));
                        format!("            {ident}: {expr},")
                    })
                    .join("\n");
                format!("attrs::{charon_ty} {{\n{fields}\n        }}")
            }
            fields => {
                let fields = fields
                    .iter()
                    .enumerate()
                    .map(|(i, field)| self.convert_expr(&field.ty, &format!("&value.{i}")))
                    .join(", ");
                format!("attrs::{charon_ty}({fields})")
            }
        };
        format!(
            "    fn {fn_name}(&mut self, value: &{rust_ty}) -> attrs::{charon_ty} {{\n        {body}\n    }}\n\n"
        )
    }

    fn generate_translate_enum(&self, decl: &TypeDecl) -> String {
        let fn_name = self.translate_fn_name(decl.def_id);
        let rust_ty = self.rust_ty_for_decl(decl.def_id);
        let charon_ty = self.local_name(decl.def_id);
        let is_attribute_kind = self.is_attribute_kind(decl.def_id);
        let arms = self
            .variants(decl)
            .into_iter()
            .map(|variant| self.generate_translate_variant(decl.def_id, variant, is_attribute_kind))
            .join("\n");
        if is_attribute_kind {
            format!(
                "    fn {fn_name}(&mut self, value: &{rust_ty}) -> Option<attrs::{charon_ty}> {{\n        match value {{\n{arms}\n            _ => None,\n        }}\n    }}\n\n"
            )
        } else {
            format!(
                "    fn {fn_name}(&mut self, value: &{rust_ty}) -> attrs::{charon_ty} {{\n        match value {{\n{arms}\n        }}\n    }}\n\n"
            )
        }
    }

    fn generate_translate_variant(
        &self,
        type_id: TypeDeclId,
        variant: &Variant,
        wrap_in_some: bool,
    ) -> String {
        let rust_ty = self.rust_ty_for_decl(type_id);
        let charon_ty = self.local_name(type_id);
        let variant_name = rust_ident(&variant.name);
        let fields = variant.fields.iter().collect_vec();
        let wrap_expr = |expr: String| {
            if wrap_in_some {
                format!("Some({expr})")
            } else {
                expr
            }
        };
        match fields.as_slice() {
            [] => {
                let expr = wrap_expr(format!("attrs::{charon_ty}::{variant_name}"));
                format!("            {rust_ty}::{variant_name} => {expr},")
            }
            fields if fields.iter().all(|field| field.name.is_some()) => {
                let pattern = fields
                    .iter()
                    .map(|field| rust_ident(field.name.as_ref().unwrap()))
                    .join(", ");
                let converted_fields = fields
                    .iter()
                    .map(|field| {
                        let name = rust_ident(field.name.as_ref().unwrap());
                        let expr = self.convert_expr(&field.ty, &name);
                        format!("                    {name}: {expr},")
                    })
                    .join("\n");
                let expr = wrap_expr(format!(
                    "attrs::{charon_ty}::{variant_name} {{\n{converted_fields}\n                }}"
                ));
                format!("            {rust_ty}::{variant_name} {{ {pattern} }} => {expr},")
            }
            fields => {
                let pattern = (0..fields.len()).map(|i| format!("field_{i}")).join(", ");
                let converted_fields = fields
                    .iter()
                    .enumerate()
                    .map(|(i, field)| self.convert_expr(&field.ty, &format!("field_{i}")))
                    .join(", ");
                let expr = wrap_expr(format!(
                    "attrs::{charon_ty}::{variant_name}({converted_fields})"
                ));
                format!("            {rust_ty}::{variant_name}({pattern}) => {expr},")
            }
        }
    }

    fn charon_ty(&self, ty: &Ty) -> String {
        match ty.kind() {
            TyKind::Literal(lit) => lit.name().to_string(),
            TyKind::Adt(tref) => match tref.id {
                TypeId::Adt(id) => {
                    self.charon_adt_ty(id, &tref.generics.types.iter().collect_vec())
                }
                TypeId::Tuple => tuple_ty(
                    tref.generics
                        .types
                        .iter()
                        .map(|ty| self.charon_ty(ty))
                        .collect_vec(),
                ),
                TypeId::Builtin(BuiltinTy::Box) => {
                    format!("Box<{}>", self.charon_ty(&tref.generics.types[0]))
                }
                TypeId::Builtin(BuiltinTy::Str) => "Ustr".to_string(),
            },
            TyKind::Array(ty, _) | TyKind::Slice(ty) => format!("Vec<{}>", self.charon_ty(ty)),
            TyKind::RawPtr(_, _) => "Ustr".to_string(),
            TyKind::Ref(_, ty, _) => self.charon_ty(ty),
            TyKind::Never => "()".to_string(),
            TyKind::TypeVar(_) => "Ustr".to_string(),
            _ => "Ustr".to_string(),
        }
    }

    fn charon_adt_ty(&self, id: TypeDeclId, generics: &[&Ty]) -> String {
        match self.special_adt(id) {
            Some(SpecialAdt::Span) => "Span".to_string(),
            Some(SpecialAdt::Symbol | SpecialAdt::Path | SpecialAdt::PathBuf) => "Ustr".to_string(),
            Some(SpecialAdt::ThinVec | SpecialAdt::Vec) => {
                format!("Vec<{}>", self.charon_ty(generics[0]))
            }
            Some(SpecialAdt::Option) => format!("Option<{}>", self.charon_ty(generics[0])),
            Some(SpecialAdt::Result) => {
                format!(
                    "Result<{}, {}>",
                    self.charon_ty(generics[0]),
                    self.charon_ty(generics[1])
                )
            }
            Some(SpecialAdt::IndexMap) => {
                format!(
                    "Vec<({}, {})>",
                    self.charon_ty(generics[0]),
                    self.charon_ty(generics[1])
                )
            }
            Some(SpecialAdt::Box) => format!("Box<{}>", self.charon_ty(generics[0])),
            Some(SpecialAdt::NonZero) => self.charon_ty(generics[0]),
            Some(
                SpecialAdt::Align
                | SpecialAdt::DefId
                | SpecialAdt::OpaqueString
                | SpecialAdt::DebugString,
            ) => self.special_output_ty(id),
            None if self.generated.contains(&id) => self.local_name(id),
            None => "Ustr".to_string(),
        }
    }

    fn convert_expr(&self, ty: &Ty, value: &str) -> String {
        match ty.kind() {
            TyKind::Literal(_) => format!("*({value})"),
            TyKind::Adt(tref) => match tref.id {
                TypeId::Adt(id) => {
                    self.convert_adt_expr(id, &tref.generics.types.iter().collect_vec(), value)
                }
                TypeId::Tuple => {
                    self.convert_tuple_expr(&tref.generics.types.iter().collect_vec(), value)
                }
                TypeId::Builtin(BuiltinTy::Box) => {
                    let inner =
                        self.convert_expr(&tref.generics.types[0], &format!("({value}).as_ref()"));
                    format!("Box::new({inner})")
                }
                TypeId::Builtin(BuiltinTy::Str) => format!("({value}).to_string().into()"),
            },
            TyKind::Array(ty, _) | TyKind::Slice(ty) => {
                let inner = self.convert_expr(ty, "value");
                format!("({value}).iter().map(|value| {inner}).collect()")
            }
            TyKind::Ref(_, ty, _) => self.convert_expr(ty, value),
            TyKind::RawPtr(_, _) => format!("format!(\"{{:?}}\", {value}).into()"),
            TyKind::Never => "()".to_string(),
            TyKind::TypeVar(_) => format!("format!(\"{{:?}}\", {value}).into()"),
            _ => format!("format!(\"{{:?}}\", {value}).into()"),
        }
    }

    fn convert_adt_expr(&self, id: TypeDeclId, generics: &[&Ty], value: &str) -> String {
        match self.special_adt(id) {
            Some(SpecialAdt::Span) => format!("self.translate_attr_span({value})"),
            Some(SpecialAdt::Symbol | SpecialAdt::OpaqueString) => {
                format!("({value}).to_string().into()")
            }
            Some(SpecialAdt::Path) => format!("self.translate_rustc_path_attr({value})"),
            Some(SpecialAdt::PathBuf) => format!("({value}).display().to_string().into()"),
            Some(SpecialAdt::Align) => format!("({value}).bytes()"),
            Some(SpecialAdt::DefId) => format!("self.tcx.def_path_str(*({value})).into()"),
            Some(SpecialAdt::DebugString) => format!("format!(\"{{:?}}\", {value}).into()"),
            Some(SpecialAdt::ThinVec | SpecialAdt::Vec) => {
                let inner = self.convert_expr(generics[0], "value");
                format!("({value}).iter().map(|value| {inner}).collect()")
            }
            Some(SpecialAdt::Option) => {
                let inner = self.convert_expr(generics[0], "value");
                format!("({value}).as_ref().map(|value| {inner})")
            }
            Some(SpecialAdt::Result) => {
                let ok = self.convert_expr(generics[0], "value");
                let err = self.convert_expr(generics[1], "value");
                format!("({value}).as_ref().map(|value| {ok}).map_err(|value| {err})")
            }
            Some(SpecialAdt::IndexMap) => {
                let key = self.convert_expr(generics[0], "key");
                let val = self.convert_expr(generics[1], "value");
                format!("({value}).iter().map(|(key, value)| ({key}, {val})).collect()")
            }
            Some(SpecialAdt::Box) => {
                let inner = self.convert_expr(generics[0], &format!("({value}).as_ref()"));
                format!("Box::new({inner})")
            }
            Some(SpecialAdt::NonZero) => format!("({value}).get()"),
            None if self.generated.contains(&id) => {
                format!("self.{}({value})", self.translate_fn_name(id))
            }
            None => format!("format!(\"{{:?}}\", {value})"),
        }
    }

    fn convert_tuple_expr(&self, fields: &[&Ty], value: &str) -> String {
        match fields {
            [] => "()".to_string(),
            [field] => {
                let field = self.convert_expr(field, &format!("&(({value}).0)"));
                format!("({field},)")
            }
            fields => {
                let fields = fields
                    .iter()
                    .enumerate()
                    .map(|(i, field)| self.convert_expr(field, &format!("&(({value}).{i})")))
                    .join(", ");
                format!("({fields})")
            }
        }
    }

    fn rust_ty_for_decl(&self, id: TypeDeclId) -> String {
        let name = self.name(id);
        if let Some(name) = name.strip_prefix("rustc_hir::attrs::data_structures::") {
            format!("rustc_hir::attrs::{name}")
        } else if let Some(name) = name.strip_prefix("rustc_hir::stability::") {
            format!("rustc_hir::{name}")
        } else {
            name.to_string()
        }
    }

    fn special_output_ty(&self, id: TypeDeclId) -> String {
        match self.special_adt(id).unwrap() {
            SpecialAdt::Align => "u64".to_string(),
            SpecialAdt::DefId => "Ustr".to_string(),
            SpecialAdt::OpaqueString | SpecialAdt::DebugString => "Ustr".to_string(),
            _ => unreachable!(),
        }
    }

    fn special_adt(&self, id: TypeDeclId) -> Option<SpecialAdt> {
        let name = self.name(id);
        Some(match name {
            "alloc::boxed::Box" => SpecialAdt::Box,
            "alloc::string::String" => SpecialAdt::OpaqueString,
            "alloc::vec::Vec" => SpecialAdt::Vec,
            "core::num::nonzero::NonZero" => SpecialAdt::NonZero,
            "core::option::Option" => SpecialAdt::Option,
            "core::result::Result" => SpecialAdt::Result,
            "indexmap::map::IndexMap" => SpecialAdt::IndexMap,
            "rustc_abi::Align" => SpecialAdt::Align,
            "rustc_ast::ast::Path" => SpecialAdt::Path,
            "rustc_span::def_id::DefId" => SpecialAdt::DefId,
            "rustc_span::span_encoding::Span" => SpecialAdt::Span,
            "rustc_span::symbol::Symbol" => SpecialAdt::Symbol,
            "std::path::PathBuf" => SpecialAdt::PathBuf,
            "thin_vec::ThinVec" => SpecialAdt::ThinVec,
            "rustc_target::spec::SanitizerSet"
            | "rustc_span::def_id::DefIndex"
            | "rustc_span::def_id::CrateNum"
            | "rustc_span::ErrorGuaranteed"
            | "rustc_ast::node_id::NodeId"
            | "rustc_ast::tokenstream::LazyAttrTokenStream"
            | "core::num::niche_types::NonZeroU32Inner"
            | "alloc::alloc::Global"
            | "rustc_hash::FxBuildHasher" => SpecialAdt::DebugString,
            _ => return None,
        })
    }

    fn doc_attrs(&self, attr_info: &AttrInfo, indent: usize) -> String {
        let pad = " ".repeat(indent);
        attr_info
            .attributes
            .iter()
            .filter_map(|attr| attr.as_doc_comment())
            .flat_map(|doc| {
                if doc.is_empty() {
                    vec![format!("{pad}///")]
                } else {
                    doc.lines()
                        .map(|line| format!("{pad}///{line}"))
                        .collect_vec()
                }
            })
            .join("\n")
    }

    fn type_attrs(&self, decl: &TypeDecl, is_enum: bool) -> String {
        let name = self.local_name(decl.def_id);
        let rename = if name == "BuiltinAttr" {
            "BuiltinAttr".to_string()
        } else {
            format!("BuiltinAttr{name}")
        };
        let mut attrs = self
            .doc_attrs(&decl.item_meta.attr_info, 0)
            .lines()
            .map(|line| line.to_string())
            .collect_vec();
        attrs.extend([
            "#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize, Drive, DriveMut)]"
                .to_string(),
            format!("#[cfg_attr(feature = \"charon_on_charon\", charon::rename(\"{rename}\"))]"),
        ]);
        if is_enum {
            attrs.push(format!(
                "#[cfg_attr(feature = \"charon_on_charon\", charon::variants_prefix(\"{rename}\"))]"
            ));
        }
        attrs.join("\n")
    }

    fn local_name(&self, id: TypeDeclId) -> String {
        self.local_names
            .get(&id)
            .cloned()
            .unwrap_or_else(|| self.short_name(id))
    }

    fn short_name(&self, id: TypeDeclId) -> String {
        self.name(id).rsplit("::").next().unwrap().to_string()
    }

    fn translate_fn_name(&self, id: TypeDeclId) -> String {
        format!(
            "translate_{}_inner",
            self.local_name(id).to_case(Case::Snake)
        )
    }

    fn name(&self, id: TypeDeclId) -> &str {
        &self.names[&id]
    }
}

#[derive(Clone, Copy)]
enum SpecialAdt {
    Span,
    Symbol,
    ThinVec,
    Vec,
    Option,
    Result,
    IndexMap,
    Box,
    NonZero,
    Align,
    DefId,
    Path,
    PathBuf,
    OpaqueString,
    DebugString,
}

fn repr_name(name: &Name) -> String {
    name.name
        .iter()
        .map(|elem| match elem {
            PathElem::Ident(name, _) => name.clone(),
            PathElem::Impl(_) => "<impl>".to_string(),
            PathElem::Instantiated(_) => "<mono>".to_string(),
            PathElem::Target(target) => target.clone(),
        })
        .join("::")
}

fn tuple_ty(fields: Vec<String>) -> String {
    match fields.as_slice() {
        [] => "()".to_string(),
        [field] => format!("({field},)"),
        _ => format!("({})", fields.iter().join(", ")),
    }
}

fn rust_ident(name: &str) -> String {
    let keywords: HashSet<&'static str> = [
        "as", "async", "await", "break", "const", "continue", "crate", "dyn", "else", "enum",
        "extern", "false", "fn", "for", "if", "impl", "in", "let", "loop", "match", "mod", "move",
        "mut", "pub", "ref", "return", "self", "Self", "static", "struct", "super", "trait",
        "true", "type", "unsafe", "use", "where", "while",
    ]
    .into_iter()
    .collect();
    if keywords.contains(name) {
        format!("r#{name}")
    } else {
        name.to_string()
    }
}
