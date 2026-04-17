use crate::GenerateCtx;
use charon_lib::ast::*;
use itertools::Itertools;
use std::collections::HashMap;
use std::collections::HashSet;
use std::fmt::Write;

const MANUAL_IMPLS: &[(&str, &str)] = &[
    // Hand-written because we replace the `FileId` with the corresponding file.
    ("FileId", "file"),
    (
        "HashConsed",
        "'a0 (* Not actually hash-consed on the OCaml side *)",
    ),
];

#[derive(Clone, Copy)]
pub struct DeriveVisitors {
    pub name: &'static str,
    pub ancestors: &'static [&'static str],
    pub reduce: bool,
    pub extra_types: &'static [&'static str],
}

impl<'a> GenerateCtx<'a> {
    fn extract_doc_comments(&self, attr_info: &AttrInfo) -> String {
        attr_info
            .attributes
            .iter()
            .filter_map(|a| a.as_doc_comment())
            .join("\n")
    }

    /// Make a doc comment that contains the given string, indenting it if necessary.
    fn build_doc_comment(&self, comment: String, indent_level: usize) -> String {
        #[derive(Default)]
        struct Exchanger {
            is_in_open_escaped_block: bool,
            is_in_open_inline_escape: bool,
        }
        impl Exchanger {
            pub fn exchange_escape_delimiters(&mut self, line: &str) -> String {
                if line.contains("```") {
                    // Handle multi-line escaped blocks.
                    let (leading, mut rest) = line.split_once("```").unwrap();

                    // Strip all (hard-coded) possible ways to open the block.
                    rest = if rest.starts_with("text") {
                        rest.strip_prefix("text").unwrap()
                    } else if rest.starts_with("rust,ignore") {
                        rest.strip_prefix("rust,ignore").unwrap()
                    } else {
                        rest
                    };
                    let mut result = leading.to_owned();
                    if self.is_in_open_escaped_block {
                        result.push_str("]}");
                        self.is_in_open_escaped_block = false;
                    } else {
                        result.push_str("{@rust[");
                        self.is_in_open_escaped_block = true;
                    }
                    result.push_str(rest);
                    result
                } else if line.contains('`') {
                    // Handle inline escaped strings. These can occur in multiple lines, so we track them globally.
                    let mut parts = line.split('`');
                    // Skip after first part (we only need to add escapes after that).
                    let mut result = parts.next().unwrap().to_owned();
                    for part in parts {
                        if self.is_in_open_inline_escape {
                            result.push(']');
                            result.push_str(part);
                            self.is_in_open_inline_escape = false;
                        } else {
                            result.push('[');
                            result.push_str(part);
                            self.is_in_open_inline_escape = true;
                        }
                    }
                    result
                } else {
                    line.to_owned()
                }
            }
        }

        if comment.is_empty() {
            return comment;
        }
        let is_multiline = comment.contains("\n");
        if !is_multiline {
            let fixed_comment = Exchanger::default().exchange_escape_delimiters(&comment);
            format!("(**{fixed_comment} *)")
        } else {
            let indent = "  ".repeat(indent_level);
            let mut exchanger = Exchanger::default();
            let comment = comment
                .lines()
                .enumerate()
                .map(|(i, line)| {
                    // Remove one leading space if there is one (there usually is because we write `///
                    // comment` and not `///comment`).
                    let line = line.strip_prefix(" ").unwrap_or(line);
                    let fixed_line = exchanger.exchange_escape_delimiters(line);

                    // The first line follows the `(**` marker, it does not need to be indented.
                    // Neither do empty lines.
                    if i == 0 || fixed_line.is_empty() {
                        fixed_line
                    } else {
                        format!("{indent}    {fixed_line}")
                    }
                })
                .join("\n");
            format!("(** {comment}\n{indent} *)")
        }
    }

    fn build_type(&self, decl: &TypeDecl, co_rec: bool, body: &str) -> String {
        let (ty_name, _) = self.type_to_ocaml_ident_raw(decl);
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
        let comment = self.extract_doc_comments(&decl.item_meta.attr_info);
        let comment = self.build_doc_comment(comment, 0);
        let keyword = if co_rec { "and" } else { "type" };
        format!("\n{comment} {keyword} {generics} {ty_name} = {body}")
    }

    /// Generate an ocaml type declaration that mirrors `decl`.
    ///
    /// `co_rec` indicates whether this definition is co-recursive with the ones that come before (i.e.
    /// should be declared with `and` instead of `type`).
    fn type_decl_to_ocaml_decl(
        &self,
        opaque_for_visitor: &HashSet<TypeDeclId>,
        manual_impls: &HashMap<TypeDeclId, String>,
        decl: &TypeDecl,
        co_rec: bool,
    ) -> String {
        let opaque = if opaque_for_visitor.contains(&decl.def_id) {
            "[@visitors.opaque]"
        } else {
            ""
        };
        let body = match &decl.kind {
            _ if let Some(def) = manual_impls.get(&decl.def_id) => def.clone(),
            TypeDeclKind::Alias(ty) => {
                let ty = self.type_to_ocaml_name(ty);
                format!("{ty} {opaque}")
            }
            TypeDeclKind::Struct(fields) if fields.is_empty() => "unit".to_string(),
            TypeDeclKind::Struct(fields)
                if fields.len() == 1
                    && fields[0].name.as_ref().is_some_and(|name| name == "_raw") =>
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
                format!("{short_name}.id [@visitors.opaque]")
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
                let ty = self.type_to_ocaml_name(&fields[0].ty);
                format!("{ty} {opaque}")
            }
            TypeDeclKind::Struct(fields) if fields.iter().all(|f| f.name.is_none()) => fields
                .iter()
                .filter(|f| !f.is_opaque())
                .map(|f| {
                    let ty = self.type_to_ocaml_name(&f.ty);
                    format!("{ty} {opaque}")
                })
                .join("*"),
            TypeDeclKind::Struct(fields) => {
                let fields = fields
                    .iter()
                    .filter(|f| !f.is_opaque())
                    .map(|f| {
                        let name = f.renamed_name().unwrap();
                        let ty = self.type_to_ocaml_name(&f.ty);
                        let comment = self.extract_doc_comments(&f.attr_info);
                        let comment = self.build_doc_comment(comment, 2);
                        format!("{name} : {ty} {opaque} {comment}")
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
                                        let comment = self.extract_doc_comments(&f.attr_info);
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
                                .map(|f| {
                                    let ty = self.type_to_ocaml_name(&f.ty);
                                    format!("{ty} {opaque}")
                                })
                                .join("*");
                            format!(" of {fields}")
                        };
                        let comment = self.extract_doc_comments(&attr_info);
                        let comment = self.build_doc_comment(comment, 3);
                        format!("\n\n | {rename}{ty} {comment}")
                    })
                    .join("")
            }
            TypeDeclKind::Union(..) => todo!(),
            TypeDeclKind::Opaque => todo!(),
            TypeDeclKind::Error(_) => todo!(),
        };
        self.build_type(decl, co_rec, &body)
    }

    fn generate_visitor_bases(
        &self,
        name: &str,
        inherits: &[&str],
        reduce: bool,
        ty_names: &[String],
    ) -> String {
        let mut out = String::new();
        let make_inherit = |variety| {
            if !inherits.is_empty() {
                inherits
                    .iter()
                    .map(|ancestor| {
                        if let [module, name] = ancestor.split(".").collect_vec().as_slice() {
                            format!("inherit [_] {module}.{variety}_{name}")
                        } else {
                            format!("inherit [_] {variety}_{ancestor}")
                        }
                    })
                    .join("\n")
            } else {
                format!("inherit [_] VisitorsRuntime.{variety}")
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
                {}
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
                {}
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
                    {}
                    {reduce_methods}
                end
                ",
                make_inherit("reduce")
            );

            let mapreduce_methods = ty_names
                .iter()
                .map(|ty| {
                    format!(
                        "method visit_{ty} : 'env -> {ty} -> {ty} * 'a = fun _ x -> (x, self#zero)"
                    )
                })
                .format("\n");
            let _ = write!(
                &mut out,
                "
                class virtual ['self] mapreduce_{name} =
                object (self : 'self)
                    {}
                    {mapreduce_methods}
                end
                ",
                make_inherit("mapreduce")
            );
        }

        out
    }

    fn add_visitors_to_decls(&self, visitors: &DeriveVisitors, mut decls: String) -> String {
        let &DeriveVisitors {
            name,
            mut ancestors,
            reduce,
            extra_types,
        } = visitors;
        let varieties: &[_] = if reduce {
            &["iter", "map", "reduce", "mapreduce"]
        } else {
            &["iter", "map"]
        };
        let intermediate_visitor_name;
        let intermediate_visitor_name_slice;
        if !extra_types.is_empty() {
            intermediate_visitor_name = format!("{name}_base");
            let intermediate_visitor = self.generate_visitor_bases(
                &intermediate_visitor_name,
                ancestors,
                reduce,
                extra_types
                    .iter()
                    .map(|s| s.to_string())
                    .collect_vec()
                    .as_slice(),
            );
            intermediate_visitor_name_slice = [intermediate_visitor_name.as_str()];
            ancestors = &intermediate_visitor_name_slice;
            decls =
                format!("(* Ancestors for the {name} visitors *){intermediate_visitor}\n{decls}");
        }
        let visitors = varieties
            .iter()
            .map(|variety| {
                let nude = if !ancestors.is_empty() {
                    "nude = true (* Don't inherit VisitorsRuntime *);".to_string()
                } else {
                    String::new()
                };
                let ancestors = format!(
                    "ancestors = [ {} ];",
                    ancestors
                        .iter()
                        .map(|a| format!("\"{variety}_{a}\""))
                        .join(";")
                );
                format!(
                    r#"
                    visitors {{
                        name = "{variety}_{name}";
                        monomorphic = ["env"];
                        variety = "{variety}";
                        {ancestors}
                        {nude}
                    }}
                "#
                )
            })
            .format(", ");
        write!(&mut decls, "\n[@@deriving show, eq, ord, {visitors}]").unwrap();
        decls
    }

    pub fn type_decls_to_ocaml(
        &self,
        visitors: &Option<DeriveVisitors>,
        tys: Vec<&TypeDecl>,
    ) -> String {
        // Types that we don't want visitors to go into.
        let opaque_for_visitors = self.names_to_type_id_set(&["Name"]);
        let manual_impls = self.names_to_type_id_map(MANUAL_IMPLS);
        let decls = tys
            .into_iter()
            .enumerate()
            .map(|(i, ty)| {
                let co_recursive = i != 0;
                self.type_decl_to_ocaml_decl(&opaque_for_visitors, &manual_impls, ty, co_recursive)
            })
            .join("\n");
        match visitors {
            Some(visitors) => self.add_visitors_to_decls(visitors, decls),
            None => decls,
        }
    }
}
