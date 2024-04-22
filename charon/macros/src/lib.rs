//! This module contains some macros for Charon. Due to technical reasons, Rust
//! forces users to define such macros in a separate, dedicated library. Note
//! that this doesn't apply to `macro_rules`.

extern crate proc_macro;
extern crate syn;
use proc_macro::{Span, TokenStream};
use quote::ToTokens;
use std::vec::Vec;
use syn::punctuated::Punctuated;
use syn::token::{Add, Comma};
use syn::{
    parse, parse_macro_input, Binding, Block, Constraint, Data, DataEnum, DeriveInput, Expr,
    Fields, FnArg, GenericArgument, GenericParam, Ident, Item, ItemTrait, Lifetime, Lit, Pat, Path,
    PathArguments, PathSegment, ReturnType, Stmt, TraitBound, TraitBoundModifier, TraitItem, Type,
    TypeParamBound, TypePath, WhereClause, WherePredicate,
};

const _TAB: &'static str = "    ";
const _TWO_TABS: &'static str = "        ";
const THREE_TABS: &'static str = "            ";

macro_rules! derive_variant_name_impl_code {
    () => {
        "impl{} {}{}{} {{
    pub fn variant_name(&self) -> &'static str {{
        match self {{
{}
        }}
    }}
}}"
    };
}

macro_rules! derive_variant_index_arity_impl_code {
    () => {
        "impl{} {}{}{} {{
    pub fn variant_index_arity(&self) -> (u32, usize) {{
        match self {{
{}
        }}
    }}
}}"
    };
}

macro_rules! derive_impl_block_code {
    () => {
        "impl{} {}{}{} {{
{}
}}"
    };
}

macro_rules! derive_enum_variant_impl_code {
    () => {
        "    pub fn {}{}({}self) -> {} {{
        match self {{
{}
        }}
    }}"
    };
}

fn lifetime_to_string(lf: &Lifetime) -> String {
    format!("'{}", lf.ident.to_string()).to_string()
}

/// We initially used the convert-case crate, but it converts names like "I32"
/// to "i_32", while we want to get "i32". We thus reimplemented our own converter
/// (which removes one dependency at the same time).
fn to_snake_case(s: &str) -> String {
    let mut snake_case = String::new();

    // We need to keep track of whether the last treated character was
    // lowercase (or not) to prevent this kind of transformations:
    // "VARIANT" -> "v_a_r_i_a_n_t"
    // Note that if we remember whether the last character was uppercase instead,
    // we get things like this:
    // "I32" -> "I3_2"
    let mut last_is_lowercase = false;

    for (_, c) in s.chars().enumerate() {
        if c.is_uppercase() {
            if last_is_lowercase {
                snake_case.push('_');
            }
            last_is_lowercase = false;
            snake_case.push(c.to_lowercase().next().unwrap());
        } else {
            last_is_lowercase = true;
            snake_case.push(c);
        }
    }

    snake_case
}

/// TODO: this is also used to format field types, so we have to take all the
/// cases into account
fn type_to_string(ty: &Type) -> String {
    match ty {
        Type::Array(type_array) => format!(
            "[{}; {}]",
            type_to_string(&type_array.elem),
            expr_to_string(&type_array.len)
        )
        .to_string(),
        Type::BareFn(_) => {
            panic!("type_to_string: unexpected type: BareFn");
        }
        Type::Group(_) => {
            panic!("type_to_string: unexpected type: Group");
        }
        Type::ImplTrait(_) => {
            panic!("type_to_string: unexpected type: ImplTrait");
        }
        Type::Infer(_) => {
            panic!("type_to_string: unexpected type: Infer");
        }
        Type::Macro(_) => {
            panic!("type_to_string: unexpected type: Macro");
        }
        Type::Never(_) => {
            panic!("type_to_string: unexpected type: Never");
        }
        Type::Paren(_) => {
            panic!("type_to_string: unexpected type: Paren");
        }
        Type::Path(p) => type_path_to_string(p),
        Type::Ptr(_) => {
            panic!("type_to_string: unexpected type: Ptr");
        }
        Type::Reference(type_ref) => {
            let lifetime = match &type_ref.lifetime {
                None => "".to_string(),
                Some(lf) => lifetime_to_string(lf),
            };
            let mutability = if type_ref.mutability.is_some() {
                format!("&{} mut", lifetime)
            } else {
                format!("&{}", lifetime)
            };

            format!("{} {}", mutability, type_to_string(&type_ref.elem)).to_string()
        }
        Type::Slice(type_slice) => format!("[{}]", type_to_string(&type_slice.elem)).to_string(),
        Type::TraitObject(_) => {
            panic!("type_to_string: unexpected type: TraitObject");
        }
        Type::Tuple(type_tuple) => {
            let tys: Vec<String> = type_tuple
                .elems
                .iter()
                .map(|ty| type_to_string(ty))
                .collect();
            format!("({})", tys.join(", ")).to_string()
        }
        Type::Verbatim(_) => {
            panic!("type_to_string: unexpected type: Verbatim");
        }
        _ => {
            panic!("type_to_string: unexpected type");
        }
    }
}

fn binding_to_string(b: &Binding) -> String {
    format!("{} = {}", b.ident.to_string(), type_to_string(&b.ty)).to_string()
}

fn constraint_to_string(c: &Constraint) -> String {
    format!(
        "{} : {}",
        c.ident.to_string(),
        type_param_bounds_to_string(&c.bounds)
    )
    .to_string()
}

fn lit_to_string(l: &Lit) -> String {
    match l {
        Lit::Str(l) => l.value(),
        Lit::ByteStr(_) => unimplemented!(),
        Lit::Byte(l) => l.value().to_string(),
        Lit::Char(l) => l.value().to_string(),
        Lit::Int(l) => l.base10_digits().to_string(),
        Lit::Float(l) => l.base10_digits().to_string(),
        Lit::Bool(l) => l.value().to_string(),
        Lit::Verbatim(_) => unimplemented!(),
    }
}

/// Converts an expression to a string.
/// For now, only supports the cases useful for the type definitions (literals)
fn expr_to_string(e: &Expr) -> String {
    match e {
        Expr::Lit(lit) => lit_to_string(&lit.lit),
        _ => unimplemented!(),
    }
}

fn angle_bracketed_generic_arguments_to_string(
    args: &Punctuated<GenericArgument, Comma>,
) -> String {
    let args: Vec<String> = args.iter().map(|a| generic_argument_to_string(a)).collect();
    if args.is_empty() {
        "".to_string()
    } else {
        format!("<{}>", args.join(", ")).to_string()
    }
}

fn generic_argument_to_string(a: &GenericArgument) -> String {
    match a {
        GenericArgument::Lifetime(lf) => lifetime_to_string(lf),
        GenericArgument::Type(ty) => type_to_string(ty),
        GenericArgument::Binding(b) => binding_to_string(b),
        GenericArgument::Constraint(c) => constraint_to_string(c),
        GenericArgument::Const(e) => expr_to_string(e),
    }
}

fn path_segment_to_string(ps: &PathSegment) -> String {
    let seg = ps.ident.to_string();

    match &ps.arguments {
        PathArguments::None => seg,
        PathArguments::AngleBracketed(args) => format!(
            "{}{}",
            seg,
            angle_bracketed_generic_arguments_to_string(&args.args)
        )
        .to_string(),
        PathArguments::Parenthesized(_) => {
            // Don't know in which situation this may happen
            unimplemented!()
        }
    }
}

fn path_to_string(path: &Path) -> String {
    let path: Vec<String> = path
        .segments
        .iter()
        .map(|x| path_segment_to_string(x))
        .collect();
    path.join("::")
}

fn type_path_to_string(tp: &TypePath) -> String {
    // Don't know what to do with that
    assert!(tp.qself.is_none());

    path_to_string(&tp.path)
}

fn trait_bound_to_string(tb: &TraitBound) -> String {
    // Sanity check
    match tb.modifier {
        TraitBoundModifier::None => (),
        TraitBoundModifier::Maybe(_) => {
            unimplemented!()
        }
    }

    assert!(tb.lifetimes.is_none());

    path_to_string(&tb.path)
}

fn type_param_bounds_to_string(bounds: &Punctuated<TypeParamBound, Add>) -> String {
    let mut s: Vec<String> = vec![];

    for p in bounds {
        match p {
            TypeParamBound::Trait(tb) => {
                s.push(trait_bound_to_string(tb));
            }
            TypeParamBound::Lifetime(lf) => {
                s.push(lifetime_to_string(lf));
            }
        }
    }

    s.join(" + ")
}

fn lifetime_bounds_to_string(bounds: &Punctuated<Lifetime, Add>) -> String {
    let bounds: Vec<String> = bounds.iter().map(|lf| lifetime_to_string(lf)).collect();
    bounds.join(" + ")
}

/// Auxiliary helper
fn generic_param_with_opt_constraints_to_string(
    param: &GenericParam,
    with_constraints: bool,
) -> String {
    match param {
        GenericParam::Type(type_param) => {
            let ident = type_param.ident.to_string();

            if type_param.bounds.is_empty() || !with_constraints {
                ident
            } else {
                format!(
                    "{} : {}",
                    ident,
                    type_param_bounds_to_string(&type_param.bounds)
                )
                .to_string()
            }
        }
        GenericParam::Lifetime(lf_param) => {
            let ident = lifetime_to_string(&lf_param.lifetime);

            if lf_param.bounds.is_empty() || !with_constraints {
                ident
            } else {
                format!(
                    "{} : {}",
                    ident,
                    lifetime_bounds_to_string(&lf_param.bounds)
                )
                .to_string()
            }
        }
        GenericParam::Const(_) => {
            // Don't know what to do with const parameters
            unimplemented!()
        }
    }
}

/// Generate a string from generic parameters.
/// `with_constraints` constrols whether we should format the constraints or not.
/// For instance, should we generate: `<'a, T1 : 'a, T2 : Clone>` or ``<'a, T1, T2>`?
fn generic_params_with_opt_constraints_to_string(
    params: &Punctuated<GenericParam, Comma>,
    with_constraints: bool,
) -> String {
    let gens: Vec<String> = params
        .iter()
        .map(|g| generic_param_with_opt_constraints_to_string(g, with_constraints))
        .collect();
    if gens.is_empty() {
        "".to_string()
    } else {
        format!("<{}>", gens.join(", "))
    }
}

/// See [`generic_params_with_opt_constraints_to_string`](generic_params_with_opt_constraints_to_string)
fn generic_params_to_string(params: &Punctuated<GenericParam, Comma>) -> String {
    generic_params_with_opt_constraints_to_string(params, true)
}

/// See [`generic_params_with_opt_constraints_to_string`](generic_params_with_opt_constraints_to_string)
fn generic_params_without_constraints_to_string(
    params: &Punctuated<GenericParam, Comma>,
) -> String {
    generic_params_with_opt_constraints_to_string(params, false)
}

fn where_predicate_to_string(wp: &WherePredicate) -> String {
    match wp {
        WherePredicate::Type(pred_type) => {
            assert!(pred_type.lifetimes.is_none());

            let ty = type_to_string(&pred_type.bounded_ty);

            if pred_type.bounds.is_empty() {
                ty
            } else {
                format!(
                    "{} : {}",
                    ty,
                    type_param_bounds_to_string(&pred_type.bounds)
                )
                .to_string()
            }
        }
        WherePredicate::Lifetime(pred_lf) => format!(
            "{} : {}",
            lifetime_to_string(&pred_lf.lifetime),
            lifetime_bounds_to_string(&pred_lf.bounds)
        )
        .to_string(),
        WherePredicate::Eq(pred_eq) => format!(
            "{} = {}",
            type_to_string(&pred_eq.lhs_ty),
            type_to_string(&pred_eq.rhs_ty)
        )
        .to_string(),
    }
}

fn where_clause_to_string(wc: &WhereClause) -> String {
    let preds = wc.predicates.iter().map(|p| where_predicate_to_string(p));
    let preds: Vec<String> = preds.map(|p| format!("    {},\n", p).to_string()).collect();
    format!("\nwhere\n{}", preds.join("")).to_string()
}

fn opt_where_clause_to_string(wc: &Option<WhereClause>) -> String {
    match wc {
        None => "".to_string(),
        Some(wc) => where_clause_to_string(wc),
    }
}

struct MatchPattern {
    /// The variant id
    variant_id: Ident,
    /// The match pattern as a string.
    /// For instance: `List::Cons(hd, tl)`
    match_pattern: String,
    /// The number of arguments in the match pattern (including anonymous
    /// arguments).
    num_args: usize,
    /// The variables we introduced in the match pattern.
    /// `["hd", "tl"]` if the pattern is `List::Cons(hd, tl)`.
    /// Empty vector if the variables are anonymous (i.e.: `_`).
    named_args: Vec<String>,
    /// The types of the variables introduced in the match pattern
    arg_types: Vec<String>,
}

/// Generate matching patterns for an enumeration
/// `patvar_name` controls the name to give to the variables introduced in the
/// pattern. We introduce anonymous variables if `None`.
fn generate_variant_match_patterns(
    enum_name: &String,
    data: &DataEnum,
    patvar_name: Option<&String>,
) -> Vec<MatchPattern> {
    let mut patterns: Vec<MatchPattern> = vec![];
    for variant in &data.variants {
        let variant_name = variant.ident.to_string();

        // Indices for variables
        let mut var_index: usize = 0;
        fn generate_varname(var_index: &mut usize, patvar_name: Option<&String>) -> String {
            match patvar_name {
                None => "_".to_string(),
                Some(v) => {
                    let s = format!("{}{}", v, var_index).to_string();
                    *var_index = var_index.checked_add(1).unwrap();
                    s
                }
            }
        }

        // Compute the pattern (without the variant constructor), the list
        // of introduced arguments and the list of field types.
        let (pattern, num_vars, named_vars, vartypes) = match &variant.fields {
            Fields::Named(fields) => {
                let fields_vars: Vec<(String, String)> = fields
                    .named
                    .iter()
                    .map(|f| {
                        let var = generate_varname(&mut var_index, patvar_name);
                        let field = format!("{}:{}", f.ident.as_ref().unwrap().to_string(), var)
                            .to_string();
                        (field, var)
                    })
                    .collect();
                let (fields_pats, vars): (Vec<String>, Vec<String>) =
                    fields_vars.into_iter().unzip();

                let num_vars = fields.named.iter().count();

                let vars = if patvar_name.is_none() { vec![] } else { vars };

                let vartypes: Vec<String> =
                    fields.named.iter().map(|f| type_to_string(&f.ty)).collect();

                let pattern = format!("{{ {} }}", fields_pats.join(", ")).to_string();
                (pattern, num_vars, vars, vartypes)
            }
            Fields::Unnamed(fields) => {
                let fields_vars: Vec<(String, String)> = fields
                    .unnamed
                    .iter()
                    .map(|_| {
                        let var = generate_varname(&mut var_index, patvar_name);
                        (var.clone(), var)
                    })
                    .collect();

                let (fields_pats, vars): (Vec<String>, Vec<String>) =
                    fields_vars.into_iter().unzip();

                let num_vars = fields.unnamed.iter().count();

                let vars = if patvar_name.is_none() { vec![] } else { vars };

                let vartypes: Vec<String> = fields
                    .unnamed
                    .iter()
                    .map(|f| type_to_string(&f.ty))
                    .collect();

                let pattern = format!("({})", fields_pats.join(", ")).to_string();

                (pattern, num_vars, vars, vartypes)
            }
            Fields::Unit => ("".to_string(), 0, vec![], vec![]),
        };

        let pattern = format!("{}::{}{}", enum_name, variant_name, pattern).to_string();
        patterns.push(MatchPattern {
            variant_id: variant.ident.clone(),
            match_pattern: pattern,
            num_args: num_vars,
            named_args: named_vars,
            arg_types: vartypes,
        });
    }

    patterns
}

/// Macro to derive a function `fn variant_name(&self) -> String` printing the
/// constructor of an enumeration. Only works on enumerations, of course.
#[proc_macro_derive(VariantName)]
pub fn derive_variant_name(item: TokenStream) -> TokenStream {
    // Parse the input
    let ast: DeriveInput = parse(item).unwrap();

    // Generate the code
    let adt_name = ast.ident.to_string();

    // Retrieve and format the generic parameters
    let generic_params_with_constraints = generic_params_to_string(&ast.generics.params);
    let generic_params_without_constraints =
        generic_params_without_constraints_to_string(&ast.generics.params);

    // Generat the code for the `where` clause
    let where_clause = opt_where_clause_to_string(&ast.generics.where_clause);

    // Generate the code for the matches
    let match_branches: Vec<String> = match &ast.data {
        Data::Enum(data) => {
            let patterns = generate_variant_match_patterns(&adt_name, data, None);
            patterns
                .iter()
                .map(|mp| {
                    format!(
                        "{}{} => {{ \"{}\" }},",
                        THREE_TABS,
                        mp.match_pattern,
                        mp.variant_id.to_string()
                    )
                    .to_string()
                })
                .collect()
        }
        Data::Struct(_) => {
            panic!("VariantName macro can not be called on structs");
        }
        Data::Union(_) => {
            panic!("VariantName macro can not be called on unions");
        }
    };

    if match_branches.len() > 0 {
        let match_branches = match_branches.join("\n");
        let impl_code = format!(
            derive_variant_name_impl_code!(),
            generic_params_with_constraints,
            adt_name,
            generic_params_without_constraints,
            where_clause,
            match_branches
        )
        .to_string();
        return impl_code.parse().unwrap();
    } else {
        "".parse().unwrap()
    }
}

/// Macro to derive a function `fn variant_index_arity(&self) -> (u32, usize)`
/// the pair (variant index, variant arity).
/// Only works on enumerations, of course.
#[proc_macro_derive(VariantIndexArity)]
pub fn derive_variant_index_arity(item: TokenStream) -> TokenStream {
    // Parse the input
    let ast: DeriveInput = parse(item).unwrap();

    // Generate the code
    let adt_name = ast.ident.to_string();

    // Retrieve and format the generic parameters
    let generic_params_with_constraints = generic_params_to_string(&ast.generics.params);
    let generic_params_without_constraints =
        generic_params_without_constraints_to_string(&ast.generics.params);

    // Generat the code for the `where` clause
    let where_clause = opt_where_clause_to_string(&ast.generics.where_clause);

    // Generate the code for the matches
    let match_branches: Vec<String> = match &ast.data {
        Data::Enum(data) => {
            let patterns = generate_variant_match_patterns(&adt_name, data, None);
            patterns
                .iter()
                .enumerate()
                .map(|(i, mp)| {
                    format!(
                        "{}{} => {{ ({}, {}) }},",
                        THREE_TABS, mp.match_pattern, i, mp.num_args
                    )
                    .to_string()
                })
                .collect()
        }
        Data::Struct(_) => {
            panic!("VariantIndex macro can not be called on structs");
        }
        Data::Union(_) => {
            panic!("VariantIndex macro can not be called on unions");
        }
    };

    if match_branches.len() > 0 {
        let match_branches = match_branches.join("\n");
        let impl_code = format!(
            derive_variant_index_arity_impl_code!(),
            generic_params_with_constraints,
            adt_name,
            generic_params_without_constraints,
            where_clause,
            match_branches
        )
        .to_string();
        return impl_code.parse().unwrap();
    } else {
        "".parse().unwrap()
    }
}

#[derive(PartialEq, Eq)]
enum EnumMethodKind {
    EnumIsA,
    EnumAsGetters,
    EnumToGetters,
}

impl EnumMethodKind {
    /// We have to write this by hand: we can't use the macros defined above on
    /// the declarations of this file...
    fn variant_name(&self) -> String {
        match self {
            EnumMethodKind::EnumIsA => "EnumIsA".to_string(),
            EnumMethodKind::EnumAsGetters => "EnumAsGetters".to_string(),
            EnumMethodKind::EnumToGetters => "EnumToGetters".to_string(),
        }
    }
}

/// Generic helper for `EnumIsA` and `EnumAsGetters`.
/// This generates one function per variant.
fn derive_enum_variant_method(item: TokenStream, method_kind: EnumMethodKind) -> TokenStream {
    // Parse the input
    let ast: DeriveInput = parse(item).unwrap();

    // Generate the code
    let adt_name = ast.ident.to_string();

    // Retrieve and format the generic parameters
    let generic_params_with_constraints = generic_params_to_string(&ast.generics.params);
    let generic_params_without_constraints =
        generic_params_without_constraints_to_string(&ast.generics.params);

    // Generat the code for the `where` clause
    let where_clause = opt_where_clause_to_string(&ast.generics.where_clause);

    // Generate the code for all the functions in the impl block
    let impls: Vec<String> = match &ast.data {
        Data::Enum(data) => {
            // We start by generating the body of the function: the matches.
            //
            // If there is only one variant, we generate:
            // ```
            //  match self {
            //      Foo::Variant(...) => ...,
            // }
            // ```
            //
            // If there is more than one variant, we generate an otherwise branch:
            // ```
            //  match self {
            //      Foo::Variant(...) => ...,
            //      _ => ...,
            // }
            // ```
            //
            // Finally, If there are no variants, we don't generate any function,
            // so we don't really have to take that case into account...
            let several_variants = data.variants.len() > 1;
            let varbasename = match method_kind {
                EnumMethodKind::EnumIsA => None,
                EnumMethodKind::EnumAsGetters | EnumMethodKind::EnumToGetters => {
                    Some("x".to_string())
                }
            };
            let patterns = generate_variant_match_patterns(&adt_name, data, varbasename.as_ref());

            match method_kind {
                EnumMethodKind::EnumIsA => {
                    patterns
                        .iter()
                        .map(|mp| {
                            // Generate the branch for the target variant
                            let true_pat =
                                format!("{}{} => true,", THREE_TABS, mp.match_pattern,).to_string();
                            // Add the otherwise branch, if necessary
                            let complete_pat = if several_variants {
                                format!("{}\n{}_ => false,", true_pat, THREE_TABS).to_string()
                            } else {
                                true_pat
                            };

                            // Generate the impl
                            format!(
                                derive_enum_variant_impl_code!(),
                                "is_",
                                to_snake_case(&mp.variant_id.to_string()),
                                "&",
                                "bool",
                                complete_pat
                            )
                            .to_string()
                        })
                        .collect()
                }
                EnumMethodKind::EnumAsGetters | EnumMethodKind::EnumToGetters => {
                    let as_getters = match method_kind {
                        EnumMethodKind::EnumAsGetters => true,
                        _ => false,
                    };

                    patterns
                        .iter()
                        .map(|mp| {
                            // Generate the branch for the target variant
                            let vars = format!("({})", mp.named_args.join(", ")); // return value
                            let variant_pat =
                                format!("{}{} => {},", THREE_TABS, mp.match_pattern, vars)
                                    .to_string();
                            // Add the otherwise branch, if necessary
                            let complete_pat = if several_variants {
                                format!(
                                    "{}\n{}_ => unreachable!(\"{}::{}_{}: Not the proper variant\"),",
                                    variant_pat, THREE_TABS, adt_name,
                                    if as_getters { "as" } else { "to" },
                                    to_snake_case(&mp.variant_id.to_string()),
                                )
                                .to_string()
                            } else {
                                variant_pat
                            };

                            // The function's return type
                            let ret_tys: Vec<String> = mp
                                .arg_types
                                .iter()
                                .map(|ty| format!("{}({})", if as_getters {"&"} else {""},ty.to_string())
                                )
                                .collect();
                            let ret_ty = format!("({})", ret_tys.join(", "));

                            // Generate the impl
                            format!(
                                derive_enum_variant_impl_code!(),
                                if as_getters { "as_" } else { "to_" },
                                // TODO: write our own to_snake_case function:
                                // names like "i32" become "i_32" with this one.
                                to_snake_case(&mp.variant_id.to_string()),
                                if as_getters { "&" } else { "" },
                                ret_ty,
                                complete_pat
                            )
                            .to_string()
                        })
                        .collect()
                }
            }
        }
        Data::Struct(_) => {
            panic!(
                "{} macro can not be called on structs",
                method_kind.variant_name()
            );
        }
        Data::Union(_) => {
            panic!(
                "{} macro can not be called on unions",
                method_kind.variant_name()
            );
        }
    };

    if impls.len() > 0 {
        // Concatenate all the functions
        let impls = impls.join("\n\n");

        // Generate the impl block
        let impl_code = format!(
            derive_impl_block_code!(),
            generic_params_with_constraints,
            adt_name,
            generic_params_without_constraints,
            where_clause,
            impls
        )
        .to_string();
        return impl_code.parse().unwrap();
    } else {
        return "".parse().unwrap();
    }
}

/// Macro `EnumIsA`
/// Derives functions of the form `fn is_{variant_name}(&self) -> bool` returning true
/// if an enumeration instance is of some variant. For lists, it would generate
/// `is_cons` and `is_nil`.
/// Note that there already exists a crate implementing such macros,
/// [`enum_methods`](https://docs.rs/enum-methods/0.0.8/enum_methods/), but
/// it doesn't work when the enumeration has generic parameters and it seems
/// dead (a PR from 2019 has never been merged), so it seems better to maintain
/// our own code here (which is small) rather than doing PRs for this crate.
#[proc_macro_derive(EnumIsA)]
pub fn derive_enum_is_a(item: TokenStream) -> TokenStream {
    derive_enum_variant_method(item, EnumMethodKind::EnumIsA)
}

/// Macro `EnumAsGetters`
/// Derives functions of the form `fn as_{variant_name}(&self) -> ...` checking
/// that an enumeration instance is of the proper variant and returning shared
/// borrows to its fields.
/// Also see the comments for [crate::derive_enum_is_a]
#[proc_macro_derive(EnumAsGetters)]
pub fn derive_enum_as_getters(item: TokenStream) -> TokenStream {
    derive_enum_variant_method(item, EnumMethodKind::EnumAsGetters)
}

/// Macro `EnumToGetters`
/// Derives functions of the form `fn to_{variant_name}(self) -> ...` checking
/// that an enumeration instance is of the proper variant and returning its
/// fields (while consuming the instance).
/// Also see the comments for [crate::derive_enum_is_a]
#[proc_macro_derive(EnumToGetters)]
pub fn derive_enum_to_getters(item: TokenStream) -> TokenStream {
    derive_enum_variant_method(item, EnumMethodKind::EnumToGetters)
}

#[test]
fn test_snake_case() {
    let s = to_snake_case("ConstantValue");
    println!("{}", s);
    assert!(s == "constant_value".to_string());
}

fn generic_type_to_mut(ty: &mut Type) {
    match ty {
        Type::Reference(r) => match &mut r.mutability {
            Option::None => {
                r.mutability = Option::Some(syn::token::Mut([Span::call_site().into()]))
            }
            Option::Some(_) => (),
        },
        _ => (),
    }
}

fn generic_stmt_to_mut(s: &mut Stmt) {
    match s {
        Stmt::Local(s) => s
            .init
            .iter_mut()
            .for_each(|e| generic_expr_to_mut(&mut e.1)),
        Stmt::Item(item) => generic_item_to_mut(item),
        Stmt::Expr(e) => generic_expr_to_mut(e),
        Stmt::Semi(e, _) => generic_expr_to_mut(e),
    }
}

fn generic_stmts_to_mut(stmts: &mut Vec<Stmt>) {
    for stmt in stmts {
        generic_stmt_to_mut(stmt)
    }
}

fn generic_item_to_mut(item: &mut Item) {
    use Item::*;
    match item {
        Const(_) => unimplemented!("Item::Const"),
        Enum(_) => unimplemented!("Item::Enum"),
        ExternCrate(_) => unimplemented!("Item::ExternCrate"),
        Fn(_) => unimplemented!("Item::Fn"),
        ForeignMod(_) => unimplemented!("Item::ForeignMod"),
        Impl(_) => unimplemented!("Item::Impl"),
        Macro(_) => unimplemented!("Item::Macro"),
        Macro2(_) => unimplemented!("Item::Macro2"),
        Mod(_) => unimplemented!("Item::Mod"),
        Static(_) => unimplemented!("Item::Static"),
        Struct(_) => unimplemented!("Item::Struct"),
        Trait(_) => unimplemented!("Item::Trait"),
        TraitAlias(_) => unimplemented!("Item::TraitAlias"),
        Type(_) => unimplemented!("Item::Type"),
        Union(_) => unimplemented!("Item::Union"),
        Use(_) => (), // Nothing to do
        Verbatim(_) => unimplemented!("Item::Verbatim"),
        #[cfg_attr(test, deny(non_exhaustive_omitted_patterns))]
        _ => {
            unimplemented!();
        }
    }
}

fn generic_block_to_mut(e: &mut Block) {
    generic_stmts_to_mut(&mut (e.stmts));
}

fn generic_expr_to_mut(e: &mut Expr) {
    // There are really a lot of cases: we try to filter the ones in which
    // we are not interested.
    match e {
        Expr::Assign(e) => {
            generic_expr_to_mut(&mut (*e.left));
            generic_expr_to_mut(&mut (*e.right));
        }
        Expr::AssignOp(e) => {
            generic_expr_to_mut(&mut (*e.left));
            generic_expr_to_mut(&mut (*e.right));
        }
        Expr::Binary(e) => {
            generic_expr_to_mut(&mut (*e.left));
            generic_expr_to_mut(&mut (*e.right));
        }
        Expr::Block(e) => {
            generic_block_to_mut(&mut (e.block));
        }
        Expr::Box(e) => {
            generic_expr_to_mut(&mut (*e.expr));
        }
        Expr::Call(e) => {
            generic_expr_to_mut(&mut (*e.func));
            for arg in e.args.iter_mut() {
                generic_expr_to_mut(arg);
            }
        }
        Expr::Closure(e) => {
            // Keeping things simple
            e.inputs.iter_mut().for_each(|i| generic_pat_to_mut(i));
            generic_expr_to_mut(&mut (*e.body));
        }
        Expr::Field(e) => {
            generic_expr_to_mut(&mut (*e.base));
        }
        Expr::ForLoop(e) => {
            // We ignore the pattern for now
            generic_expr_to_mut(&mut (*e.expr));
            generic_block_to_mut(&mut (e.body));
        }
        Expr::Group(e) => {
            generic_expr_to_mut(&mut (*e.expr));
        }
        Expr::If(e) => {
            generic_expr_to_mut(&mut (*e.cond));
            generic_block_to_mut(&mut (e.then_branch));
            e.else_branch
                .iter_mut()
                .for_each(|(_, b)| generic_expr_to_mut(b));
        }
        Expr::Index(e) => {
            generic_expr_to_mut(&mut (*e.expr));
            generic_expr_to_mut(&mut (*e.index));
        }
        Expr::Let(e) => {
            // Ignoring the pattern
            generic_expr_to_mut(&mut (*e.expr));
        }
        Expr::Loop(e) => {
            generic_block_to_mut(&mut (e.body));
        }
        Expr::Macro(_) => {
            // Doing nothing
        }
        Expr::Match(e) => {
            generic_expr_to_mut(&mut (*e.expr));
            e.arms.iter_mut().for_each(|a| {
                a.guard.iter_mut().for_each(|(_, g)| generic_expr_to_mut(g));
                generic_expr_to_mut(&mut a.body)
            });
        }
        Expr::MethodCall(e) => {
            generic_expr_to_mut(&mut (*e.receiver));
            e.args.iter_mut().for_each(|a| generic_expr_to_mut(a));

            // IMPORTANT: check the name of the method: if it is `iter` change
            // to `iter_mut`
            let id = e.method.to_string();
            if id == "iter" {
                e.method = Ident::new("iter_mut", Span::call_site().into());
            }
        }
        Expr::Paren(e) => {
            generic_expr_to_mut(&mut (*e.expr));
        }
        Expr::Path(_) => {
            // Doing nothing
        }
        Expr::Reference(e) => {
            // IMPORTANT: change the mutability
            // Remark: closures are handled elsewhere
            e.mutability = Option::Some(syn::token::Mut([Span::call_site().into()]));
            generic_expr_to_mut(&mut (*e.expr));
        }
        Expr::Return(e) => {
            e.expr.iter_mut().for_each(|e| generic_expr_to_mut(e));
        }
        Expr::Type(e) => {
            generic_expr_to_mut(&mut (*e.expr));
            generic_type_to_mut(&mut (*e.ty));
        }
        Expr::While(e) => {
            generic_expr_to_mut(&mut (*e.cond));
            generic_block_to_mut(&mut (e.body));
        }
        _ => (),
    }
}

/// We use this method to update the names of the supertraits
/// when defining an implementation generic over the borrow type.
///
/// For instance, if we write:
/// ```
/// make_generic_in_borrows! {
///   trait AstVisitor : ExprVisitor { ... }
/// }
/// ```
///
/// We want to generate two definitions:
/// ```
/// make_generic_in_borrows! {
///   trait SharedAstVisitor : SharedExprVisitor { ... }
/// }
/// ```
///
/// and:
/// ```
/// make_generic_in_borrows! {
///   trait MutAstVisitor : MutExprVisitor { ... }
/// }
/// ```
fn generic_supertraits_to_mut_shared(tr: &mut ItemTrait, to_mut: bool) {
    for p in tr.supertraits.iter_mut() {
        match p {
            TypeParamBound::Trait(t) => {
                // Update the path: update the last segment
                let mut it = t.path.segments.iter_mut();
                let mut last_s = it.next().unwrap();
                while let Some(s) = it.next() {
                    last_s = s;
                }
                last_s.ident = generic_mk_ident(&last_s.ident, to_mut);
            }
            TypeParamBound::Lifetime(_) => (),
        }
    }
}

fn generic_mk_ident(id: &syn::Ident, to_mut: bool) -> syn::Ident {
    // TODO: not sure about the spans
    // Not very clean, but does the job
    let id = id.to_string();
    let name = if to_mut {
        format!("Mut{}", id)
    } else {
        format!("Shared{}", id)
    };
    syn::Ident::new(&name, Span::call_site().into())
}

fn generic_pat_to_mut(p: &mut Pat) {
    match p {
        Pat::Type(p) => generic_type_to_mut(&mut p.ty),
        _ => (),
    }
}

fn generic_mk_item(id: &Ident, to_mut: bool, item: &mut TraitItem) {
    match item {
        TraitItem::Const(_) | TraitItem::Macro(_) => {
            unimplemented!("Trait item")
        }
        TraitItem::Type(ty) => {
            // Update the references to self (we need to change the name).
            // For now, we only update the bounds
            for bound in &mut ty.bounds {
                if let TypeParamBound::Trait(tr) = bound {
                    if tr.path.segments.len() == 1 {
                        if let Some(last) = tr.path.segments.last_mut() {
                            if &last.ident == id {
                                last.ident = generic_mk_ident(&mut last.ident, to_mut)
                            }
                        }
                    }
                }
            }
        }
        TraitItem::Verbatim(_) => (),
        TraitItem::Method(s) => {
            // Update the borrows
            if to_mut {
                // Update the signature
                for input in &mut s.sig.inputs {
                    match input {
                        FnArg::Receiver(_) => {
                            /* We don't touch the self parameter for now */
                            ()
                        }
                        FnArg::Typed(arg) => {
                            // Change the reference types
                            generic_type_to_mut(&mut (*arg.ty));
                        }
                    }
                }

                match &mut s.sig.output {
                    ReturnType::Default => (),
                    ReturnType::Type(_, ty) => {
                        generic_type_to_mut(ty);
                    }
                }

                // Update the body
                // - we replace all the references
                // - we replace the occurrences of `iter`
                match &mut s.default {
                    Option::None => (),
                    Option::Some(body) => {
                        generic_stmts_to_mut(&mut body.stmts);
                    }
                }
            }
        }
        #[cfg_attr(test, deny(non_exhaustive_omitted_patterns))]
        _ => {
            /* See the fox of [TraitItem] */
            unimplemented!()
        }
    }
}

/// We use this macro to write implementation which are generic in borrow
/// kinds (i.e., from one implementation, we derive two implementations which
/// use shared borrows or mut borrows).
///
/// Note that this macro is meant to work on a limited set of cases: it is not
/// very general.
/// For instance, for now it only works on traits.
///
/// Applied on a trait definition named "Trait", it will generate two traits:
/// "MutTrait" and "SharedTrait".
#[proc_macro]
pub fn make_generic_in_borrows(tokens: TokenStream) -> TokenStream {
    let input_item = parse_macro_input!(tokens as ItemTrait);
    // We should have received the shared version
    let mut shared_item = input_item.clone();
    let mut mut_item = input_item;

    let id = shared_item.ident.clone();
    mut_item.ident = generic_mk_ident(&id, true);
    shared_item.ident = generic_mk_ident(&id, false);

    generic_supertraits_to_mut_shared(&mut shared_item, false);
    generic_supertraits_to_mut_shared(&mut mut_item, true);

    // Update the shared version
    for item in &mut shared_item.items {
        generic_mk_item(&id, false, item)
    }

    // Update the mutable version
    for item in &mut mut_item.items {
        generic_mk_item(&id, true, item)
    }

    // TODO: This is not very clean, but I don't know how to concatenate stream tokens
    format!(
        "{}\n{}",
        shared_item.to_token_stream(),
        mut_item.to_token_stream()
    )
    .parse()
    .unwrap()
}
