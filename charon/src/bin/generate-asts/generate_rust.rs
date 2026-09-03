//! Generate copies of some internal rustc types, to be part of the Charon AST.
//!
//! We add the selected datatypes and their dependencies to `ast/from_rustc.rs`, and the
//! translation code to `translate_from_rustc.rs`.
use anyhow::{Context, Result, bail};
use charon_lib::ast::*;
use itertools::Itertools;
use std::cell::{Cell, RefCell};
use std::collections::{BTreeMap, HashMap, HashSet, VecDeque};
use std::fmt;
use std::fs;

mod ast;
mod translation;

type Path = &'static str;
type GeneratedTypePrinter =
    fn(&Generator<'_>, &mut fmt::Formatter<'_>, &GenericArgs) -> fmt::Result;
type TranslationExprPrinter =
    fn(&Generator<'_>, &mut fmt::Formatter<'_>, &GenericArgs, &str) -> fmt::Result;

#[derive(Clone, Copy)]
enum RustcDatatype {
    /// Copy this rustc ADT into Charon's AST.
    Copy {
        /// If `Some`, only copy the selected variants.
        selected_variants: Option<&'static [&'static str]>,
    },
    /// Use custom generated and translated representations for this type.
    Special {
        fmt_type: GeneratedTypePrinter,
        fmt_translation: TranslationExprPrinter,
    },
}

#[derive(Default)]
pub(crate) struct RustcDatatypes {
    datatypes: SeqHashMap<Path, RustcDatatype>,
}

impl RustcDatatype {
    fn is_copy(&self) -> bool {
        matches!(self, RustcDatatype::Copy { .. })
    }

    fn selected_variants(&self) -> Option<&'static [&'static str]> {
        match self {
            RustcDatatype::Copy { selected_variants } => *selected_variants,
            RustcDatatype::Special { .. } => None,
        }
    }
}

impl RustcDatatypes {
    pub(crate) fn new() -> Self {
        use RustcDatatype::{Copy, Special};

        let mut datatypes = RustcDatatypes::default();
        datatypes.insert(
            "rustc_attr_ir::data_structures::AttributeKind",
            Copy {
                selected_variants: Some(&[
                    "AutomaticallyDerived",
                    "Cold",
                    "Deprecated",
                    "Fundamental",
                    "Ignore",
                    "Inline",
                    "MayDangle",
                    "Naked",
                    "NoLink",
                    "NoMangle",
                    "NonExhaustive",
                    "Optimize",
                    "RustcAlign",
                    "RustcIntrinsic",
                    "RustcTestEntrypointMarker",
                    "ShouldPanic",
                    "TargetFeature",
                    "TrackCaller",
                ]),
            },
        );
        datatypes.insert(
            "rustc_attr_ir::lang_items::LangItem",
            Copy {
                selected_variants: None,
            },
        );
        datatypes.insert(
            "rustc_abi::Align",
            Special {
                fmt_type: |_, f, _| write!(f, "u64"),
                fmt_translation: |_, f, _, value| write!(f, "{value}.bytes()"),
            },
        );
        datatypes.insert(
            "rustc_span::span_encoding::Span",
            Special {
                fmt_type: |_, f, _| write!(f, "Span"),
                fmt_translation: |_, f, _, value| write!(f, "self.translate_span({value})"),
            },
        );
        datatypes.insert(
            "core::option::Option",
            Special {
                fmt_type: |generator, f, generics| {
                    let ty = generics.types.iter().next().unwrap();
                    write!(f, "Option<{}>", generator.generated_type(ty))
                },
                fmt_translation: |generator, f, generics, value| {
                    let ty = generics.types.iter().next().unwrap();
                    write!(f, "({value}).as_ref().map(|value| ")?;
                    generator.fmt_result_translation_expr(f, ty, "value")?;
                    write!(f, ").transpose()?")
                },
            },
        );
        datatypes.insert(
            "thin_vec::ThinVec",
            Special {
                fmt_type: |generator, f, generics| {
                    let ty = generics.types.iter().next().unwrap();
                    write!(f, "Vec<{}>", generator.generated_type(ty))
                },
                fmt_translation: |generator, f, generics, value| {
                    let ty = generics.types.iter().next().unwrap();
                    write!(f, "({value}).iter().map(|value| ")?;
                    generator.fmt_result_translation_expr(f, ty, "value")?;
                    write!(f, ").collect::<Result<Vec<_>, FromRustcError>>()?")
                },
            },
        );
        datatypes.insert(
            "rustc_span::def_id::DefId",
            Special {
                fmt_type: |_, f, _| write!(f, "Ustr"),
                fmt_translation: |_, f, _, value| {
                    write!(f, "self.tcx.def_path_str(*({value})).into()")
                },
            },
        );
        datatypes.insert(
            "rustc_span::symbol::Symbol",
            Special {
                fmt_type: |_, f, _| write!(f, "Ustr"),
                fmt_translation: |_, f, _, value| write!(f, "({value}).to_string().into()"),
            },
        );
        datatypes
    }

    fn insert(&mut self, path: Path, datatype: RustcDatatype) {
        self.datatypes.insert(path, datatype);
    }

    pub(crate) fn paths_to_start_from(&self) -> impl Iterator<Item = Path> + '_ {
        self.datatypes
            .iter()
            .filter(|(_, datatype)| datatype.is_copy())
            .map(|(path, _)| *path)
    }

    fn resolve(
        &self,
        crate_data: &TranslatedCrate,
    ) -> Result<SeqHashMap<TypeDeclId, RustcDatatype>> {
        fn name_matches_path(name: &Name, path: &str) -> bool {
            let mut elems = name.name.iter();
            let mut parts = path.split("::");
            loop {
                match (elems.next(), parts.next()) {
                    (None, None) => return true,
                    (Some(PathElem::Ident(name, disambiguator)), Some(part))
                        if disambiguator.is_zero() && name == part => {}
                    _ => return false,
                }
            }
        }

        let mut datatypes = SeqHashMap::new();
        for (&path, datatype) in &self.datatypes {
            let ids = crate_data
                .type_decls
                .iter()
                .filter(|decl| name_matches_path(&decl.item_meta.name, path))
                .map(|decl| decl.def_id)
                .collect_vec();
            match ids.as_slice() {
                [] => {
                    if datatype.is_copy() {
                        bail!("could not find translated `{path}`")
                    }
                }
                [id] => {
                    datatypes.insert(*id, *datatype);
                }
                _ => bail!("ambiguous translated path `{path}`"),
            }
        }
        Ok(datatypes)
    }
}

pub(crate) fn generate(crate_data: &TranslatedCrate, datatypes: &RustcDatatypes) -> Result<()> {
    Generator::new(crate_data, datatypes)?.write_files()
}

#[derive(Clone)]
struct Generator<'a> {
    crate_data: &'a TranslatedCrate,
    datatypes: SeqHashMap<TypeDeclId, RustcDatatype>,
    variant_filters: HashMap<TypeDeclId, HashSet<VariantId>>,
    /// Types we are yet to generate.
    queue: RefCell<VecDeque<TypeDeclId>>,
    /// Types that have been added to the output.
    generated: RefCell<HashSet<TypeDeclId>>,
    current_decl: Cell<Option<TypeDeclId>>,
}

impl<'a> Generator<'a> {
    fn new(crate_data: &'a TranslatedCrate, datatypes: &RustcDatatypes) -> Result<Self> {
        let datatypes = datatypes.resolve(crate_data)?;
        let mut generator = Generator {
            crate_data,
            datatypes,
            variant_filters: HashMap::new(),
            queue: RefCell::new(VecDeque::new()),
            generated: RefCell::new(HashSet::new()),
            current_decl: Cell::new(None),
        };
        generator.variant_filters = generator.resolve_variant_filters()?;
        for (id, datatype) in &generator.datatypes {
            if datatype.is_copy() {
                generator.enqueue(*id);
            }
        }
        Ok(generator)
    }

    fn write_files(self) -> Result<()> {
        let ast_generator = self.clone();
        let ast_defs = ast_generator.ast_defs().to_string();
        ast_generator.check_duplicate_type_names()?;

        let translation_code = self.translation_code().to_string();
        self.check_duplicate_type_names()?;

        fs::write("src/ast/from_rustc.rs", ast_defs)
            .context("failed to write src/ast/from_rustc.rs")?;
        fs::write(
            "src/bin/charon-driver/translate/translate_from_rustc.rs",
            translation_code,
        )
        .context("failed to write translate_from_rustc.rs")?;
        Ok(())
    }

    fn unsupported_type(&self, ty: impl fmt::Display) -> ! {
        let context = self
            .current_decl
            .get()
            .expect("unsupported type encountered outside a type declaration");
        panic!(
            "unsupported rustc type `{ty}` while generating `{}`",
            self.debug_type_name(context)
        )
    }

    fn resolve_variant_filters(&self) -> Result<HashMap<TypeDeclId, HashSet<VariantId>>> {
        let mut filters = HashMap::new();
        for (id, datatype) in &self.datatypes {
            let Some(selected_names) = datatype.selected_variants() else {
                continue;
            };
            let TypeDeclKind::Enum(variants) = &self.crate_data[*id].kind else {
                bail!(
                    "variant filter configured for non-enum `{}`",
                    self.debug_type_name(*id)
                );
            };
            let selected_names = selected_names.iter().copied().collect::<HashSet<_>>();
            let available_names = variants
                .iter()
                .map(|variant| variant.name.as_str())
                .collect::<HashSet<_>>();
            for name in &selected_names {
                if !available_names.contains(name) {
                    bail!("unknown variant {name} for `{}`", self.debug_type_name(*id));
                }
            }
            let variants = variants
                .iter()
                .filter(|variant| selected_names.contains(variant.name.as_str()))
                .map(|variant| variant.id)
                .collect();
            filters.insert(*id, variants);
        }
        Ok(filters)
    }

    fn enqueue(&self, id: TypeDeclId) -> bool {
        if !self.should_generate_decl(id) {
            return false;
        }
        if self.generated.borrow_mut().insert(id) {
            self.queue.borrow_mut().push_back(id);
        }
        true
    }

    fn next_decl(&self) -> Option<&TypeDecl> {
        let id = self.queue.borrow_mut().pop_front()?;
        self.current_decl.set(Some(id));
        Some(&self.crate_data[id])
    }

    fn should_generate_decl(&self, id: TypeDeclId) -> bool {
        let decl = &self.crate_data[id];
        !self
            .datatype_for(id)
            .is_some_and(|datatype| matches!(datatype, RustcDatatype::Special { .. }))
            && decl.generics.is_empty()
            && matches!(
                decl.kind,
                TypeDeclKind::Struct(_)
                    | TypeDeclKind::Enum(_)
                    | TypeDeclKind::Union(_)
                    | TypeDeclKind::Alias(_)
            )
    }

    fn check_duplicate_type_names(&self) -> Result<()> {
        let mut by_name: BTreeMap<&str, Vec<TypeDeclId>> = BTreeMap::new();
        for id in self.generated.borrow().iter().copied() {
            by_name.entry(self.type_name(id)).or_default().push(id);
        }
        let duplicates = by_name
            .iter()
            .filter(|(_, ids)| ids.len() > 1)
            .map(|(name, ids)| {
                format!(
                    "{name}: {}",
                    ids.iter().map(|id| self.debug_type_name(*id)).join(", ")
                )
            })
            .collect_vec();
        if !duplicates.is_empty() {
            bail!(
                "duplicate generated type names; add a disambiguation rule:\n{}",
                duplicates.join("\n")
            );
        }
        Ok(())
    }

    fn variants<'b>(&self, decl: &'b TypeDecl) -> Vec<&'b Variant> {
        let TypeDeclKind::Enum(variants) = &decl.kind else {
            return vec![];
        };
        if let Some(selected) = self.variant_filters.get(&decl.def_id) {
            variants
                .iter()
                .filter(|variant| selected.contains(&variant.id))
                .collect()
        } else {
            variants.iter().collect()
        }
    }

    fn type_name(&self, id: TypeDeclId) -> &str {
        self.crate_data[id]
            .item_meta
            .name
            .short_str()
            .expect("generated rustc type does not have a short name")
    }

    fn debug_type_name(&self, id: TypeDeclId) -> String {
        self.crate_data[id]
            .item_meta
            .name
            .debug_repr(self.crate_data)
    }

    fn datatype_for(&self, id: TypeDeclId) -> Option<&RustcDatatype> {
        self.datatypes.get(&id)
    }
}
