//! This file groups everything which is linked to implementations about [crate::types]
#![allow(dead_code)]

use crate::assumed::get_name_from_type_id;
use crate::common::TAB_INCR;
use crate::formatter::Formatter;
use crate::types::*;
use crate::ullbc_ast::*;
use crate::values::*;
use hax_frontend_exporter as hax;
use im::{HashMap, OrdSet};
use macros::make_generic_in_borrows;
use std::iter::FromIterator;
use std::iter::Iterator;

pub type RegionSubst<R> = HashMap<RegionVarId::Id, R>;
pub type TypeSubst<R> = HashMap<TypeVarId::Id, Ty<R>>;
/// Type substitution where the regions are erased
pub type ETypeSubst = TypeSubst<ErasedRegion>;
pub type ConstGenericSubst = HashMap<ConstGenericVarId::Id, ConstGeneric>;

// TODO: should we just put all the potential constraints we need in there?
pub trait TypeFormatter<'a, R: 'a> = Formatter<TypeVarId::Id>
    + Formatter<&'a R>
    + Formatter<&'a ErasedRegion>
    + Formatter<&'a Region<RegionVarId::Id>>
    + Formatter<TypeDeclId::Id>
    + Formatter<ConstGenericVarId::Id>
    + Formatter<FunDeclId::Id>
    + Formatter<GlobalDeclId::Id>
    + Formatter<TraitDeclId::Id>
    + Formatter<TraitImplId::Id>
    + Formatter<TraitClauseId::Id>
    + Formatter<RegionVarId::Id>;

impl ConstGenericVarId::Id {
    pub fn substitute(
        &self,
        cgsubst: &dyn Fn(&ConstGenericVarId::Id) -> ConstGeneric,
    ) -> ConstGeneric {
        cgsubst(self)
    }
}

impl ConstGeneric {
    pub fn substitute(
        &self,
        cgsubst: &dyn Fn(&ConstGenericVarId::Id) -> ConstGeneric,
    ) -> ConstGeneric {
        match self {
            ConstGeneric::Var(id) => id.substitute(cgsubst),
            ConstGeneric::Value(v) => ConstGeneric::Value(v.clone()),
            ConstGeneric::Global(id) => ConstGeneric::Global(*id),
        }
    }
}

impl RegionVarId::Id {
    pub fn substitute<R>(&self, rsubst: &RegionSubst<R>) -> R
    where
        R: Clone,
    {
        rsubst.get(self).unwrap().clone()
    }
}

impl<Rid: Clone> Region<Rid> {
    pub fn fmt_with_ctx<T>(&self, ctx: &T) -> String
    where
        T: Formatter<Rid>,
    {
        match self {
            Region::Static => "'static".to_string(),
            Region::Var(id) => ctx.format_object(id.clone()),
        }
    }
}

impl<Rid1: Clone + Ord + std::hash::Hash> Region<Rid1> {
    pub fn substitute<Rid2: Clone>(&self, rsubst: &HashMap<Rid1, Region<Rid2>>) -> Region<Rid2> {
        match self {
            Region::Static => Region::Static,
            Region::Var(id) => rsubst.get(id).unwrap().clone(),
        }
    }

    pub fn contains_var(&self, rset: &OrdSet<Rid1>) -> bool {
        match self {
            Region::Static => false,
            Region::Var(id) => rset.contains(id),
        }
    }
}

impl TypeVar {
    pub fn new(index: TypeVarId::Id, name: String) -> TypeVar {
        TypeVar { index, name }
    }

    pub fn fresh(name: String, gen: &mut TypeVarId::Generator) -> TypeVar {
        TypeVar {
            index: gen.fresh_id(),
            name,
        }
    }
}

impl std::string::ToString for TypeVar {
    fn to_string(&self) -> String {
        self.name.to_string()
    }
}

impl std::string::ToString for RegionVar {
    fn to_string(&self) -> String {
        let id = self.index.to_pretty_string();
        match &self.name {
            Some(name) => name.to_string(),
            None => id,
        }
    }
}

impl std::string::ToString for ConstGenericVar {
    fn to_string(&self) -> String {
        format!("const {} : {}", self.name, self.ty.to_string())
    }
}

impl GenericParams {
    pub fn len(&self) -> usize {
        let GenericParams {
            regions,
            types,
            const_generics,
            trait_clauses,
        } = self;
        regions.len() + types.len() + const_generics.len() + trait_clauses.len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn empty() -> Self {
        GenericParams {
            regions: RegionVarId::Vector::new(),
            types: TypeVarId::Vector::new(),
            const_generics: ConstGenericVarId::Vector::new(),
            trait_clauses: TraitClauseId::Vector::new(),
        }
    }

    pub fn fmt_with_ctx<'a, C>(&'a self, ctx: &C) -> String
    where
        C: TypeFormatter<'a, Region<RegionVarId::Id>>,
    {
        if self.is_empty() {
            "".to_string()
        } else {
            let mut params = Vec::new();
            let GenericParams {
                regions,
                types,
                const_generics,
                trait_clauses,
            } = self;
            for x in regions {
                params.push(x.to_string());
            }
            for x in types {
                params.push(x.to_string());
            }
            for x in const_generics {
                params.push(x.to_string());
            }
            for x in trait_clauses {
                params.push(x.fmt_with_ctx(ctx));
            }
            format!("<{}>", params.join(", "))
        }
    }

    pub fn fmt_with_ctx_with_trait_clauses<'a, C>(&'a self, ctx: &C) -> (String, Vec<String>)
    where
        C: TypeFormatter<'a, Region<RegionVarId::Id>>,
    {
        let mut params = Vec::new();
        let GenericParams {
            regions,
            types,
            const_generics,
            trait_clauses,
        } = self;
        for x in regions {
            params.push(x.to_string());
        }
        for x in types {
            params.push(x.to_string());
        }
        for x in const_generics {
            params.push(x.to_string());
        }
        let params = if params.is_empty() {
            "".to_string()
        } else {
            format!("<{}>", params.join(", "))
        };

        let mut clauses = Vec::new();
        for x in trait_clauses {
            clauses.push(x.fmt_with_ctx(ctx));
        }
        (params, clauses)
    }
}

/// [num_parent_clauses]: we store in the definitions all the clauses
/// they have access to, which includes the clauses inherited from the parent.
/// This can be confusing: we insert a delimiter between the inherited clauses
/// and the local clauses.
pub fn fmt_where_clauses(tab: &str, num_parent_clauses: usize, clauses: Vec<String>) -> String {
    if clauses.is_empty() {
        "".to_string()
    } else {
        let mut clauses = clauses
            .iter()
            .map(|x| format!("\n{tab}{TAB_INCR}{x},"))
            .collect::<Vec<String>>();
        if num_parent_clauses > 0 {
            let local_clauses = clauses.split_off(num_parent_clauses);

            let delim1 = if local_clauses.is_empty() {
                "".to_string()
            } else {
                format!("\n{tab}{TAB_INCR}// Local clauses:")
            };

            let delim0 = if clauses.is_empty() {
                "".to_string()
            } else {
                format!("\n{tab}{TAB_INCR}// Inherited clauses:")
            };

            let clauses = clauses.join("");
            let local_clauses = local_clauses.join("");
            format!("\n{tab}where{delim0}{clauses}{delim1}{local_clauses}")
        } else {
            let clauses = clauses.join("");
            format!("\n{tab}where{clauses}")
        }
    }
}

impl<R> TraitTypeConstraint<R> {
    pub fn fmt_with_ctx<'a, C>(&'a self, ctx: &C) -> String
    where
        C: TypeFormatter<'a, R>,
    {
        let trait_ref = self.trait_ref.fmt_with_ctx(ctx);
        let generics = self.generics.fmt_with_ctx_split_trait_refs(ctx);
        let ty = self.ty.fmt_with_ctx(ctx);
        format!("{}{}::{} = {}", trait_ref, generics, self.type_name, ty)
    }
}

pub fn fmt_where_clauses_with_ctx<'a, C>(
    ctx: &C,
    tab: &str,
    info: &Option<ParamsInfo>,
    mut trait_clauses: Vec<String>,
    preds: &'a Predicates,
) -> String
where
    C: TypeFormatter<'a, Region<RegionVarId::Id>>,
{
    let mut types_outlive: Vec<_> = preds
        .types_outlive
        .iter()
        .map(|OutlivesPred(x, y)| format!("{} : {}", x.fmt_with_ctx(ctx), y.fmt_with_ctx(ctx)))
        .collect();
    let mut regions_outlive: Vec<_> = preds
        .regions_outlive
        .iter()
        .map(|OutlivesPred(x, y)| format!("{} : {}", x.fmt_with_ctx(ctx), y.fmt_with_ctx(ctx)))
        .collect();
    let mut type_constraints: Vec<_> = preds
        .trait_type_constraints
        .iter()
        .map(|x| x.fmt_with_ctx(ctx))
        .collect();
    match info {
        None => {
            let clauses: Vec<_> = trait_clauses
                .into_iter()
                .chain(types_outlive.into_iter())
                .chain(regions_outlive.into_iter())
                .chain(type_constraints.into_iter())
                .collect();
            fmt_where_clauses(tab, 0, clauses)
        }
        Some(info) => {
            // Below: definitely not efficient nor convenient, but it is not really
            // important
            let local_clauses: Vec<_> = trait_clauses
                .split_off(info.num_trait_clauses)
                .into_iter()
                .chain(regions_outlive.split_off(info.num_regions_outlive))
                .chain(types_outlive.split_off(info.num_types_outlive).into_iter())
                .chain(
                    type_constraints
                        .split_off(info.num_trait_type_constraints)
                        .into_iter(),
                )
                .collect();
            let inherited_clauses: Vec<_> = trait_clauses
                .into_iter()
                .chain(regions_outlive.into_iter())
                .chain(types_outlive.into_iter())
                .chain(type_constraints.into_iter())
                .collect();
            let num_inherited = inherited_clauses.len();
            let all_clauses: Vec<_> = inherited_clauses
                .into_iter()
                .chain(local_clauses.into_iter())
                .collect();
            fmt_where_clauses(tab, num_inherited, all_clauses)
        }
    }
}

impl<R> GenericArgs<R> {
    pub fn len(&self) -> usize {
        let GenericArgs {
            regions,
            types,
            const_generics,
            trait_refs,
        } = self;
        regions.len() + types.len() + const_generics.len() + trait_refs.len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn empty() -> Self {
        GenericArgs {
            regions: Vec::new(),
            types: Vec::new(),
            const_generics: Vec::new(),
            trait_refs: Vec::new(),
        }
    }

    pub fn new_from_types(types: Vec<Ty<R>>) -> Self {
        GenericArgs {
            regions: Vec::new(),
            types,
            const_generics: Vec::new(),
            trait_refs: Vec::new(),
        }
    }

    pub fn new(
        regions: Vec<R>,
        types: Vec<Ty<R>>,
        const_generics: Vec<ConstGeneric>,
        trait_refs: Vec<TraitRef<R>>,
    ) -> Self {
        GenericArgs {
            regions,
            types,
            const_generics,
            trait_refs,
        }
    }

    pub(crate) fn fmt_with_ctx_no_brackets<'a, C>(&'a self, ctx: &C) -> String
    where
        C: TypeFormatter<'a, R>,
    {
        let mut params = Vec::new();
        let GenericArgs {
            regions,
            types,
            const_generics,
            trait_refs,
        } = self;
        for x in regions {
            params.push(ctx.format_object(x));
        }
        for x in types {
            params.push(x.fmt_with_ctx(ctx));
        }
        for x in const_generics {
            params.push(x.fmt_with_ctx(ctx));
        }
        for x in trait_refs {
            params.push(x.fmt_with_ctx(ctx))
        }
        params.join(", ")
    }

    pub fn fmt_with_ctx<'a, C>(&'a self, ctx: &C) -> String
    where
        C: TypeFormatter<'a, R>,
    {
        if self.is_empty() {
            "".to_string()
        } else {
            format!("<{}>", self.fmt_with_ctx_no_brackets(ctx),)
        }
    }

    pub fn fmt_with_ctx_split_trait_refs<'a, C>(&'a self, ctx: &C) -> String
    where
        C: TypeFormatter<'a, R>,
    {
        let mut params = Vec::new();
        let GenericArgs {
            regions,
            types,
            const_generics,
            trait_refs,
        } = self;
        for x in regions {
            params.push(ctx.format_object(x));
        }
        for x in types {
            params.push(x.fmt_with_ctx(ctx));
        }
        for x in const_generics {
            params.push(x.fmt_with_ctx(ctx));
        }
        let params = if params.is_empty() {
            "".to_string()
        } else {
            format!("<{}>", params.join(", "))
        };

        let mut clauses = Vec::new();
        for x in trait_refs {
            clauses.push(x.fmt_with_ctx(ctx));
        }
        let clauses = if clauses.is_empty() {
            "".to_string()
        } else {
            format!("[{}]", clauses.join(", "))
        };
        format!("{params}{clauses}")
    }
}

impl TraitClause {
    pub fn fmt_with_ctx<'a, C>(&'a self, ctx: &C) -> String
    where
        C: TypeFormatter<'a, Region<RegionVarId::Id>>,
    {
        let clause_id = ctx.format_object(self.clause_id);
        let trait_id = ctx.format_object(self.trait_id);
        let generics = self.generics.fmt_with_ctx(ctx);
        format!("[{clause_id}]: {trait_id}{generics}")
    }
}

impl TraitInstanceId {
    pub fn fmt_with_ctx<'a, C>(&'a self, ctx: &C) -> String
    where
        C: TypeFormatter<'a, ErasedRegion>,
    {
        match self {
            TraitInstanceId::SelfId => "Self".to_string(),
            TraitInstanceId::ParentClause(id, _decl_id, clause_id) => {
                let id = id.fmt_with_ctx(ctx);
                // Using on purpose [to_pretty_string] instead of [format_object]:
                // the clause is local to the associated type, so it should not
                // be referenced in the current context.
                let clause = clause_id.to_pretty_string();
                format!("(parents({id})::[{clause}])")
            }
            TraitInstanceId::ItemClause(id, _decl_id, type_name, clause_id) => {
                let id = id.fmt_with_ctx(ctx);
                // Using on purpose [to_pretty_string] instead of [format_object]:
                // the clause is local to the associated type, so it should not
                // be referenced in the current context.
                let clause = clause_id.to_pretty_string();
                format!("({id}::{type_name}::[{clause}])")
            }
            TraitInstanceId::TraitImpl(id) => ctx.format_object(*id),
            TraitInstanceId::Clause(id) => ctx.format_object(*id),
            TraitInstanceId::BuiltinOrAuto(id) => ctx.format_object(*id),
            TraitInstanceId::FnPointer(box ty) => {
                format!("(fn_ptr:{})", ty.fmt_with_ctx(ctx))
            }
            TraitInstanceId::Unknown(msg) => format!("UNKNOWN({msg})"),
        }
    }
}

impl<R> TraitRef<R> {
    pub fn fmt_with_ctx<'a, C>(&'a self, ctx: &C) -> String
    where
        C: TypeFormatter<'a, R>,
    {
        let trait_id = self.trait_id.fmt_with_ctx(ctx);
        let generics = self.generics.fmt_with_ctx_split_trait_refs(ctx);
        format!("{trait_id}{generics}")
    }
}

impl<R> TraitDeclRef<R> {
    pub fn fmt_with_ctx<'a, C>(&'a self, ctx: &C) -> String
    where
        C: TypeFormatter<'a, R>,
    {
        let trait_id = ctx.format_object(self.trait_id);
        let generics = self.generics.fmt_with_ctx_split_trait_refs(ctx);
        format!("{trait_id}{generics}")
    }
}

impl TypeDecl {
    /// The variant id should be `None` if it is a structure and `Some` if it
    /// is an enumeration.
    pub fn get_fields(&self, variant_id: Option<VariantId::Id>) -> &FieldId::Vector<Field> {
        match &self.kind {
            TypeDeclKind::Enum(variants) => &variants.get(variant_id.unwrap()).unwrap().fields,
            TypeDeclKind::Struct(fields) => {
                assert!(variant_id.is_none());
                fields
            }
            TypeDeclKind::Opaque => {
                unreachable!("Opaque type")
            }
        }
    }

    /// Instantiate the fields of every variant of a type definition.
    ///
    /// Return an option: `Some` if we have access to the type definition,
    /// `None` if the type is opaque.
    pub fn get_instantiated_variants(
        &self,
        inst_regions: &Vec<Region<RegionVarId::Id>>,
        inst_types: &Vec<RTy>,
    ) -> Option<VariantId::Vector<FieldId::Vector<RTy>>> {
        // Introduce the substitutions
        let r_subst = make_region_subst(
            self.generics.regions.iter().map(|x| x.index),
            inst_regions.iter(),
        );
        let ty_subst = make_type_subst(
            self.generics.types.iter().map(|x| x.index),
            inst_types.iter(),
        );

        match &self.kind {
            TypeDeclKind::Struct(fields) => {
                Option::Some(VariantId::Vector::from(vec![FieldId::Vector::from_iter(
                    fields
                        .iter()
                        .map(|f| f.ty.substitute_regions_types(&r_subst, &ty_subst)),
                )]))
            }
            TypeDeclKind::Enum(variants) => {
                Option::Some(VariantId::Vector::from_iter(variants.iter().map(|v| {
                    FieldId::Vector::from_iter(
                        v.fields
                            .iter()
                            .map(|f| f.ty.substitute_regions_types(&r_subst, &ty_subst)),
                    )
                })))
            }
            TypeDeclKind::Opaque => Option::None,
        }
    }

    /// The variant id should be `None` if it is a structure and `Some` if it
    /// is an enumeration.
    pub fn get_erased_regions_instantiated_field_types(
        &self,
        variant_id: Option<VariantId::Id>,
        inst_types: &Vec<ETy>,
        cgs: &Vec<ConstGeneric>,
    ) -> Vec<ETy> {
        // Introduce the substitution
        let ty_subst = make_type_subst(
            self.generics.types.iter().map(|x| x.index),
            inst_types.iter(),
        );
        let cg_subst = make_cg_subst(
            self.generics.const_generics.iter().map(|x| x.index),
            cgs.iter(),
        );

        let fields = self.get_fields(variant_id);
        let field_types: Vec<ETy> = fields
            .iter()
            .map(|f| f.ty.erase_regions_substitute_types(&ty_subst, &cg_subst))
            .collect();

        Vec::from(field_types)
    }

    /// The variant id should be `None` if it is a structure and `Some` if it
    /// is an enumeration.
    pub fn get_erased_regions_instantiated_field_type(
        &self,
        variant_id: Option<VariantId::Id>,
        inst_types: &Vec<ETy>,
        cgs: &Vec<ConstGeneric>,
        field_id: FieldId::Id,
    ) -> ETy {
        // Introduce the substitution
        let ty_subst = make_type_subst(
            self.generics.types.iter().map(|x| x.index),
            inst_types.iter(),
        );
        let cg_subst = make_cg_subst(
            self.generics.const_generics.iter().map(|x| x.index),
            cgs.iter(),
        );

        let fields = self.get_fields(variant_id);
        let field_type = fields
            .get(field_id)
            .unwrap()
            .ty
            .erase_regions()
            .substitute_types(&ty_subst, &cg_subst);
        field_type
    }

    pub fn fmt_with_ctx<'a, T>(&'a self, ctx: &'a T) -> String
    where
        T: TypeFormatter<'a, Region<RegionVarId::Id>>,
    {
        let (params, trait_clauses) = self.generics.fmt_with_ctx_with_trait_clauses(ctx);
        // Trait clauses
        let eq_space = if trait_clauses.is_empty() {
            "".to_string()
        } else {
            format!("\n ")
        };
        let trait_clauses = fmt_where_clauses("", 0, trait_clauses);

        match &self.kind {
            TypeDeclKind::Struct(fields) => {
                if !fields.is_empty() {
                    let fields: Vec<String> = fields
                        .iter()
                        .map(|f| format!("\n  {}", f.fmt_with_ctx(ctx)))
                        .collect();
                    let fields = fields.join(",");
                    format!(
                        "struct {}{params}{trait_clauses}{eq_space}=\n{{{fields}\n}}",
                        self.name
                    )
                } else {
                    format!(
                        "struct {}{params}{trait_clauses}{eq_space}= {{}}",
                        self.name
                    )
                }
            }
            TypeDeclKind::Enum(variants) => {
                let variants: Vec<String> = variants
                    .iter()
                    .map(|v| format!("|  {}", v.fmt_with_ctx(ctx)))
                    .collect();
                let variants = variants.join("\n");
                format!(
                    "enum {}{params}{trait_clauses}{eq_space}=\n{variants}\n",
                    self.name
                )
            }
            TypeDeclKind::Opaque => format!("opaque type {}{params}{trait_clauses}", self.name),
        }
    }
}

impl std::string::ToString for TypeDecl {
    fn to_string(&self) -> String {
        self.fmt_with_ctx(&DummyFormatter {})
    }
}

impl Variant {
    pub fn fmt_with_ctx<'a, T>(&'a self, ctx: &'a T) -> String
    where
        T: TypeFormatter<'a, Region<RegionVarId::Id>>,
    {
        let fields: Vec<String> = self.fields.iter().map(|f| f.fmt_with_ctx(ctx)).collect();
        let fields = fields.join(", ");
        format!("{}({})", self.name, fields)
    }
}

impl Field {
    pub fn fmt_with_ctx<'a, T>(&'a self, ctx: &'a T) -> String
    where
        T: TypeFormatter<'a, Region<RegionVarId::Id>>,
    {
        match &self.name {
            Option::Some(name) => format!("{}: {}", name, self.ty.fmt_with_ctx(ctx)),
            Option::None => self.ty.fmt_with_ctx(ctx),
        }
    }
}

impl std::string::ToString for Variant {
    fn to_string(&self) -> String {
        self.fmt_with_ctx(&DummyFormatter {})
    }
}

impl std::string::ToString for Field {
    fn to_string(&self) -> String {
        self.fmt_with_ctx(&DummyFormatter {})
    }
}

impl IntegerTy {
    pub fn rust_int_ty_to_integer_ty(ty: hax::IntTy) -> IntegerTy {
        use hax::IntTy::*;
        match ty {
            Isize => IntegerTy::Isize,
            I8 => IntegerTy::I8,
            I16 => IntegerTy::I16,
            I32 => IntegerTy::I32,
            I64 => IntegerTy::I64,
            I128 => IntegerTy::I128,
        }
    }

    pub fn rust_uint_ty_to_integer_ty(ty: hax::UintTy) -> IntegerTy {
        use hax::UintTy::*;
        match ty {
            Usize => IntegerTy::Usize,
            U8 => IntegerTy::U8,
            U16 => IntegerTy::U16,
            U32 => IntegerTy::U32,
            U64 => IntegerTy::U64,
            U128 => IntegerTy::U128,
        }
    }

    pub fn is_signed(&self) -> bool {
        matches!(
            self,
            IntegerTy::Isize
                | IntegerTy::I8
                | IntegerTy::I16
                | IntegerTy::I32
                | IntegerTy::I64
                | IntegerTy::I128
        )
    }

    pub fn is_unsigned(&self) -> bool {
        !(self.is_signed())
    }

    /// Return the size (in bytes) of an integer of the proper type
    pub fn size(&self) -> usize {
        use std::mem::size_of;
        match self {
            IntegerTy::Isize => size_of::<isize>(),
            IntegerTy::I8 => size_of::<i8>(),
            IntegerTy::I16 => size_of::<i16>(),
            IntegerTy::I32 => size_of::<i32>(),
            IntegerTy::I64 => size_of::<i64>(),
            IntegerTy::I128 => size_of::<i128>(),
            IntegerTy::Usize => size_of::<isize>(),
            IntegerTy::U8 => size_of::<u8>(),
            IntegerTy::U16 => size_of::<u16>(),
            IntegerTy::U32 => size_of::<u32>(),
            IntegerTy::U64 => size_of::<u64>(),
            IntegerTy::U128 => size_of::<u128>(),
        }
    }
}

impl TypeVarId::Id {
    pub fn to_pretty_string(&self) -> String {
        format!("@T{self}")
    }
}

impl TypeDeclId::Id {
    pub fn to_pretty_string(&self) -> String {
        format!("@Adt{self}")
    }
}

impl VariantId::Id {
    pub fn to_pretty_string(&self) -> String {
        format!("@Variant{self}")
    }
}

impl FieldId::Id {
    pub fn to_pretty_string(&self) -> String {
        format!("@Field{self}")
    }
}

impl RegionVarId::Id {
    pub fn to_pretty_string(&self) -> String {
        format!("@R{self}")
    }
}

impl ConstGenericVarId::Id {
    pub fn to_pretty_string(&self) -> String {
        format!("@Const{self}")
    }
}

impl GlobalDeclId::Id {
    pub fn to_pretty_string(&self) -> String {
        format!("@Global{self}")
    }
}

impl TraitClauseId::Id {
    pub fn to_pretty_string(&self) -> String {
        format!("@TraitClause{self}")
    }
}

impl TraitDeclId::Id {
    pub fn to_pretty_string(&self) -> String {
        format!("@TraitDecl{self}")
    }
}

impl TraitImplId::Id {
    pub fn to_pretty_string(&self) -> String {
        format!("@TraitImpl{self}")
    }
}

impl std::string::ToString for LiteralTy {
    fn to_string(&self) -> String {
        match self {
            LiteralTy::Integer(ty) => ty.to_string(),
            LiteralTy::Bool => "bool".to_string(),
            LiteralTy::Char => "char".to_string(),
        }
    }
}

impl std::fmt::Display for IntegerTy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        match self {
            IntegerTy::Isize => write!(f, "isize"),
            IntegerTy::I8 => write!(f, "i8"),
            IntegerTy::I16 => write!(f, "i16"),
            IntegerTy::I32 => write!(f, "i32"),
            IntegerTy::I64 => write!(f, "i64"),
            IntegerTy::I128 => write!(f, "i128"),
            IntegerTy::Usize => write!(f, "usize"),
            IntegerTy::U8 => write!(f, "u8"),
            IntegerTy::U16 => write!(f, "u16"),
            IntegerTy::U32 => write!(f, "u32"),
            IntegerTy::U64 => write!(f, "u64"),
            IntegerTy::U128 => write!(f, "u128"),
        }
    }
}

// IntTy is not defined in the current crate
pub fn intty_to_string(ty: hax::IntTy) -> String {
    use hax::IntTy::*;
    match ty {
        Isize => "isize".to_string(),
        I8 => "i8".to_string(),
        I16 => "i16".to_string(),
        I32 => "i32".to_string(),
        I64 => "i64".to_string(),
        I128 => "i128".to_string(),
    }
}

// UintTy is not defined in the current crate
fn uintty_to_string(ty: hax::UintTy) -> String {
    use hax::UintTy::*;
    match ty {
        Usize => "usize".to_string(),
        U8 => "u8".to_string(),
        U16 => "u16".to_string(),
        U32 => "u32".to_string(),
        U64 => "u64".to_string(),
        U128 => "u128".to_string(),
    }
}

impl TypeId {
    pub fn fmt_with_ctx<T>(&self, ctx: &T) -> String
    where
        T: Formatter<TypeDeclId::Id>,
    {
        match self {
            TypeId::Tuple => "".to_string(),
            TypeId::Adt(def_id) => ctx.format_object(*def_id),
            TypeId::Assumed(aty) => get_name_from_type_id(*aty).join("::"),
        }
    }
}

impl ConstGeneric {
    pub fn fmt_with_ctx<T>(&self, ctx: &T) -> String
    where
        T: Formatter<ConstGenericVarId::Id> + Formatter<GlobalDeclId::Id>,
    {
        match self {
            ConstGeneric::Var(id) => ctx.format_object(*id),
            ConstGeneric::Value(v) => v.to_string(),
            ConstGeneric::Global(id) => ctx.format_object(*id),
        }
    }
}

impl<R> Ty<R> {
    /// Return true if it is actually unit (i.e.: 0-tuple)
    pub fn is_unit(&self) -> bool {
        match self {
            Ty::Adt(TypeId::Tuple, args) => {
                assert!(args.regions.is_empty());
                assert!(args.const_generics.is_empty());
                args.types.is_empty()
            }
            _ => false,
        }
    }

    /// Return the unit type
    pub fn mk_unit() -> Ty<R> {
        Ty::Adt(TypeId::Tuple, GenericArgs::empty())
    }

    /// Return true if this is a scalar type
    pub fn is_scalar(&self) -> bool {
        match self {
            Ty::Literal(kind) => kind.is_integer(),
            _ => false,
        }
    }

    pub fn is_unsigned_scalar(&self) -> bool {
        match self {
            Ty::Literal(LiteralTy::Integer(kind)) => kind.is_unsigned(),
            _ => false,
        }
    }

    pub fn is_signed_scalar(&self) -> bool {
        match self {
            Ty::Literal(LiteralTy::Integer(kind)) => kind.is_signed(),
            _ => false,
        }
    }

    /// Format the type as a string.
    ///
    /// We take an optional type context to be able to implement the Display
    /// trait, in which case there is no type context available and we print
    /// the ADT ids rather than their names.
    pub fn fmt_with_ctx<'a, 'b, T>(&'a self, ctx: &'b T) -> String
    where
        R: 'a,
        T: TypeFormatter<'a, R>,
    {
        match self {
            Ty::Adt(id, generics) => {
                let adt_ident = id.fmt_with_ctx(ctx);

                if id.is_tuple() {
                    assert!(generics.trait_refs.is_empty());
                    let generics = generics.fmt_with_ctx_no_brackets(ctx);
                    format!("({generics})")
                } else {
                    let generics = generics.fmt_with_ctx(ctx);
                    format!("{adt_ident}{generics}")
                }
            }
            Ty::TypeVar(id) => ctx.format_object(*id),
            Ty::Literal(kind) => kind.to_string(),
            Ty::Never => "!".to_string(),
            Ty::Ref(r, ty, kind) => match kind {
                RefKind::Mut => {
                    format!("&{} mut ({})", ctx.format_object(r), ty.fmt_with_ctx(ctx))
                }
                RefKind::Shared => {
                    format!("&{} ({})", ctx.format_object(r), ty.fmt_with_ctx(ctx))
                }
            },
            Ty::RawPtr(ty, kind) => match kind {
                RefKind::Mut => format!("*const {}", ty.fmt_with_ctx(ctx)),
                RefKind::Shared => format!("*mut {}", ty.fmt_with_ctx(ctx)),
            },
            Ty::TraitType(trait_ref, substs, name) => {
                format!(
                    "{}{}::{name}",
                    trait_ref.fmt_with_ctx(ctx),
                    substs.fmt_with_ctx_split_trait_refs(ctx)
                )
            }
            Ty::Arrow(inputs, box output) => {
                let inputs = inputs
                    .iter()
                    .map(|x| x.fmt_with_ctx(ctx))
                    .collect::<Vec<String>>()
                    .join(", ");
                if output.is_unit() {
                    format!("fn({inputs})")
                } else {
                    let output = output.fmt_with_ctx(ctx);
                    format!("fn({inputs}) -> {output}")
                }
            }
        }
    }

    /// Return true if the type is Box
    pub fn is_box(&self) -> bool {
        match self {
            Ty::Adt(TypeId::Assumed(AssumedTy::Box), generics) => {
                assert!(generics.regions.is_empty());
                assert!(generics.types.len() == 1);
                assert!(generics.const_generics.is_empty());
                true
            }
            _ => false,
        }
    }

    pub fn as_box(&self) -> Option<&Ty<R>> {
        match self {
            Ty::Adt(TypeId::Assumed(AssumedTy::Box), generics) => {
                assert!(generics.regions.is_empty());
                assert!(generics.types.len() == 1);
                assert!(generics.const_generics.is_empty());
                Some(generics.types.get(0).unwrap())
            }
            _ => None,
        }
    }
}

impl<Rid: Clone + Ord + std::hash::Hash> Ty<Region<Rid>> {
    /// Returns `true` if the type contains one of the regions listed
    /// in the set
    /// TODO: reimplement this with visitors
    pub fn contains_region_var(&self, rset: &OrdSet<Rid>) -> bool {
        match self {
            Ty::TypeVar(_) => false,
            Ty::Literal(_) | Ty::Never => false,
            Ty::Ref(r, ty, _) => r.contains_var(rset) || ty.contains_region_var(rset),
            Ty::RawPtr(ty, _) => ty.contains_region_var(rset),
            Ty::TraitType(_, generics, _) | Ty::Adt(_, generics) => {
                // For the trait type case: we are checking the projected type,
                // so we don't need to explore the trait ref
                generics.regions.iter().any(|r| {
                    r.contains_var(rset)
                        || generics.types.iter().any(|x| x.contains_region_var(rset))
                })
            }
            Ty::Arrow(inputs, box output) => {
                inputs.iter().any(|x| x.contains_region_var(rset))
                    || output.contains_region_var(rset)
            }
        }
    }
}

impl<Rid> std::fmt::Display for Region<Rid>
where
    Rid: std::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        match self {
            Region::Static => write!(f, "'static"),
            Region::Var(id) => write!(f, "'_{id}"),
        }
    }
}

impl std::fmt::Display for ErasedRegion {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        write!(f, "'_")
    }
}

impl std::string::ToString for Ty<ErasedRegion> {
    fn to_string(&self) -> String {
        self.fmt_with_ctx(&DummyFormatter {})
    }
}

impl<R: Eq + Clone> TraitRef<R> {
    pub fn substitute<R1: Eq>(
        &self,
        rsubst: &dyn Fn(&R) -> R1,
        tsubst: &dyn Fn(&TypeVarId::Id) -> Ty<R1>,
        cgsubst: &dyn Fn(&ConstGenericVarId::Id) -> ConstGeneric,
    ) -> TraitRef<R1> {
        let generics = self.generics.substitute(rsubst, tsubst, cgsubst);
        let trait_decl_ref = self.trait_decl_ref.substitute(rsubst, tsubst, cgsubst);
        TraitRef {
            trait_id: self.trait_id.clone(),
            generics,
            trait_decl_ref,
        }
    }
}

impl<R: Eq + Clone> TraitDeclRef<R> {
    pub fn substitute<R1: Eq>(
        &self,
        rsubst: &dyn Fn(&R) -> R1,
        tsubst: &dyn Fn(&TypeVarId::Id) -> Ty<R1>,
        cgsubst: &dyn Fn(&ConstGenericVarId::Id) -> ConstGeneric,
    ) -> TraitDeclRef<R1> {
        let generics = self.generics.substitute(rsubst, tsubst, cgsubst);
        TraitDeclRef {
            trait_id: self.trait_id,
            generics,
        }
    }
}

impl<R: Eq + Clone> GenericArgs<R> {
    pub fn substitute<R1: Eq>(
        &self,
        rsubst: &dyn Fn(&R) -> R1,
        tsubst: &dyn Fn(&TypeVarId::Id) -> Ty<R1>,
        cgsubst: &dyn Fn(&ConstGenericVarId::Id) -> ConstGeneric,
    ) -> GenericArgs<R1> {
        let GenericArgs {
            regions,
            types,
            const_generics,
            trait_refs,
        } = self;
        let regions = Ty::substitute_regions(regions, rsubst);
        let types = types
            .iter()
            .map(|ty| ty.substitute(rsubst, tsubst, cgsubst))
            .collect();
        let const_generics = const_generics
            .iter()
            .map(|cg| cg.substitute(cgsubst))
            .collect();
        let trait_refs = trait_refs
            .iter()
            .map(|x| x.substitute(rsubst, tsubst, cgsubst))
            .collect();
        GenericArgs {
            regions,
            types,
            const_generics,
            trait_refs,
        }
    }
}

impl<R: Eq + Clone> Ty<R> {
    pub fn substitute<R1: Eq>(
        &self,
        rsubst: &dyn Fn(&R) -> R1,
        tsubst: &dyn Fn(&TypeVarId::Id) -> Ty<R1>,
        cgsubst: &dyn Fn(&ConstGenericVarId::Id) -> ConstGeneric,
    ) -> Ty<R1> {
        match self {
            Ty::Adt(id, args) => {
                let args = args.substitute(rsubst, tsubst, cgsubst);
                Ty::Adt(id.clone(), args)
            }
            Ty::TypeVar(id) => tsubst(id),
            Ty::Literal(pty) => Ty::Literal(*pty),
            Ty::Never => Ty::Never,
            Ty::Ref(rid, ty, kind) => Ty::Ref(
                rsubst(rid),
                Box::new(ty.substitute(rsubst, tsubst, cgsubst)),
                *kind,
            ),
            Ty::RawPtr(ty, kind) => {
                Ty::RawPtr(Box::new(ty.substitute(rsubst, tsubst, cgsubst)), *kind)
            }
            Ty::TraitType(trait_ref, args, name) => {
                let trait_ref = trait_ref.substitute(rsubst, tsubst, cgsubst);
                let args = args.substitute(rsubst, tsubst, cgsubst);
                Ty::TraitType(trait_ref, args, name.clone())
            }
            Ty::Arrow(inputs, box output) => {
                let inputs = inputs
                    .iter()
                    .map(|ty| ty.substitute(rsubst, tsubst, cgsubst))
                    .collect();
                let output = output.substitute(rsubst, tsubst, cgsubst);
                Ty::Arrow(inputs, Box::new(output))
            }
        }
    }

    fn substitute_regions<R1>(regions: &Vec<R>, rsubst: &dyn Fn(&R) -> R1) -> Vec<R1> {
        Vec::from_iter(regions.iter().map(|rid| rsubst(rid)))
    }

    /// Substitute the type parameters
    // TODO: tsubst and cgsubst should be closures instead of hashmaps
    pub fn substitute_types(&self, subst: &TypeSubst<R>, cgsubst: &ConstGenericSubst) -> Self {
        self.substitute(
            &|r| r.clone(),
            &|tid| subst.get(tid).unwrap().clone(),
            &|cgid| cgsubst.get(cgid).unwrap().clone(),
        )
    }

    /// Erase the regions
    pub fn erase_regions(&self) -> ETy {
        self.substitute(
            &|_| ErasedRegion::Erased,
            &|tid| Ty::TypeVar(*tid),
            &|cgid| ConstGeneric::Var(*cgid),
        )
    }

    /// Erase the regions and substitute the types at the same time
    pub fn erase_regions_substitute_types(
        &self,
        subst: &TypeSubst<ErasedRegion>,
        cgsubst: &ConstGenericSubst,
    ) -> ETy {
        self.substitute(
            &|_| ErasedRegion::Erased,
            &|tid| subst.get(tid).unwrap().clone(),
            &|cgid| cgsubst.get(cgid).unwrap().clone(),
        )
    }

    /// Returns `true` if the type contains some region or type variables
    /// TODO: reimplement this with visitors
    pub fn contains_variables(&self) -> bool {
        match self {
            Ty::TypeVar(_) => true,
            Ty::Literal(_) | Ty::Never => false,
            Ty::Ref(_, _, _) => true, // Always contains a region identifier
            Ty::RawPtr(ty, _) => ty.contains_variables(),
            Ty::TraitType(_, args, _) | Ty::Adt(_, args) => {
                // For the trait type case: we are checking the projected type,
                // so we don't need to explore the trait ref
                !args.regions.is_empty() || args.types.iter().any(|x| x.contains_variables())
            }
            Ty::Arrow(inputs, box output) => {
                inputs.iter().any(|ty| ty.contains_variables()) || output.contains_variables()
            }
        }
    }

    /// Returns `true` if the type contains some regions
    /// TODO: reimplement this with visitors
    pub fn contains_regions(&self) -> bool {
        match self {
            Ty::TypeVar(_) => false,
            Ty::Literal(_) | Ty::Never => false,
            Ty::Ref(_, _, _) => true,
            Ty::RawPtr(ty, _) => ty.contains_regions(),
            Ty::TraitType(_, args, _) | Ty::Adt(_, args) => {
                // For the trait type case: we are checking the projected type,
                // so we don't need to explore the trait ref
                !args.regions.is_empty() || args.types.iter().any(|x| x.contains_regions())
            }
            Ty::Arrow(inputs, box output) => {
                inputs.iter().any(|ty| ty.contains_regions()) || output.contains_regions()
            }
        }
    }
}

impl RTy {
    /// Substitute the regions and type parameters
    pub fn substitute_regions_types(
        &self,
        rsubst: &RegionSubst<Region<RegionVarId::Id>>,
        tsubst: &TypeSubst<Region<RegionVarId::Id>>,
    ) -> Self {
        self.substitute(
            &|rid| match rid {
                Region::Static => Region::Static,
                Region::Var(rid) => *rsubst.get(rid).unwrap(),
            },
            &|tid| tsubst.get(tid).unwrap().clone(),
            &|cgid| ConstGeneric::Var(*cgid),
        )
    }
}

impl ETy {
    /// Convert an `ETy` to an `Ty<R>` provided there are no (erased) regions
    /// in the type.
    pub fn to_rty<R: Eq>(&self) -> Ty<R> {
        self.substitute(
            &|_| panic!("Unexpected region"),
            &|tid| Ty::TypeVar(*tid),
            &|cgid| ConstGeneric::Var(*cgid),
        )
    }
}

pub fn make_subst<'a, T1, T2: 'a, I1: Iterator<Item = T1>, I2: Iterator<Item = &'a T2>>(
    keys: I1,
    values: I2,
) -> HashMap<T1, T2>
where
    T1: std::hash::Hash + Eq + Clone + Copy,
    T2: Clone,
{
    // We don't need to do this, but we want to check the lengths
    let keys: Vec<T1> = keys.collect();
    let values: Vec<T2> = values.cloned().collect();
    assert!(
        keys.len() == values.len(),
        "keys and values don't have the same length"
    );

    let mut res: HashMap<T1, T2> = HashMap::new();
    keys.iter().zip(values.into_iter()).for_each(|(p, ty)| {
        let _ = res.insert(*p, ty);
    });

    res
}

pub fn make_type_subst<
    'a,
    R: 'a + Eq,
    I1: Iterator<Item = TypeVarId::Id>,
    I2: Iterator<Item = &'a Ty<R>>,
>(
    params: I1,
    types: I2,
) -> TypeSubst<R>
where
    R: Clone,
{
    make_subst(params, types)
}

pub fn make_region_subst<
    'a,
    R: 'a + Eq,
    I1: Iterator<Item = RegionVarId::Id>,
    I2: Iterator<Item = &'a R>,
>(
    keys: I1,
    values: I2,
) -> RegionSubst<R>
where
    R: Clone,
{
    make_subst(keys, values)
}

pub fn make_cg_subst<
    'a,
    I1: Iterator<Item = ConstGenericVarId::Id>,
    I2: Iterator<Item = &'a ConstGeneric>,
>(
    keys: I1,
    values: I2,
) -> ConstGenericSubst {
    make_subst(keys, values)
}

impl Formatter<TypeVarId::Id> for TypeDecl {
    fn format_object(&self, id: TypeVarId::Id) -> String {
        let var = self.generics.types.get(id).unwrap();
        var.to_string()
    }
}

impl Formatter<RegionVarId::Id> for TypeDecl {
    fn format_object(&self, id: RegionVarId::Id) -> String {
        let var = self.generics.regions.get(id).unwrap();
        var.to_string()
    }
}

impl Formatter<ConstGenericVarId::Id> for TypeDecl {
    fn format_object(&self, id: ConstGenericVarId::Id) -> String {
        let var = self.generics.const_generics.get(id).unwrap();
        var.to_string()
    }
}

impl<Rid: Clone> Formatter<&Region<Rid>> for TypeDecl
where
    TypeDecl: Formatter<Rid>,
{
    fn format_object(&self, r: &Region<Rid>) -> String {
        r.fmt_with_ctx(self)
    }
}

impl Formatter<&ErasedRegion> for TypeDecl {
    fn format_object(&self, _: &ErasedRegion) -> String {
        "'_".to_string()
    }
}

impl Formatter<TypeDeclId::Id> for TypeDecls {
    fn format_object(&self, id: TypeDeclId::Id) -> String {
        // The definition may not be available yet, especially if we print-debug
        // while translating the crate
        match self.get(id) {
            Option::None => id.to_pretty_string(),
            Option::Some(def) => def.name.to_string(),
        }
    }
}

impl<R: Clone + std::cmp::Eq> Ty<R> {
    // TODO: reimplement this with visitors
    pub fn contains_never(&self) -> bool {
        match self {
            Ty::Never => true,
            Ty::TraitType(_, args, _) | Ty::Adt(_, args) => {
                // For the trait type case: we are checking the projected type,
                // so we don't need to explore the trait ref
                args.types.iter().any(|ty| ty.contains_never())
            }
            Ty::TypeVar(_) | Ty::Literal(_) => false,
            Ty::Ref(_, ty, _) | Ty::RawPtr(ty, _) => ty.contains_never(),
            Ty::Arrow(inputs, box output) => {
                inputs.iter().any(|ty| ty.contains_never()) || output.contains_never()
            }
        }
    }
}

pub struct TySubst<R> {
    pub ignore_regions: bool,
    /// This map is from regions to regions, not from region ids to regions.
    /// In case the regions are not erased, we must be careful with the
    /// static region.
    pub regions_map: HashMap<R, R>,
    pub type_vars_map: HashMap<TypeVarId::Id, Ty<R>>,
    pub const_generics_map: HashMap<ConstGenericVarId::Id, ConstGeneric>,
}

macro_rules! check_ok_return {
    ( $x:expr ) => {{
        if $x {
            return Ok(());
        } else {
            return Err(());
        }
    }};
}

macro_rules! check_ok {
    ( $x:expr ) => {{
        if !$x {
            return Err(());
        }
    }};
}

impl<R: Clone + Eq + std::hash::Hash> TySubst<R> {
    fn new() -> Self {
        TySubst {
            ignore_regions: false,
            regions_map: HashMap::new(),
            type_vars_map: HashMap::new(),
            const_generics_map: HashMap::new(),
        }
    }

    fn unify_regions(&mut self, src: &R, tgt: &R) -> Result<(), ()> {
        use Result::*;
        match self.regions_map.get(src) {
            None => {
                check_ok_return!(self.regions_map.insert(src.clone(), tgt.clone()).is_none());
            }
            Some(src) => {
                check_ok_return!(src == tgt);
            }
        }
    }

    fn unify_const_generics(&mut self, src: &ConstGeneric, tgt: &ConstGeneric) -> Result<(), ()> {
        use ConstGeneric::*;
        use Result::*;
        if let Var(v) = src {
            check_ok_return!(self.const_generics_map.insert(*v, tgt.clone()).is_none());
        }
        match (src, tgt) {
            (Global(src), Global(tgt)) => {
                check_ok_return!(src == tgt);
            }
            (Value(src), Value(tgt)) => {
                check_ok_return!(src == tgt);
            }
            _ => Err(()),
        }
    }

    fn unify_types(&mut self, src: &Ty<R>, tgt: &Ty<R>) -> Result<(), ()> {
        use Result::*;
        use Ty::*;

        if let TypeVar(v) = src {
            check_ok_return!(self.type_vars_map.insert(*v, tgt.clone()).is_none());
        }

        match (src, tgt) {
            (Adt(src_id, src_args), Adt(tgt_id, tgt_args)) => {
                check_ok!(src_id == tgt_id);
                self.unify_args(src_args, tgt_args)
            }
            (Literal(src), Literal(tgt)) => {
                check_ok_return!(src == tgt);
            }
            (Never, Never) => Ok(()),
            (Ref(src_r, box src_ty, src_kind), Ref(tgt_r, box tgt_ty, tgt_kind)) => {
                if !self.ignore_regions {
                    self.unify_regions(src_r, tgt_r)?;
                }
                self.unify_types(src_ty, tgt_ty)?;
                check_ok_return!(src_kind == tgt_kind);
            }
            (RawPtr(box src_ty, src_kind), RawPtr(box tgt_ty, tgt_kind)) => {
                self.unify_types(src_ty, tgt_ty)?;
                check_ok_return!(src_kind == tgt_kind);
            }
            _ => Err(()),
        }
    }

    fn unify_regions_lists(&mut self, src: &[R], tgt: &[R]) -> Result<(), ()> {
        check_ok!(src.len() == tgt.len());
        for (src, tgt) in src.iter().zip(tgt.iter()) {
            self.unify_regions(src, tgt)?;
        }
        Ok(())
    }

    fn unify_const_generics_lists(
        &mut self,
        src: &[ConstGeneric],
        tgt: &[ConstGeneric],
    ) -> Result<(), ()> {
        check_ok!(src.len() == tgt.len());
        for (src, tgt) in src.iter().zip(tgt.iter()) {
            self.unify_const_generics(src, tgt)?;
        }
        Ok(())
    }

    fn unify_types_lists(&mut self, src: &[Ty<R>], tgt: &[Ty<R>]) -> Result<(), ()> {
        check_ok!(src.len() == tgt.len());
        for (src, tgt) in src.iter().zip(tgt.iter()) {
            self.unify_types(src, tgt)?;
        }
        Ok(())
    }

    fn unify_args(
        &mut self,
        src: &crate::gast::GenericArgs<R>,
        tgt: &crate::gast::GenericArgs<R>,
    ) -> Result<(), ()> {
        if !self.ignore_regions {
            self.unify_regions_lists(&src.regions, &tgt.regions)?;
        }
        self.unify_types_lists(&src.types, &tgt.types)?;
        self.unify_const_generics_lists(&src.const_generics, &tgt.const_generics)?;
        Ok(())
    }
}

impl TySubst<ErasedRegion> {
    pub fn unify_eargs(
        fixed_type_vars: impl std::iter::Iterator<Item = TypeVarId::Id>,
        fixed_const_generic_vars: impl std::iter::Iterator<Item = ConstGenericVarId::Id>,
        src: &crate::gast::EGenericArgs,
        tgt: &crate::gast::EGenericArgs,
    ) -> Result<Self, ()> {
        let mut s = TySubst::new();
        for v in fixed_type_vars {
            s.type_vars_map.insert(v, Ty::TypeVar(v));
        }
        for v in fixed_const_generic_vars {
            s.const_generics_map.insert(v, ConstGeneric::Var(v));
        }

        s.ignore_regions = true;
        s.unify_args(src, tgt)?;
        Ok(s)
    }
}

/// Visitor to replace the [TraitInstanceId::SelfId] inside a type
struct TraitInstanceIdSelfReplacer {
    new_id: TraitInstanceId,
}

impl MutTypeVisitor for TraitInstanceIdSelfReplacer {
    fn visit_trait_instance_id(&mut self, id: &mut TraitInstanceId) {
        match id {
            TraitInstanceId::SelfId => *id = self.new_id.clone(),
            TraitInstanceId::ParentClause(box id, _, _)
            | TraitInstanceId::ItemClause(box id, _, _, _) => self.visit_trait_instance_id(id),
            TraitInstanceId::TraitImpl(_)
            | TraitInstanceId::Clause(_)
            | TraitInstanceId::BuiltinOrAuto(_)
            | TraitInstanceId::FnPointer(_)
            | TraitInstanceId::Unknown(_) => (),
        }
    }
}

impl<R> Ty<R> {
    pub(crate) fn replace_self_trait_instance_id(mut self, new_id: TraitInstanceId) -> Self {
        let mut visitor = TraitInstanceIdSelfReplacer { new_id };
        visitor.visit_ty(&mut self);
        self
    }
}

// Derive two implementations at once: one which uses shared borrows, and one
// which uses mutable borrows.
// Generates the traits: `SharedTypeVisitor` and `MutTypeVisitor`.
make_generic_in_borrows! {

// TODO: we should use traits with default implementations to allow overriding
// the default behavior (that would also prevent problems with naming collisions)
pub trait TypeVisitor {
    fn visit_ty<R>(&mut self, ty: &Ty<R>) {
        self.default_visit_ty(ty)
    }

    fn default_visit_ty<R>(&mut self, ty: &Ty<R>) {
        use Ty::*;
        match ty {
            Adt(id, args) => self.visit_ty_adt(id, args),
            TypeVar(vid) => self.visit_ty_type_var(vid),
            Literal(lit) => self.visit_ty_literal(lit),
            Never => self.visit_ty_never(),
            Ref(r, ty, rk) => self.visit_ty_ref(r, ty, rk),
            RawPtr(ty, rk) => self.visit_ty_raw_ptr(ty, rk),
            TraitType(trait_ref, generics, _name) => {
                self.visit_trait_ref(trait_ref);
                self.visit_generic_args(generics);
            }
            Arrow(inputs, box output) => self.visit_arrow(inputs, output),
        }
    }

    fn visit_arrow<R>(&mut self, inputs: &Vec<Ty<R>>, output: &Ty<R>) {
        for ty in inputs {
            self.visit_ty(ty);
        }
        self.visit_ty(output);
    }

    fn visit_ty_adt<R>(
        &mut self,
        id: &TypeId,
        args: &GenericArgs<R>,
    ) {
        self.visit_type_id(id);
        self.visit_generic_args(args);
    }

    fn visit_ty_type_var(&mut self, vid: &TypeVarId::Id) {
        self.visit_type_var_id(vid);
    }

    fn visit_ty_literal(&mut self, ty: &LiteralTy) {}

    fn visit_ty_never(&mut self) {}

    fn visit_ty_ref<R>(&mut self, _r: &R, ty: &Box<Ty<R>>, _rk: &RefKind) {
        // We ignore the region
        self.visit_ty(ty);
    }

    fn visit_ty_raw_ptr<R>(&mut self, ty: &Box<Ty<R>>, _rk: &RefKind) {
        // We ignore the region
        self.visit_ty(ty);
    }

    fn visit_type_id(&mut self, id: &TypeId) {
        use TypeId::*;
        match id {
            Adt(id) => self.visit_type_decl_id(id),
            Tuple => (),
            Assumed(aty) => self.visit_assumed_ty(aty),
        }
    }

    fn visit_type_decl_id(&mut self, _: &TypeDeclId::Id) {}

    fn visit_assumed_ty(&mut self, _: &AssumedTy) {}

    fn visit_const_generic(&mut self, cg: &ConstGeneric) {
        use ConstGeneric::*;
        match cg {
            Global(id) => self.visit_global_decl_id(id),
            Var(id) => self.visit_const_generic_var_id(id),
            Value(lit) => self.visit_literal(lit),
        }
    }

    fn visit_type_var(&mut self, ty: &TypeVar) {
        self.visit_type_var_id(&ty.index);
        // Ignoring the name
    }

    fn visit_const_generic_var(&mut self, cg: &ConstGenericVar) {
        self.visit_const_generic_var_id(&cg.index);
        // Ignoring the name and type
    }

    fn visit_global_decl_id(&mut self, _: &GlobalDeclId::Id) {}
    fn visit_type_var_id(&mut self, _: &TypeVarId::Id) {}
    fn visit_const_generic_var_id(&mut self, _: &ConstGenericVarId::Id) {}

    fn visit_literal(&mut self, _: &Literal) {}

    fn visit_trait_ref<R>(&mut self, tr: &TraitRef<R>) {
        let TraitRef {
            trait_id,
            generics,
            trait_decl_ref,
        } = tr;
        self.visit_trait_instance_id(trait_id);
        self.visit_generic_args(generics);
        self.visit_trait_decl_ref(trait_decl_ref);
    }

    fn visit_trait_decl_ref<R>(&mut self, tr: &TraitDeclRef<R>) {
        let TraitDeclRef {
            trait_id,
            generics,
        } = tr;
        self.visit_trait_decl_id(trait_id);
        self.visit_generic_args(generics);
    }

    fn visit_trait_decl_id(&mut self, _: &TraitDeclId::Id) {}
    fn visit_trait_impl_id(&mut self, _: &TraitImplId::Id) {}
    fn visit_trait_clause_id(&mut self, _: &TraitClauseId::Id) {}

    fn visit_trait_instance_id(&mut self, id: &TraitInstanceId) {
        match id {
            TraitInstanceId::SelfId => (),
            TraitInstanceId::TraitImpl(id) => self.visit_trait_impl_id(id),
            TraitInstanceId::BuiltinOrAuto(id) => self.visit_trait_decl_id(id),
            TraitInstanceId::Clause(id) => self.visit_trait_clause_id(id),
            TraitInstanceId::ParentClause(box id, decl_id, clause_id) => {
                self.visit_trait_instance_id(id);
                self.visit_trait_decl_id(decl_id);
                self.visit_trait_clause_id(clause_id)
            },
            TraitInstanceId::ItemClause(box id, decl_id, _name, clause_id) => {
                self.visit_trait_instance_id(id);
                self.visit_trait_decl_id(decl_id);
                self.visit_trait_clause_id(clause_id)
            },
            TraitInstanceId::FnPointer(box ty) => {
                self.visit_ty(ty);
            }
            TraitInstanceId::Unknown(_) => (),
        }
    }

    fn visit_generic_args<R>(&mut self, g: &GenericArgs<R>) {
        // We ignore the regions - TODO: we shouldn't
        for t in &g.types {
            self.visit_ty(t);
        }
        for cg in &g.const_generics {
            self.visit_const_generic(cg);
        }
        for t in &g.trait_refs {
            self.visit_trait_ref(t);
        }
    }

    fn visit_generic_params(&mut self, g: &GenericParams) {
        // We ignore the regions - TODO: we shouldn't
        for t in g.types.iter() {
            self.visit_type_var(t);
        }
        for cg in g.const_generics.iter() {
            self.visit_const_generic_var(cg);
        }
        for t in g.trait_clauses.iter() {
            self.visit_trait_clause(t);
        }
    }

    fn visit_trait_clause(&mut self, c: &TraitClause) {
        let TraitClause { clause_id, meta: _, trait_id, generics } = c;
        self.visit_trait_clause_id(clause_id);
        self.visit_trait_decl_id(trait_id);
        self.visit_generic_args(generics);
    }

    fn visit_predicates(&mut self, preds: &Predicates) {
        // We don't need to visit the regions - TODO: we should
        let Predicates {
            regions_outlive: _,
            types_outlive,
            trait_type_constraints,
        } = preds;
        for p in types_outlive {
            self.visit_ty(&p.0);
        }
        for TraitTypeConstraint {
            trait_ref,
            generics,
            type_name: _,
            ty,
        } in trait_type_constraints
        {
            self.visit_trait_ref(trait_ref);
            self.visit_generic_args(generics);
            self.visit_ty(ty);
        }
    }

    fn visit_fun_sig(&mut self, sig: &FunSig) {
        let FunSig {
            is_unsafe : _,
            generics,
            preds,
            parent_params_info: _,
            inputs,
            output,
            regions_hierarchy: _,
        } = sig;

        self.visit_generic_params(generics);
        self.visit_predicates(preds);
        for ty in inputs { self.visit_ty(ty); }
        self.visit_ty(output);
    }
}

} // make_generic_in_borrows

impl FunSig {
    pub fn fmt_with_ctx<'a, T>(&'a self, ctx: &T) -> String
    where
        T: TypeFormatter<'a, Region<RegionVarId::Id>>,
    {
        // Unsafe keyword
        let unsafe_kw = if self.is_unsafe {
            "unsafe ".to_string()
        } else {
            "".to_string()
        };

        // Generic parameters
        let (params, trait_clauses) = self.generics.fmt_with_ctx_with_trait_clauses(ctx);

        // Arguments
        let mut args: Vec<String> = Vec::new();
        for ty in &self.inputs {
            args.push(ty.fmt_with_ctx(ctx).to_string());
        }
        let args = args.join(", ");

        // Return type
        let ret_ty = &self.output;
        let ret_ty = if ret_ty.is_unit() {
            "".to_string()
        } else {
            format!(" -> {}", ret_ty.fmt_with_ctx(ctx))
        };

        // Clauses
        let clauses = fmt_where_clauses_with_ctx(
            ctx,
            "",
            &self.parent_params_info,
            trait_clauses,
            &self.preds,
        );

        // Put everything together
        format!("{unsafe_kw}fn{params}({args}){ret_ty}{clauses}",)
    }
}
