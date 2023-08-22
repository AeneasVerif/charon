//! This file groups everything which is linked to implementations about [crate::types]
#![allow(dead_code)]

use crate::assumed::get_name_from_type_id;
use crate::formatter::Formatter;
use crate::types::*;
use crate::ullbc_ast::{GlobalDeclId, TraitId};
use crate::values::Literal;
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

impl<Rid: Copy + Eq> Region<Rid> {
    pub fn fmt_with_ctx<T>(&self, ctx: &T) -> String
    where
        T: Formatter<Rid>,
    {
        match self {
            Region::Static => "'static".to_string(),
            Region::Var(id) => ctx.format_object(*id),
        }
    }
}

impl<Rid1: Copy + Eq + Ord + std::hash::Hash> Region<Rid1> {
    pub fn substitute<Rid2: Copy + Eq>(
        &self,
        rsubst: &HashMap<Rid1, Region<Rid2>>,
    ) -> Region<Rid2> {
        match self {
            Region::Static => Region::Static,
            Region::Var(id) => *rsubst.get(id).unwrap(),
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
            self.region_params.iter().map(|x| x.index),
            inst_regions.iter(),
        );
        let ty_subst = make_type_subst(self.type_params.iter().map(|x| x.index), inst_types.iter());

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
        let ty_subst = make_type_subst(self.type_params.iter().map(|x| x.index), inst_types.iter());
        let cg_subst = make_cg_subst(
            self.const_generic_params.iter().map(|x| x.index),
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
        let ty_subst = make_type_subst(self.type_params.iter().map(|x| x.index), inst_types.iter());
        let cg_subst = make_cg_subst(
            self.const_generic_params.iter().map(|x| x.index),
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
        T: Formatter<TypeVarId::Id>
            + Formatter<RegionVarId::Id>
            + Formatter<&'a Region<RegionVarId::Id>>
            + Formatter<TypeDeclId::Id>
            + Formatter<GlobalDeclId::Id>
            + Formatter<ConstGenericVarId::Id>,
    {
        let params = TypeDecl::fmt_params(&self.region_params, &self.type_params);
        match &self.kind {
            TypeDeclKind::Struct(fields) => {
                if !fields.is_empty() {
                    let fields: Vec<String> = fields
                        .iter()
                        .map(|f| format!("\n  {}", f.fmt_with_ctx(ctx)))
                        .collect();
                    let fields = fields.join(",");
                    format!("struct {}{} = {{{}\n}}", self.name, params, fields)
                } else {
                    format!("struct {}{} = {{}}", self.name, params)
                }
            }
            TypeDeclKind::Enum(variants) => {
                let variants: Vec<String> = variants
                    .iter()
                    .map(|v| format!("|  {}", v.fmt_with_ctx(ctx)))
                    .collect();
                let variants = variants.join("\n");
                format!("enum {}{} =\n{}\n", self.name, params, variants)
            }
            TypeDeclKind::Opaque => format!("opaque type {}{}", self.name, params),
        }
    }

    fn fmt_params(
        region_params: &RegionVarId::Vector<RegionVar>,
        type_params: &TypeVarId::Vector<TypeVar>,
    ) -> String {
        if region_params.len() + type_params.len() > 0 {
            let regions = region_params.iter().map(|r| r.to_string());
            let type_params = type_params.iter().map(|p| p.to_string());
            let params: Vec<String> = regions.chain(type_params).collect();
            format!("<{}>", params.join(", "))
        } else {
            "".to_string()
        }
    }
}

impl std::string::ToString for TypeDecl {
    fn to_string(&self) -> String {
        self.fmt_with_ctx(&IncompleteFormatter { def: self })
    }
}

impl Variant {
    pub fn fmt_with_ctx<'a, T>(&'a self, ctx: &'a T) -> String
    where
        T: Formatter<TypeVarId::Id>
            + Formatter<RegionVarId::Id>
            + Formatter<&'a Region<RegionVarId::Id>>
            + Formatter<TypeDeclId::Id>
            + Formatter<ConstGenericVarId::Id>
            + Formatter<GlobalDeclId::Id>,
    {
        let fields: Vec<String> = self.fields.iter().map(|f| f.fmt_with_ctx(ctx)).collect();
        let fields = fields.join(", ");
        format!("{}({})", self.name, fields)
    }
}

impl Field {
    pub fn fmt_with_ctx<'a, T>(&'a self, ctx: &'a T) -> String
    where
        T: Formatter<TypeVarId::Id>
            + Formatter<RegionVarId::Id>
            + Formatter<&'a Region<RegionVarId::Id>>
            + Formatter<TypeDeclId::Id>
            + Formatter<ConstGenericVarId::Id>
            + Formatter<GlobalDeclId::Id>,
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

impl TraitId::Id {
    pub fn to_pretty_string(&self) -> String {
        format!("@Trait{self}")
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

impl<R> Ty<R>
where
    R: Clone + Eq,
{
    /// Return true if it is actually unit (i.e.: 0-tuple)
    pub fn is_unit(&self) -> bool {
        match self {
            Ty::Adt(TypeId::Tuple, regions, tys, cgs) => {
                assert!(regions.is_empty());
                assert!(cgs.is_empty());
                tys.is_empty()
            }
            _ => false,
        }
    }

    /// Return the unit type
    pub fn mk_unit() -> Ty<R> {
        Ty::Adt(TypeId::Tuple, Vec::new(), Vec::new(), Vec::new())
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
        T: Formatter<ConstGenericVarId::Id>
            + Formatter<TypeVarId::Id>
            + Formatter<TypeDeclId::Id>
            + Formatter<GlobalDeclId::Id>
            + Formatter<&'a R>,
    {
        match self {
            Ty::Adt(id, regions, inst_types, cgs) => {
                let adt_ident = id.fmt_with_ctx(ctx);

                let num_params = regions.len() + inst_types.len();

                let regions: Vec<String> = regions.iter().map(|r| ctx.format_object(r)).collect();
                let mut types: Vec<String> =
                    inst_types.iter().map(|ty| ty.fmt_with_ctx(ctx)).collect();
                let mut cgs: Vec<String> = cgs.iter().map(|cg| cg.fmt_with_ctx(ctx)).collect();
                let mut all_params = regions;
                all_params.append(&mut types);
                all_params.append(&mut cgs);
                let all_params = all_params.join(", ");

                if id.is_tuple() {
                    format!("({all_params})")
                } else if num_params > 0 {
                    format!("{adt_ident}<{all_params}>")
                } else {
                    adt_ident
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
        }
    }

    /// Return true if the type is Box
    pub fn is_box(&self) -> bool {
        match self {
            Ty::Adt(TypeId::Assumed(AssumedTy::Box), regions, tys, cgs) => {
                assert!(regions.is_empty());
                assert!(tys.len() == 1);
                assert!(cgs.is_empty());
                true
            }
            _ => false,
        }
    }

    pub fn as_box(&self) -> Option<&Ty<R>> {
        match self {
            Ty::Adt(TypeId::Assumed(AssumedTy::Box), regions, tys, cgs) => {
                assert!(regions.is_empty());
                assert!(tys.len() == 1);
                assert!(cgs.is_empty());
                Some(tys.get(0).unwrap())
            }
            _ => None,
        }
    }

    /// Return true if the type is Vec
    pub fn is_vec(&self) -> bool {
        match self {
            Ty::Adt(TypeId::Assumed(AssumedTy::Vec), regions, tys, cgs) => {
                assert!(regions.is_empty());
                assert!(tys.len() == 1);
                assert!(cgs.is_empty());
                true
            }
            _ => false,
        }
    }

    pub fn as_vec(&self) -> Option<&Ty<R>> {
        match self {
            Ty::Adt(TypeId::Assumed(AssumedTy::Vec), regions, tys, cgs) => {
                assert!(regions.is_empty());
                assert!(tys.len() == 1);
                assert!(cgs.is_empty());
                Some(tys.get(0).unwrap())
            }
            _ => None,
        }
    }
}

impl<Rid: Copy + Eq + Ord + std::hash::Hash> Ty<Region<Rid>> {
    /// Returns `true` if the type contains one of the regions listed
    /// in the set
    pub fn contains_region_var(&self, rset: &OrdSet<Rid>) -> bool {
        match self {
            Ty::TypeVar(_) => false,
            Ty::Literal(_) | Ty::Never => false,
            Ty::Ref(r, ty, _) => r.contains_var(rset) || ty.contains_region_var(rset),
            Ty::RawPtr(ty, _) => ty.contains_region_var(rset),
            Ty::Adt(_, regions, tys, _) => regions
                .iter()
                .any(|r| r.contains_var(rset) || tys.iter().any(|x| x.contains_region_var(rset))),
        }
    }
}

impl<Rid: Copy + Eq> std::fmt::Display for Region<Rid>
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

pub struct IncompleteFormatter<'a> {
    def: &'a TypeDecl,
}

impl<'a> Formatter<TypeVarId::Id> for IncompleteFormatter<'a> {
    fn format_object(&self, id: TypeVarId::Id) -> String {
        self.def.format_object(id)
    }
}

impl<'a> Formatter<GlobalDeclId::Id> for IncompleteFormatter<'a> {
    fn format_object(&self, id: GlobalDeclId::Id) -> String {
        id.to_pretty_string()
    }
}

impl<'a, 'b, Rid: Copy + Eq> Formatter<&'b Region<Rid>> for IncompleteFormatter<'a>
where
    TypeDecl: Formatter<&'b Region<Rid>>,
{
    fn format_object(&self, r: &'b Region<Rid>) -> String {
        self.def.format_object(r)
    }
}

impl<'a, 'b> Formatter<&'b ErasedRegion> for IncompleteFormatter<'a> {
    fn format_object(&self, r: &'b ErasedRegion) -> String {
        self.def.format_object(r)
    }
}

impl<'a> Formatter<RegionVarId::Id> for IncompleteFormatter<'a> {
    fn format_object(&self, id: RegionVarId::Id) -> String {
        self.def.format_object(id)
    }
}

impl<'a> Formatter<TypeDeclId::Id> for IncompleteFormatter<'a> {
    fn format_object(&self, id: TypeDeclId::Id) -> String {
        // For type def ids, we simply print the def id because
        // we lack context
        id.to_pretty_string()
    }
}

impl<'a> Formatter<ConstGenericVarId::Id> for IncompleteFormatter<'a> {
    fn format_object(&self, id: ConstGenericVarId::Id) -> String {
        self.def.format_object(id)
    }
}

pub struct DummyFormatter {}

impl Formatter<TypeVarId::Id> for DummyFormatter {
    fn format_object(&self, id: TypeVarId::Id) -> String {
        id.to_pretty_string()
    }
}

impl<Rid: Copy + Eq> Formatter<&Region<Rid>> for DummyFormatter
where
    DummyFormatter: Formatter<Rid>,
{
    fn format_object(&self, r: &Region<Rid>) -> String {
        r.fmt_with_ctx(self)
    }
}

impl Formatter<&ErasedRegion> for DummyFormatter {
    fn format_object(&self, _: &ErasedRegion) -> String {
        "'_".to_string()
    }
}

impl Formatter<RegionVarId::Id> for DummyFormatter {
    fn format_object(&self, id: RegionVarId::Id) -> String {
        id.to_pretty_string()
    }
}

impl Formatter<TypeDeclId::Id> for DummyFormatter {
    fn format_object(&self, id: TypeDeclId::Id) -> String {
        id.to_pretty_string()
    }
}

impl Formatter<ConstGenericVarId::Id> for DummyFormatter {
    fn format_object(&self, id: ConstGenericVarId::Id) -> String {
        id.to_pretty_string()
    }
}

impl Formatter<GlobalDeclId::Id> for DummyFormatter {
    fn format_object(&self, id: GlobalDeclId::Id) -> String {
        id.to_pretty_string()
    }
}

impl std::string::ToString for Ty<ErasedRegion> {
    fn to_string(&self) -> String {
        self.fmt_with_ctx(&DummyFormatter {})
    }
}

// TODO: mixing Copy and Clone in the trait requirements below. Update to only use Copy.
impl<R> Ty<R>
where
    R: Copy + Clone + Eq,
{
    pub fn substitute<R1>(
        &self,
        rsubst: &dyn Fn(&R) -> R1,
        tsubst: &dyn Fn(&TypeVarId::Id) -> Ty<R1>,
        cgsubst: &dyn Fn(&ConstGenericVarId::Id) -> ConstGeneric,
    ) -> Ty<R1>
    where
        R1: Clone + Eq,
    {
        match self {
            Ty::Adt(id, regions, tys, cgs) => {
                let nregions = Ty::substitute_regions(regions, rsubst);
                let ntys = tys
                    .iter()
                    .map(|ty| ty.substitute(rsubst, tsubst, cgsubst))
                    .collect();
                let ncgs = cgs.iter().map(|cg| cg.substitute(cgsubst)).collect();
                Ty::Adt(id.clone(), nregions, ntys, ncgs)
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
        }
    }

    fn substitute_regions<R1>(regions: &Vec<R>, rsubst: &dyn Fn(&R) -> R1) -> Vec<R1>
    where
        R1: Clone + Eq,
    {
        Vec::from_iter(regions.iter().map(|rid| rsubst(rid)))
    }

    /// Substitute the type parameters
    // TODO: tsubst and cgsubst should be closures instead of hashmaps
    pub fn substitute_types(&self, subst: &TypeSubst<R>, cgsubst: &ConstGenericSubst) -> Self {
        self.substitute(&|r| *r, &|tid| subst.get(tid).unwrap().clone(), &|cgid| {
            cgsubst.get(cgid).unwrap().clone()
        })
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
    pub fn contains_variables(&self) -> bool {
        match self {
            Ty::TypeVar(_) => true,
            Ty::Literal(_) | Ty::Never => false,
            Ty::Ref(_, _, _) => true, // Always contains a region identifier
            Ty::RawPtr(ty, _) => ty.contains_variables(),
            Ty::Adt(_, regions, tys, _) => {
                !regions.is_empty() || tys.iter().any(|x| x.contains_variables())
            }
        }
    }

    /// Returns `true` if the type contains some regions
    pub fn contains_regions(&self) -> bool {
        match self {
            Ty::TypeVar(_) => false,
            Ty::Literal(_) | Ty::Never => false,
            Ty::Ref(_, _, _) => true,
            Ty::RawPtr(ty, _) => ty.contains_regions(),
            Ty::Adt(_, regions, tys, _) => {
                !regions.is_empty() || tys.iter().any(|x| x.contains_regions())
            }
        }
    }
}

// TODO: mixing Copy and Clone in the trait requirements below. Update to only use Copy.
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
        let var = self.type_params.get(id).unwrap();
        var.to_string()
    }
}

impl Formatter<RegionVarId::Id> for TypeDecl {
    fn format_object(&self, id: RegionVarId::Id) -> String {
        let var = self.region_params.get(id).unwrap();
        var.to_string()
    }
}

impl Formatter<ConstGenericVarId::Id> for TypeDecl {
    fn format_object(&self, id: ConstGenericVarId::Id) -> String {
        let var = self.const_generic_params.get(id).unwrap();
        var.to_string()
    }
}

impl<Rid: Copy + Eq> Formatter<&Region<Rid>> for TypeDecl
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
    pub fn contains_never(&self) -> bool {
        match self {
            Ty::Never => true,
            Ty::Adt(_, _, tys, _) => tys.iter().any(|ty| ty.contains_never()),
            Ty::TypeVar(_) | Ty::Literal(_) => false,
            Ty::Ref(_, ty, _) | Ty::RawPtr(ty, _) => ty.contains_never(),
        }
    }
}

// Derive two implementations at once: one which uses shared borrows, and one
// which uses mutable borrows.
// Generates the traits: `SharedTypeVisitor` and `MutTypeVisitor`.
make_generic_in_borrows! {

// TODO: we should use traits with default implementations to allow overriding
// the default behavior (that would also prevent problems with naming collisions)
pub trait TypeVisitor {
    fn visit_ty<R: Clone + std::cmp::Eq>(&mut self, ty: &Ty<R>) {
        self.default_visit_ty(ty)
    }

    fn default_visit_ty<R: Clone + std::cmp::Eq>(&mut self, ty: &Ty<R>) {
        use Ty::*;
        match ty {
            Adt(id, rl, tys, cgs) => self.visit_ty_adt(id, rl, tys, cgs),
            TypeVar(vid) => self.visit_ty_type_var(vid),
            Literal(lit) => self.visit_ty_literal(lit),
            Never => self.visit_ty_never(),
            Ref(r, ty, rk) => self.visit_ty_ref(r, ty, rk),
            RawPtr(ty, rk) => self.visit_ty_raw_ptr(ty, rk),
        }
    }

    fn visit_ty_adt<R: Clone + std::cmp::Eq>(
        &mut self,
        id: &TypeId,
        rl: &Vec<R>,
        tys: &Vec<Ty<R>>,
        cgs: &Vec<ConstGeneric>,
    ) {
        self.visit_type_id(id);
        // We ignore the regions
        for ty in tys {
            self.visit_ty(ty)
        }
        for cg in cgs {
            self.visit_const_generic(cg);
        }
    }

    fn visit_ty_type_var(&mut self, vid: &TypeVarId::Id) {
        self.visit_type_var_id(vid);
    }

    fn visit_ty_literal(&mut self, ty: &LiteralTy) {}

    fn visit_ty_never(&mut self) {}

    fn visit_ty_ref<R: Clone + std::cmp::Eq>(&mut self, _r: &R, ty: &Box<Ty<R>>, _rk: &RefKind) {
        // We ignore the region
        self.visit_ty(ty);
    }

    fn visit_ty_raw_ptr<R: Clone + std::cmp::Eq>(&mut self, ty: &Box<Ty<R>>, _rk: &RefKind) {
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

    fn visit_global_decl_id(&mut self, _: &GlobalDeclId::Id) {}
    fn visit_type_var_id(&mut self, _: &TypeVarId::Id) {}
    fn visit_const_generic_var_id(&mut self, _: &ConstGenericVarId::Id) {}

    fn visit_literal(&mut self, _: &Literal) {}
}

} // make_generic_in_borrows
