//! This file groups everything which is linked to implementations about [crate::expressions]
#![allow(dead_code)]

use crate::assumed;
use crate::common::*;
use crate::expressions::*;
use crate::formatter::Formatter;
use crate::types::*;
use crate::ullbc_ast::GlobalDeclId;
use crate::values;
use crate::values::*;
use macros::make_generic_in_borrows;
use serde::ser::SerializeStruct;
use serde::ser::SerializeTupleVariant;
use serde::{Serialize, Serializer};

impl Place {
    pub fn new(var_id: VarId::Id) -> Place {
        Place {
            var_id,
            projection: im::Vector::new(),
        }
    }
}

impl Serialize for Place {
    fn serialize<S>(&self, serializer: S) -> std::result::Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut s = serializer.serialize_struct("Place", 2)?;
        s.serialize_field("var_id", &self.var_id)?;
        let projection = VectorSerializer::new(&self.projection);
        s.serialize_field("projection", &projection)?;
        s.end()
    }
}

impl std::fmt::Display for BorrowKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        match self {
            BorrowKind::Shared => write!(f, "Shared"),
            BorrowKind::Mut => write!(f, "Mut"),
            BorrowKind::TwoPhaseMut => write!(f, "TwoPhaseMut"),
            BorrowKind::Shallow => write!(f, "Shallow"),
        }
    }
}

impl std::fmt::Display for UnOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        match self {
            UnOp::Not => write!(f, "~"),
            UnOp::Neg => write!(f, "-"),
            UnOp::Cast(src, tgt) => write!(f, "cast<{src},{tgt}>"),
            UnOp::SliceNew(l) => write!(f, "mk_slice<{:?}>", l),
        }
    }
}

impl std::fmt::Display for BinOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        match self {
            BinOp::BitXor => write!(f, "^"),
            BinOp::BitAnd => write!(f, "&"),
            BinOp::BitOr => write!(f, "|"),
            BinOp::Eq => write!(f, "=="),
            BinOp::Lt => write!(f, "<"),
            BinOp::Le => write!(f, "<="),
            BinOp::Ne => write!(f, "!="),
            BinOp::Ge => write!(f, ">="),
            BinOp::Gt => write!(f, ">"),
            BinOp::Div => write!(f, "/"),
            BinOp::Rem => write!(f, "%"),
            BinOp::Add => write!(f, "+"),
            BinOp::Sub => write!(f, "-"),
            BinOp::Mul => write!(f, "*"),
            BinOp::Shl => write!(f, "<<"),
            BinOp::Shr => write!(f, ">>"),
        }
    }
}

impl Place {
    pub fn fmt_with_ctx<T>(&self, ctx: &T) -> String
    where
        T: Formatter<TypeDeclId::Id>
            + Formatter<GlobalDeclId::Id>
            + Formatter<VarId::Id>
            + Formatter<(TypeDeclId::Id, Option<VariantId::Id>, FieldId::Id)>,
    {
        let mut out = ctx.format_object(self.var_id);

        for p in &self.projection {
            match p {
                ProjectionElem::Deref => {
                    out = format!("*({out})");
                }
                ProjectionElem::DerefBox => {
                    out = format!("deref_box ({out})");
                }
                ProjectionElem::DerefRawPtr => {
                    out = format!("deref_raw_ptr ({out})");
                }
                ProjectionElem::DerefPtrUnique => {
                    out = format!("deref_ptr_unique ({out})");
                }
                ProjectionElem::DerefPtrNonNull => {
                    out = format!("deref_ptr_non_null ({out})");
                }
                ProjectionElem::Field(proj_kind, field_id) => match proj_kind {
                    FieldProjKind::Adt(adt_id, opt_variant_id) => {
                        let field_name = ctx.format_object((*adt_id, *opt_variant_id, *field_id));
                        let downcast = match opt_variant_id {
                            None => "".to_string(),
                            Some(variant_id) => format!(" as variant @{variant_id}"),
                        };
                        out = format!("({out}{downcast}).{field_name}");
                    }
                    FieldProjKind::Tuple(_) => {
                        out = format!("({out}).{field_id}");
                    }
                    FieldProjKind::Option(_) => {
                        out = format!("({out}).{field_id}");
                    }
                },
                ProjectionElem::Offset(i) => out = format!("{out}[{}]", i),
            }
        }

        out
    }

    /// Perform a type substitution - actually simply clone the object
    pub fn substitute(&self, _subst: &ETypeSubst) -> Self {
        self.clone()
    }
}

impl std::fmt::Display for Place {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        write!(f, "{}", self.fmt_with_ctx(&values::DummyFormatter {}))
    }
}

impl OperandConstantValue {
    pub fn fmt_with_ctx<T>(&self, ctx: &T) -> String
    where
        T: Formatter<TypeDeclId::Id> + Formatter<GlobalDeclId::Id>,
    {
        match self {
            OperandConstantValue::PrimitiveValue(c) => c.to_string(),
            OperandConstantValue::Adt(variant_id, values) => {
                // It is a bit annoying: in order to properly format the value,
                // we need the type (which contains the type def id).
                // Anyway, the printing utilities are mostly for debugging.
                let variant_id = match variant_id {
                    Option::Some(id) => format!("Some({id})"),
                    Option::None => "None".to_string(),
                };
                let values: Vec<String> = values.iter().map(|v| v.fmt_with_ctx(ctx)).collect();
                format!("ConstAdt {} [{}]", variant_id, values.join(", "))
            }
            OperandConstantValue::ConstantId(id) => ctx.format_object(*id),
            OperandConstantValue::StaticId(id) => format!("alloc: &{}", ctx.format_object(*id)),
        }
    }
}

impl std::fmt::Display for OperandConstantValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        write!(f, "{}", self.fmt_with_ctx(&values::DummyFormatter {}))
    }
}

impl Operand {
    pub fn fmt_with_ctx<T>(&self, ctx: &T) -> String
    where
        T: Formatter<VarId::Id>
            + Formatter<TypeDeclId::Id>
            + Formatter<GlobalDeclId::Id>
            + Formatter<(TypeDeclId::Id, Option<VariantId::Id>, FieldId::Id)>,
    {
        match self {
            Operand::Copy(p) => format!("copy ({})", p.fmt_with_ctx(ctx)),
            Operand::Move(p) => format!("move ({})", p.fmt_with_ctx(ctx)),
            Operand::Const(_, c) => format!("const ({})", c.fmt_with_ctx(ctx)),
        }
    }

    /// Perform a type substitution - actually simply clone the object
    pub fn substitute(&self, _subst: &ETypeSubst) -> Self {
        self.clone()
    }
}

impl std::fmt::Display for Operand {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        write!(f, "{}", self.fmt_with_ctx(&values::DummyFormatter {}))
    }
}

impl Rvalue {
    pub fn fmt_with_ctx<'a, T>(&'a self, ctx: &T) -> String
    where
        T: Formatter<VarId::Id>
            + Formatter<TypeDeclId::Id>
            + Formatter<GlobalDeclId::Id>
            + Formatter<(TypeDeclId::Id, VariantId::Id)>
            + Formatter<(TypeDeclId::Id, Option<VariantId::Id>, FieldId::Id)>
            + Formatter<TypeVarId::Id>
            + Formatter<&'a ErasedRegion>,
    {
        match self {
            Rvalue::Use(x) => x.fmt_with_ctx(ctx),
            Rvalue::Ref(place, borrow_kind) => match borrow_kind {
                BorrowKind::Shared => format!("&{}", place.fmt_with_ctx(ctx)),
                BorrowKind::Mut => format!("&mut {}", place.fmt_with_ctx(ctx)),
                BorrowKind::TwoPhaseMut => {
                    format!("&two-phase-mut {}", place.fmt_with_ctx(ctx))
                }
                BorrowKind::Shallow => format!("&shallow {}", place.fmt_with_ctx(ctx)),
            },
            Rvalue::UnaryOp(unop, x) => {
                format!("{}({})", unop, x.fmt_with_ctx(ctx))
            }
            Rvalue::BinaryOp(binop, x, y) => {
                format!("{} {} {}", x.fmt_with_ctx(ctx), binop, y.fmt_with_ctx(ctx))
            }
            Rvalue::Discriminant(p) => {
                format!("@discriminant({})", p.fmt_with_ctx(ctx),)
            }
            Rvalue::Aggregate(kind, ops) => {
                let ops_s: Vec<String> = ops.iter().map(|op| op.fmt_with_ctx(ctx)).collect();
                match kind {
                    AggregateKind::Tuple => format!("({})", ops_s.join(", ")),
                    AggregateKind::Option(variant_id, _) => {
                        if *variant_id == assumed::OPTION_NONE_VARIANT_ID {
                            assert!(ops.is_empty());
                            "@Option::None".to_string()
                        } else if *variant_id == assumed::OPTION_SOME_VARIANT_ID {
                            assert!(ops.len() == 1);
                            format!("@Option::Some({})", ops[0].fmt_with_ctx(ctx))
                        } else {
                            unreachable!();
                        }
                    }
                    AggregateKind::Adt(def_id, variant_id, _, _, _) => {
                        // Format every field
                        let mut fields = vec![];
                        for (i, op) in ops.iter().enumerate() {
                            let field_id = FieldId::Id::new(i);
                            let field_name = ctx.format_object((*def_id, *variant_id, field_id));
                            fields.push(format!("{}: {}", field_name, op.fmt_with_ctx(ctx)));
                        }

                        let variant = match variant_id {
                            None => ctx.format_object(*def_id),
                            Some(variant_id) => ctx.format_object((*def_id, *variant_id)),
                        };
                        format!("{} {{ {} }}", variant, fields.join(", "))
                    }
                    AggregateKind::Range(_) => {
                        format!("@Range")
                    }
                }
            }
            Rvalue::Global(gid) => ctx.format_object(*gid),
            Rvalue::Len(place) => format!("len({})", place.fmt_with_ctx(ctx)),
        }
    }

    /// Perform a type substitution - actually simply clone the object
    pub fn substitute(&self, _subst: &ETypeSubst) -> Self {
        self.clone()
    }
}

impl std::fmt::Display for Rvalue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        write!(f, "{}", self.fmt_with_ctx(&values::DummyFormatter {}))
    }
}

impl Serialize for AggregateKind {
    fn serialize<S>(&self, serializer: S) -> std::result::Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        // Note that we rename the variant names
        // Also, it seems the "standard" way of doing is the following (this is
        // consistent with what the automatically generated serializer does):
        // - if the arity is > 0, use `serialize_tuple_variant`
        // - otherwise simply serialize a string with the variant name
        //
        // Remark: we change the names of the variants, which is why we don't
        // use the [variant_name] function.
        let enum_name = "AggregateKind";
        let (variant_index, variant_arity) = self.variant_index_arity();
        match self {
            AggregateKind::Tuple => "AggregatedTuple".serialize(serializer),
            AggregateKind::Option(variant_id, ty) => {
                let mut vs = serializer.serialize_tuple_variant(
                    enum_name,
                    variant_index,
                    "AggregatedOption",
                    variant_arity,
                )?;

                vs.serialize_field(variant_id)?;
                vs.serialize_field(ty)?;

                vs.end()
            }
            AggregateKind::Adt(def_id, opt_variant_id, regions, tys, cgs) => {
                let mut vs = serializer.serialize_tuple_variant(
                    enum_name,
                    variant_index,
                    "AggregatedAdt",
                    variant_arity,
                )?;

                vs.serialize_field(def_id)?;
                vs.serialize_field(opt_variant_id)?;
                let regions = VecSerializer::new(regions);
                vs.serialize_field(&regions)?;
                let tys = VecSerializer::new(tys);
                vs.serialize_field(&tys)?;
                let cgs = VecSerializer::new(cgs);
                vs.serialize_field(&cgs)?;

                vs.end()
            }
            AggregateKind::Range(ty) => {
                let mut vs = serializer.serialize_tuple_variant(
                    enum_name,
                    variant_index,
                    "AggregatedRange",
                    variant_arity,
                )?;

                vs.serialize_field(ty)?;

                vs.end()
            }
        }
    }
}

impl Serialize for OperandConstantValue {
    fn serialize<S>(&self, serializer: S) -> std::result::Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        match self {
            // [OperandConstantValue] exists only to handle temporary cases inherited from the MIR:
            // for the final (U)LLBC format, we simply export the underlying constant value.
            OperandConstantValue::PrimitiveValue(cv) => cv.serialize(serializer),
            _ => unreachable!("unexpected `{:?}`: `OperandConstantValue` fields other than `ConstantValue` are temporary and should not occur in serialized LLBC", self),
        }
    }
}

// Derive two implementations at once: one which uses shared borrows, and one
// which uses mutable borrows.
// Generates the traits: `SharedExprVisitor` and `MutExprVisitor`.
make_generic_in_borrows! {

/// A visitor for expressions.
///
/// TODO: implement macros to automatically derive visitors.
pub trait ExprVisitor {
    fn visit_place(&mut self, p: &Place) {
        self.visit_var_id(&p.var_id);
        self.visit_projection(&p.projection);
    }

    fn visit_var_id(&mut self, _: &VarId::Id) {}

    fn visit_projection(&mut self, p: &Projection) {
        for pe in p.iter() {
            self.visit_projection_elem(pe)
        }
    }

    fn default_visit_projection_elem(&mut self, pe: &ProjectionElem) {
        match pe {
            ProjectionElem::Deref => self.visit_deref(),
            ProjectionElem::DerefBox => self.visit_deref_box(),
            ProjectionElem::DerefRawPtr => self.visit_deref_raw_ptr(),
            ProjectionElem::DerefPtrUnique => self.visit_deref_ptr_unique(),
            ProjectionElem::DerefPtrNonNull => self.visit_deref_ptr_non_null(),
            ProjectionElem::Field(proj_kind, fid) => self.visit_projection_field(proj_kind, fid),
            ProjectionElem::Offset(o) => self.visit_var_id(o),
        }
    }

    fn visit_projection_elem(&mut self, pe: &ProjectionElem) {
        self.default_visit_projection_elem(pe)
    }

    fn visit_deref(&mut self) {}
    fn visit_deref_box(&mut self) {}
    fn visit_deref_raw_ptr(&mut self) {}
    fn visit_deref_ptr_unique(&mut self) {}
    fn visit_deref_ptr_non_null(&mut self) {}
    fn visit_projection_field(&mut self, _: &FieldProjKind, _: &FieldId::Id) {}

    fn default_visit_operand(&mut self, o: &Operand) {
        match o {
            Operand::Copy(p) => self.visit_copy(p),
            Operand::Move(p) => self.visit_move(p),
            Operand::Const(ety, cv) => self.visit_operand_const(ety, cv),
        }
    }

    fn visit_operand(&mut self, o: &Operand) {
        self.default_visit_operand(o)
    }

    fn visit_copy(&mut self, p: &Place) {
        self.visit_place(p)
    }

    fn visit_move(&mut self, p: &Place) {
        self.visit_place(p)
    }

    fn visit_operand_const(&mut self, _: &ETy, _: &OperandConstantValue) {}

    fn default_visit_rvalue(&mut self, rv: &Rvalue) {
        match rv {
            Rvalue::Use(o) => self.visit_use(o),
            Rvalue::Ref(p, bkind) => self.visit_ref(p, bkind),
            Rvalue::UnaryOp(op, o1) => self.visit_unary_op(op, o1),
            Rvalue::BinaryOp(op, o1, o2) => self.visit_binary_op(op, o1, o2),
            Rvalue::Discriminant(p) => self.visit_discriminant(p),
            Rvalue::Aggregate(kind, ops) => self.visit_aggregate(kind, ops),
            Rvalue::Global(gid) => self.visit_global(gid),
            Rvalue::Len(p) => self.visit_len(p),
        }
    }

    fn visit_rvalue(&mut self, o: &Rvalue) {
        self.default_visit_rvalue(o)
    }

    fn visit_use(&mut self, o: &Operand) {
        self.visit_operand(o)
    }

    fn visit_ref(&mut self, p: &Place, _: &BorrowKind) {
        self.visit_place(p)
    }

    fn visit_unary_op(&mut self, _: &UnOp, o1: &Operand) {
        self.visit_operand(o1)
    }

    fn visit_binary_op(&mut self, _: &BinOp, o1: &Operand, o2: &Operand) {
        self.visit_operand(o1);
        self.visit_operand(o2);
    }

    fn visit_discriminant(&mut self, p: &Place) {
        self.visit_place(p)
    }

    fn visit_aggregate(&mut self, _: &AggregateKind, ops: &Vec<Operand>) {
        for o in ops {
            self.visit_operand(o)
        }
    }

    fn visit_global(&mut self, _: &GlobalDeclId::Id) {}

    fn visit_len(&mut self, p: &Place) {
        self.visit_place(p)
    }
}

} // make_generic_in_borrows
