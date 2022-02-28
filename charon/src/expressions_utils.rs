//! This file groups everything which is linked to implementations about expression.rs
#![allow(dead_code)]

use crate::common::*;
use crate::expressions::*;
use crate::formatter::Formatter;
use crate::types::*;
use crate::values;
use crate::values::*;
use serde::ser::SerializeStruct;
use serde::ser::SerializeTupleVariant;
use serde::{Serialize, Serializer};

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
        }
    }
}

impl std::string::ToString for UnOp {
    fn to_string(&self) -> String {
        match self {
            UnOp::Not => "~".to_owned(),
            UnOp::Neg => "-".to_owned(),
        }
    }
}

impl std::string::ToString for BinOp {
    fn to_string(&self) -> String {
        match self {
            BinOp::BitXor => "^".to_owned(),
            BinOp::BitAnd => "&".to_owned(),
            BinOp::BitOr => "|".to_owned(),
            BinOp::Eq => "==".to_owned(),
            BinOp::Lt => "<".to_owned(),
            BinOp::Le => "<=".to_owned(),
            BinOp::Ne => "!=".to_owned(),
            BinOp::Ge => ">=".to_owned(),
            BinOp::Gt => ">".to_owned(),
            BinOp::Div => "/".to_owned(),
            BinOp::Rem => "%".to_owned(),
            BinOp::Add => "+".to_owned(),
            BinOp::Sub => "-".to_owned(),
            BinOp::Mul => "*".to_owned(),
            BinOp::Shl => "<<".to_owned(),
            BinOp::Shr => ">>".to_owned(),
        }
    }
}

impl Place {
    pub fn fmt_with_ctx<T>(&self, ctx: &T) -> String
    where
        T: Formatter<VarId::Id> + Formatter<(TypeDeclId::Id, Option<VariantId::Id>, FieldId::Id)>,
    {
        let mut out = ctx.format_object(self.var_id);

        for p in &self.projection {
            match p {
                ProjectionElem::Deref => {
                    out = format!("*({})", out);
                }
                ProjectionElem::DerefBox => {
                    out = format!("deref_box ({})", out);
                }
                ProjectionElem::Field(proj_kind, field_id) => match proj_kind {
                    FieldProjKind::Adt(adt_id, opt_variant_id) => {
                        let field_name = ctx.format_object((*adt_id, *opt_variant_id, *field_id));
                        let downcast = match opt_variant_id {
                            None => "".to_string(),
                            Some(variant_id) => format!(" as variant @{}", variant_id),
                        };
                        out = format!("({}{}).{}", out, downcast, field_name);
                    }
                    FieldProjKind::Tuple(_) => {
                        out = format!("({}).{}", out, field_id);
                    }
                    FieldProjKind::Option(_) => {
                        out = format!("({}).{}", out, field_id);
                    }
                },
            }
        }

        out
    }

    /// Perform a type substitution - actually simply clone the object
    pub fn substitute(&self, _subst: &ETypeSubst) -> Self {
        self.clone()
    }
}

impl std::string::ToString for Place {
    fn to_string(&self) -> String {
        self.fmt_with_ctx(&values::DummyFormatter {})
    }
}

impl OperandConstantValue {
    pub fn fmt_with_ctx<T>(&self, ctx: &T) -> String
    where
        T: Formatter<TypeDeclId::Id>,
    {
        match self {
            OperandConstantValue::ConstantValue(c) => c.to_string(),
            OperandConstantValue::Adt(variant_id, values) => {
                // It is a bit annoying: in order to properly format the value,
                // we need the type (which contains the type def id).
                // Anyway, the printing utilities are mostly for debugging.
                let variant_id = match variant_id {
                    Option::Some(id) => format!("Some({})", id).to_string(),
                    Option::None => "None".to_string(),
                };
                let values: Vec<String> = values.iter().map(|v| v.fmt_with_ctx(ctx)).collect();
                format!("ConstAdt {} [{}]", variant_id, values.join(", ")).to_owned()
            }
        }
    }
}

impl std::string::ToString for OperandConstantValue {
    fn to_string(&self) -> String {
        self.fmt_with_ctx(&values::DummyFormatter {})
    }
}

impl Operand {
    pub fn fmt_with_ctx<T>(&self, ctx: &T) -> String
    where
        T: Formatter<VarId::Id>
            + Formatter<TypeDeclId::Id>
            + Formatter<(TypeDeclId::Id, Option<VariantId::Id>, FieldId::Id)>,
    {
        match self {
            Operand::Copy(p) => format!("copy ({})", p.fmt_with_ctx(ctx)).to_owned(),
            Operand::Move(p) => format!("move ({})", p.fmt_with_ctx(ctx)).to_owned(),
            Operand::Constant(_, c) => format!("const ({})", c.fmt_with_ctx(ctx)).to_owned(),
        }
    }

    /// Perform a type substitution - actually simply clone the object
    pub fn substitute(&self, _subst: &ETypeSubst) -> Self {
        self.clone()
    }
}

impl std::string::ToString for Operand {
    fn to_string(&self) -> String {
        self.fmt_with_ctx(&values::DummyFormatter {})
    }
}

impl Rvalue {
    pub fn fmt_with_ctx<T>(&self, ctx: &T) -> String
    where
        T: Formatter<VarId::Id>
            + Formatter<TypeDeclId::Id>
            + Formatter<(TypeDeclId::Id, VariantId::Id)>
            + Formatter<(TypeDeclId::Id, Option<VariantId::Id>, FieldId::Id)>,
    {
        match self {
            Rvalue::Use(x) => x.fmt_with_ctx(ctx),
            Rvalue::Ref(place, borrow_kind) => match borrow_kind {
                BorrowKind::Shared => format!("&{}", place.fmt_with_ctx(ctx)).to_owned(),
                BorrowKind::Mut => format!("&mut {}", place.fmt_with_ctx(ctx)).to_owned(),
                BorrowKind::TwoPhaseMut => {
                    format!("&two-phase-mut {}", place.fmt_with_ctx(ctx)).to_owned()
                }
            },
            Rvalue::UnaryOp(unop, x) => {
                format!("{}({})", unop.to_string(), x.fmt_with_ctx(ctx)).to_owned()
            }
            Rvalue::BinaryOp(binop, x, y) => format!(
                "{} {} {}",
                x.fmt_with_ctx(ctx),
                binop.to_string(),
                y.fmt_with_ctx(ctx)
            )
            .to_owned(),
            Rvalue::Discriminant(p) => {
                format!("@discriminant({})", p.fmt_with_ctx(ctx),).to_owned()
            }
            Rvalue::Aggregate(kind, ops) => {
                let ops_s: Vec<String> = ops.iter().map(|op| op.fmt_with_ctx(ctx)).collect();
                match kind {
                    AggregateKind::Tuple => format!("({})", ops_s.join(", ")).to_owned(),
                    AggregateKind::Adt(def_id, variant_id, _, _) => {
                        // Format every field
                        let mut fields = vec![];
                        for i in 0..ops.len() {
                            let field_id = FieldId::Id::new(i);
                            let field_name = ctx.format_object((*def_id, *variant_id, field_id));
                            let op = &ops[i];
                            fields.push(
                                format!("{}: {}", field_name, op.fmt_with_ctx(ctx)).to_owned(),
                            );
                        }

                        let variant = match variant_id {
                            None => ctx.format_object(*def_id),
                            Some(variant_id) => ctx.format_object((*def_id, *variant_id)),
                        };
                        format!("{} {{ {} }}", variant, fields.join(", "))
                    }
                }
            }
        }
    }

    /// Perform a type substitution - actually simply clone the object
    pub fn substitute(&self, _subst: &ETypeSubst) -> Self {
        self.clone()
    }
}

impl std::string::ToString for Rvalue {
    fn to_string(&self) -> String {
        self.fmt_with_ctx(&values::DummyFormatter {})
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
        match self {
            AggregateKind::Tuple => "AggregatedTuple".serialize(serializer),
            AggregateKind::Adt(def_id, opt_variant_id, regions, tys) => {
                let mut vs =
                    serializer.serialize_tuple_variant("AggregateKind", 1, "AggregatedAdt", 4)?;

                vs.serialize_field(def_id)?;
                vs.serialize_field(opt_variant_id)?;
                let regions = VecSerializer::new(regions);
                vs.serialize_field(&regions)?;
                let tys = VecSerializer::new(tys);
                vs.serialize_field(&tys)?;

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
        let enum_name = "OperandConstantValue";
        // We change the variant names for serialization
        let variant_name = match self {
            OperandConstantValue::ConstantValue(_) => "ConstantValue",
            OperandConstantValue::Adt(_, _) => "ConstantAdt",
        };
        let (variant_index, variant_arity) = self.variant_index_arity();
        // It seems the "standard" way of doing is the following (this is
        // consistent with what the automatically generated serializer does):
        // - if the arity is > 0, use `serialize_tuple_variant`
        // - otherwise simply serialize a string with the variant name
        if variant_arity > 0 {
            let mut vs = serializer.serialize_tuple_variant(
                enum_name,
                variant_index,
                variant_name,
                variant_arity,
            )?;
            match self {
                OperandConstantValue::ConstantValue(cv) => {
                    vs.serialize_field(cv)?;
                }
                OperandConstantValue::Adt(variant_id, values) => {
                    vs.serialize_field(variant_id)?;
                    let values = VectorSerializer::new(values);
                    vs.serialize_field(&values)?;
                }
            }
            vs.end()
        } else {
            variant_name.serialize(serializer)
        }
    }
}
