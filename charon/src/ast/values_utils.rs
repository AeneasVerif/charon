//! Implementations for [crate::values]
use crate::ast::*;
use serde::{Deserialize, Serialize, Serializer};

#[derive(Debug, Clone)]
pub enum ScalarError {
    /// Attempt to use a signed scalar as an unsigned scalar or vice-versa
    IncorrectSign,
    /// Out of bounds scalar
    OutOfBounds,
}
/// Our redefinition of Result - we don't care much about the I/O part.
pub type ScalarResult<T> = std::result::Result<T, ScalarError>;

impl ScalarValue {
    pub fn get_integer_ty(&self) -> IntegerTy {
        match self {
            ScalarValue::Isize(_) => IntegerTy::Isize,
            ScalarValue::I8(_) => IntegerTy::I8,
            ScalarValue::I16(_) => IntegerTy::I16,
            ScalarValue::I32(_) => IntegerTy::I32,
            ScalarValue::I64(_) => IntegerTy::I64,
            ScalarValue::I128(_) => IntegerTy::I128,
            ScalarValue::Usize(_) => IntegerTy::Usize,
            ScalarValue::U8(_) => IntegerTy::U8,
            ScalarValue::U16(_) => IntegerTy::U16,
            ScalarValue::U32(_) => IntegerTy::U32,
            ScalarValue::U64(_) => IntegerTy::U64,
            ScalarValue::U128(_) => IntegerTy::U128,
        }
    }

    pub fn is_int(&self) -> bool {
        matches!(
            self,
            ScalarValue::Isize(_)
                | ScalarValue::I8(_)
                | ScalarValue::I16(_)
                | ScalarValue::I32(_)
                | ScalarValue::I64(_)
                | ScalarValue::I128(_)
        )
    }

    pub fn is_uint(&self) -> bool {
        matches!(
            self,
            ScalarValue::Usize(_)
                | ScalarValue::U8(_)
                | ScalarValue::U16(_)
                | ScalarValue::U32(_)
                | ScalarValue::U64(_)
                | ScalarValue::U128(_)
        )
    }

    /// When computing the result of binary operations, we convert the values
    /// to u128 then back to the target type (while performing dynamic checks
    /// of course).
    pub fn as_uint(&self) -> ScalarResult<u128> {
        match self {
            ScalarValue::Usize(v) => Ok(*v as u128),
            ScalarValue::U8(v) => Ok(*v as u128),
            ScalarValue::U16(v) => Ok(*v as u128),
            ScalarValue::U32(v) => Ok(*v as u128),
            ScalarValue::U64(v) => Ok(*v as u128),
            ScalarValue::U128(v) => Ok(*v),
            _ => Err(ScalarError::IncorrectSign),
        }
    }

    pub fn uint_is_in_bounds(ty: IntegerTy, v: u128) -> bool {
        match ty {
            IntegerTy::Usize => v <= (usize::MAX as u128),
            IntegerTy::U8 => v <= (u8::MAX as u128),
            IntegerTy::U16 => v <= (u16::MAX as u128),
            IntegerTy::U32 => v <= (u32::MAX as u128),
            IntegerTy::U64 => v <= (u64::MAX as u128),
            IntegerTy::U128 => true,
            _ => false,
        }
    }

    pub fn from_unchecked_uint(ty: IntegerTy, v: u128) -> ScalarValue {
        match ty {
            IntegerTy::Usize => ScalarValue::Usize(v as u64),
            IntegerTy::U8 => ScalarValue::U8(v as u8),
            IntegerTy::U16 => ScalarValue::U16(v as u16),
            IntegerTy::U32 => ScalarValue::U32(v as u32),
            IntegerTy::U64 => ScalarValue::U64(v as u64),
            IntegerTy::U128 => ScalarValue::U128(v),
            _ => panic!("Expected an unsigned integer kind"),
        }
    }

    pub fn from_uint(ty: IntegerTy, v: u128) -> ScalarResult<ScalarValue> {
        if !ScalarValue::uint_is_in_bounds(ty, v) {
            trace!("Not in bounds for {:?}: {}", ty, v);
            Err(ScalarError::OutOfBounds)
        } else {
            Ok(ScalarValue::from_unchecked_uint(ty, v))
        }
    }

    /// When computing the result of binary operations, we convert the values
    /// to i128 then back to the target type (while performing dynamic checks
    /// of course).
    pub fn as_int(&self) -> ScalarResult<i128> {
        match self {
            ScalarValue::Isize(v) => Ok(*v as i128),
            ScalarValue::I8(v) => Ok(*v as i128),
            ScalarValue::I16(v) => Ok(*v as i128),
            ScalarValue::I32(v) => Ok(*v as i128),
            ScalarValue::I64(v) => Ok(*v as i128),
            ScalarValue::I128(v) => Ok(*v),
            _ => Err(ScalarError::IncorrectSign),
        }
    }

    pub fn int_is_in_bounds(ty: IntegerTy, v: i128) -> bool {
        match ty {
            IntegerTy::Isize => v >= (isize::MIN as i128) && v <= (isize::MAX as i128),
            IntegerTy::I8 => v >= (i8::MIN as i128) && v <= (i8::MAX as i128),
            IntegerTy::I16 => v >= (i16::MIN as i128) && v <= (i16::MAX as i128),
            IntegerTy::I32 => v >= (i32::MIN as i128) && v <= (i32::MAX as i128),
            IntegerTy::I64 => v >= (i64::MIN as i128) && v <= (i64::MAX as i128),
            IntegerTy::I128 => true,
            _ => false,
        }
    }

    pub fn from_unchecked_int(ty: IntegerTy, v: i128) -> ScalarValue {
        match ty {
            IntegerTy::Isize => ScalarValue::Isize(v as i64),
            IntegerTy::I8 => ScalarValue::I8(v as i8),
            IntegerTy::I16 => ScalarValue::I16(v as i16),
            IntegerTy::I32 => ScalarValue::I32(v as i32),
            IntegerTy::I64 => ScalarValue::I64(v as i64),
            IntegerTy::I128 => ScalarValue::I128(v),
            _ => panic!("Expected a signed integer kind"),
        }
    }

    pub fn from_le_bytes(ty: IntegerTy, b: [u8; 16]) -> ScalarValue {
        match ty {
            IntegerTy::Isize => {
                let b: [u8; 8] = b[0..8].try_into().unwrap();
                ScalarValue::Isize(i64::from_le_bytes(b))
            }
            IntegerTy::I8 => {
                let b: [u8; 1] = b[0..1].try_into().unwrap();
                ScalarValue::I8(i8::from_le_bytes(b))
            }
            IntegerTy::I16 => {
                let b: [u8; 2] = b[0..2].try_into().unwrap();
                ScalarValue::I16(i16::from_le_bytes(b))
            }
            IntegerTy::I32 => {
                let b: [u8; 4] = b[0..4].try_into().unwrap();
                ScalarValue::I32(i32::from_le_bytes(b))
            }
            IntegerTy::I64 => {
                let b: [u8; 8] = b[0..8].try_into().unwrap();
                ScalarValue::I64(i64::from_le_bytes(b))
            }
            IntegerTy::I128 => {
                let b: [u8; 16] = b[0..16].try_into().unwrap();
                ScalarValue::I128(i128::from_le_bytes(b))
            }
            IntegerTy::Usize => {
                let b: [u8; 8] = b[0..8].try_into().unwrap();
                ScalarValue::Usize(u64::from_le_bytes(b))
            }
            IntegerTy::U8 => {
                let b: [u8; 1] = b[0..1].try_into().unwrap();
                ScalarValue::U8(u8::from_le_bytes(b))
            }
            IntegerTy::U16 => {
                let b: [u8; 2] = b[0..2].try_into().unwrap();
                ScalarValue::U16(u16::from_le_bytes(b))
            }
            IntegerTy::U32 => {
                let b: [u8; 4] = b[0..4].try_into().unwrap();
                ScalarValue::U32(u32::from_le_bytes(b))
            }
            IntegerTy::U64 => {
                let b: [u8; 8] = b[0..8].try_into().unwrap();
                ScalarValue::U64(u64::from_le_bytes(b))
            }
            IntegerTy::U128 => {
                let b: [u8; 16] = b[0..16].try_into().unwrap();
                ScalarValue::U128(u128::from_le_bytes(b))
            }
        }
    }

    /// Most integers are represented as `u128` by rustc. We must be careful not to sign-extend.
    pub fn to_bits(&self) -> u128 {
        match *self {
            ScalarValue::Usize(v) => v as u128,
            ScalarValue::U8(v) => v as u128,
            ScalarValue::U16(v) => v as u128,
            ScalarValue::U32(v) => v as u128,
            ScalarValue::U64(v) => v as u128,
            ScalarValue::U128(v) => v,
            ScalarValue::Isize(v) => v as usize as u128,
            ScalarValue::I8(v) => v as u8 as u128,
            ScalarValue::I16(v) => v as u16 as u128,
            ScalarValue::I32(v) => v as u32 as u128,
            ScalarValue::I64(v) => v as u64 as u128,
            ScalarValue::I128(v) => v as u128,
        }
    }

    pub fn from_bits(ty: IntegerTy, bits: u128) -> Self {
        Self::from_le_bytes(ty, bits.to_le_bytes())
    }

    /// **Warning**: most constants are stored as u128 by rustc. When converting
    /// to i128, it is not correct to do `v as i128`, we must reinterpret the
    /// bits (see [ScalarValue::from_le_bytes]).
    pub fn from_int(ty: IntegerTy, v: i128) -> ScalarResult<ScalarValue> {
        if !ScalarValue::int_is_in_bounds(ty, v) {
            Err(ScalarError::OutOfBounds)
        } else {
            Ok(ScalarValue::from_unchecked_int(ty, v))
        }
    }

    pub fn to_constant(self) -> ConstantExpr {
        ConstantExpr {
            value: RawConstantExpr::Literal(Literal::Scalar(self)),
            ty: TyKind::Literal(LiteralTy::Integer(self.get_integer_ty())).into_ty(),
        }
    }
}

/// Custom serializer that stores integers as strings to avoid overflow.
impl Serialize for ScalarValue {
    fn serialize<S>(&self, serializer: S) -> std::result::Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let enum_name = "ScalarValue";
        let variant_name = self.variant_name();
        let (variant_index, _variant_arity) = self.variant_index_arity();
        let v = match self {
            ScalarValue::Isize(i) => i.to_string(),
            ScalarValue::I8(i) => i.to_string(),
            ScalarValue::I16(i) => i.to_string(),
            ScalarValue::I32(i) => i.to_string(),
            ScalarValue::I64(i) => i.to_string(),
            ScalarValue::I128(i) => i.to_string(),
            ScalarValue::Usize(i) => i.to_string(),
            ScalarValue::U8(i) => i.to_string(),
            ScalarValue::U16(i) => i.to_string(),
            ScalarValue::U32(i) => i.to_string(),
            ScalarValue::U64(i) => i.to_string(),
            ScalarValue::U128(i) => i.to_string(),
        };
        serializer.serialize_newtype_variant(enum_name, variant_index, variant_name, &v)
    }
}

impl<'de> Deserialize<'de> for ScalarValue {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        struct Visitor;
        impl<'de> serde::de::Visitor<'de> for Visitor {
            type Value = ScalarValue;
            fn expecting(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
                write!(f, "ScalarValue")
            }
            fn visit_map<A: serde::de::MapAccess<'de>>(
                self,
                mut map: A,
            ) -> Result<Self::Value, A::Error> {
                use serde::de::Error;
                let (k, v): (String, String) = map.next_entry()?.expect("Malformed ScalarValue");
                Ok(match k.as_str() {
                    "Isize" => ScalarValue::Isize(v.parse().unwrap()),
                    "I8" => ScalarValue::I8(v.parse().unwrap()),
                    "I16" => ScalarValue::I16(v.parse().unwrap()),
                    "I32" => ScalarValue::I32(v.parse().unwrap()),
                    "I64" => ScalarValue::I64(v.parse().unwrap()),
                    "I128" => ScalarValue::I128(v.parse().unwrap()),
                    "Usize" => ScalarValue::Usize(v.parse().unwrap()),
                    "U8" => ScalarValue::U8(v.parse().unwrap()),
                    "U16" => ScalarValue::U16(v.parse().unwrap()),
                    "U32" => ScalarValue::U32(v.parse().unwrap()),
                    "U64" => ScalarValue::U64(v.parse().unwrap()),
                    "U128" => ScalarValue::U128(v.parse().unwrap()),
                    _ => {
                        return Err(A::Error::custom(format!(
                            "{k} is not a valid type for a ScalarValue"
                        )))
                    }
                })
            }
        }
        deserializer.deserialize_map(Visitor)
    }
}
