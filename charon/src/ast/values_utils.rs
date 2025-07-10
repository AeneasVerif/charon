//! Implementations for [crate::values]
use crate::ast::*;
use serde::{Deserialize, Serialize, Serializer, ser::SerializeTupleVariant};

#[derive(Debug, Clone)]
pub enum ScalarError {
    /// Attempt to use a signed scalar as an unsigned scalar or vice-versa
    IncorrectSign,
    /// Out of bounds scalar
    OutOfBounds,
    UnsupportedPtrSize,
}
/// Our redefinition of Result - we don't care much about the I/O part.
pub type ScalarResult<T> = std::result::Result<T, ScalarError>;

macro_rules! from_ne_bytes {
    ($m:ident, $b:ident, [$(($i:ident, $s:ident, $n_ty:ty, $t:ty)),*]) => {
        match $m {
            $(
                IntegerTy::$i => {
                    let n = size_of::<$n_ty>();
                    let b: [u8; _] = if cfg!(target_endian = "big"){
                        $b[16-n..16].try_into().unwrap()
                    } else {
                        $b[0..n].try_into().unwrap()
                    };
                    ScalarValue::$s($m,<$n_ty>::from_ne_bytes(b) as $t)
                }
            )*
        }
    }
}

impl ScalarValue {
    fn ptr_size_max(ptr_size: ByteCount, signed: bool) -> ScalarResult<u128> {
        match ptr_size {
            2 => Ok(if signed {
                i16::MAX as u128
            } else {
                u16::MAX as u128
            }),
            4 => Ok(if signed {
                i32::MAX as u128
            } else {
                u32::MAX as u128
            }),
            8 => Ok(if signed {
                i64::MAX as u128
            } else {
                u64::MAX as u128
            }),
            _ => Err(ScalarError::UnsupportedPtrSize),
        }
    }

    fn ptr_size_min(ptr_size: ByteCount, signed: bool) -> ScalarResult<i128> {
        match ptr_size {
            2 => Ok(if signed {
                i16::MIN as i128
            } else {
                u16::MIN as i128
            }),
            4 => Ok(if signed {
                i32::MIN as i128
            } else {
                u32::MIN as i128
            }),
            8 => Ok(if signed {
                i64::MIN as i128
            } else {
                u64::MIN as i128
            }),
            _ => Err(ScalarError::UnsupportedPtrSize),
        }
    }

    pub fn get_integer_ty(&self) -> IntegerTy {
        match self {
            ScalarValue::Signed(ty, _) | ScalarValue::Unsigned(ty, _) => *ty,
        }
    }

    pub fn is_int(&self) -> bool {
        matches!(self, ScalarValue::Signed(_, _))
    }

    pub fn is_uint(&self) -> bool {
        matches!(self, ScalarValue::Unsigned(_, _))
    }

    /// When computing the result of binary operations, we convert the values
    /// to u128 then back to the target type (while performing dynamic checks
    /// of course).
    pub fn as_uint(&self) -> ScalarResult<u128> {
        match self {
            ScalarValue::Unsigned(ty, v) if ty.is_unsigned() => Ok(*v),
            _ => Err(ScalarError::IncorrectSign),
        }
    }

    pub fn uint_is_in_bounds(ptr_size: ByteCount, ty: IntegerTy, v: u128) -> bool {
        match ty {
            IntegerTy::Usize => v <= Self::ptr_size_max(ptr_size, false).unwrap(),
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
            IntegerTy::Usize
            | IntegerTy::U8
            | IntegerTy::U16
            | IntegerTy::U32
            | IntegerTy::U64
            | IntegerTy::U128 => ScalarValue::Unsigned(ty, v),
            _ => panic!("Expected an unsigned integer kind"),
        }
    }

    pub fn from_uint(ptr_size: ByteCount, ty: IntegerTy, v: u128) -> ScalarResult<ScalarValue> {
        if !ScalarValue::uint_is_in_bounds(ptr_size, ty, v) {
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
            ScalarValue::Signed(ty, v) if ty.is_signed() => Ok(*v),
            _ => Err(ScalarError::IncorrectSign),
        }
    }

    pub fn int_is_in_bounds(ptr_size: ByteCount, ty: IntegerTy, v: i128) -> bool {
        match ty {
            IntegerTy::Isize => {
                v >= Self::ptr_size_min(ptr_size, true).unwrap()
                    && v <= Self::ptr_size_max(ptr_size, true).unwrap() as i128
            }
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
            IntegerTy::Isize
            | IntegerTy::I8
            | IntegerTy::I16
            | IntegerTy::I32
            | IntegerTy::I64
            | IntegerTy::I128 => ScalarValue::Signed(ty, v),
            _ => panic!("Expected a signed integer kind"),
        }
    }

    /// Most integers are represented as `u128` by rustc. We must be careful not to sign-extend.
    pub fn to_bits(&self) -> u128 {
        match *self {
            ScalarValue::Unsigned(_, v) => v,
            ScalarValue::Signed(_, v) => u128::from_be_bytes(v.to_ne_bytes()),
        }
    }

    pub fn from_bytes(ty: IntegerTy, bytes: [u8; 16]) -> Self {
        from_ne_bytes!(
            ty,
            bytes,
            [
                (Isize, Signed, isize, i128),
                (I8, Signed, i8, i128),
                (I16, Signed, i16, i128),
                (I32, Signed, i32, i128),
                (I64, Signed, i64, i128),
                (I128, Signed, i128, i128),
                (Usize, Unsigned, usize, u128),
                (U8, Unsigned, u8, u128),
                (U16, Unsigned, u16, u128),
                (U32, Unsigned, u32, u128),
                (U64, Unsigned, u64, u128),
                (U128, Unsigned, u128, u128)
            ]
        )
    }

    pub fn from_bits(ty: IntegerTy, bits: u128) -> Self {
        let bytes = bits.to_ne_bytes();
        Self::from_bytes(ty, bytes)
    }

    /// **Warning**: most constants are stored as u128 by rustc. When converting
    /// to i128, it is not correct to do `v as i128`, we must reinterpret the
    /// bits (see [ScalarValue::from_le_bytes]).
    pub fn from_int(ptr_size: ByteCount, ty: IntegerTy, v: i128) -> ScalarResult<ScalarValue> {
        if !ScalarValue::int_is_in_bounds(ptr_size, ty, v) {
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
        let mut tv =
            serializer.serialize_tuple_variant(enum_name, variant_index, variant_name, 2)?;
        match self {
            ScalarValue::Signed(ty, i) => {
                tv.serialize_field(ty)?;
                tv.serialize_field(&i.to_string())?;
            }
            ScalarValue::Unsigned(ty, i) => {
                tv.serialize_field(ty)?;
                tv.serialize_field(&i.to_string())?;
            }
        };
        tv.end()
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
                let (k, (ty, i)): (String, (String, String)) =
                    map.next_entry()?.expect("Malformed ScalarValue");
                let ty = match ty.as_str() {
                    "Isize" => IntegerTy::Isize,
                    "I8" => IntegerTy::I8,
                    "I16" => IntegerTy::I16,
                    "I32" => IntegerTy::I32,
                    "I64" => IntegerTy::I64,
                    "I128" => IntegerTy::I128,
                    "Usize" => IntegerTy::Usize,
                    "U8" => IntegerTy::U8,
                    "U16" => IntegerTy::U16,
                    "U32" => IntegerTy::U32,
                    "U64" => IntegerTy::U64,
                    "U128" => IntegerTy::U128,
                    _ => {
                        return Err(A::Error::custom(format!(
                            "{ty} is not a valid type for a ScalarValue"
                        )));
                    }
                };
                Ok(match k.as_str() {
                    "Signed" => {
                        let i = i.parse().unwrap();
                        ScalarValue::Signed(ty, i)
                    }
                    "Unsigned" => {
                        let i = i.parse().unwrap();
                        ScalarValue::Unsigned(ty, i)
                    }
                    _ => {
                        return Err(A::Error::custom(format!(
                            "{k} is not a valid type for a ScalarValue"
                        )));
                    }
                })
            }
        }
        deserializer.deserialize_map(Visitor)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_big_endian_scalars() -> ScalarResult<()> {
        let u128 = 0x12345678901234567890123456789012u128;
        let ne_bytes = u128.to_ne_bytes();

        let ne_scalar = ScalarValue::from_bytes(IntegerTy::U128, ne_bytes);
        assert_eq!(ne_scalar, ScalarValue::Unsigned(IntegerTy::U128, u128));

        let i64 = 0x1234567890123456i64;
        let ne_bytes = (i64 as i128).to_ne_bytes();
        let ne_scalar = ScalarValue::from_bytes(IntegerTy::I64, ne_bytes);
        assert_eq!(ne_scalar, ScalarValue::Signed(IntegerTy::I64, i64 as i128));

        Ok(())
    }
}
