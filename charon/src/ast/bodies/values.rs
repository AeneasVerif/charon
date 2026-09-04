//! Contains definitions for variables and constant values.
use core::hash::Hash;
use derive_generic_visitor::{Drive, DriveMut, DriveTwo};
use macros::{EnumAsGetters, EnumIsA, VariantIndexArity, VariantName};
use serde::{Deserialize, Serialize};
use serde_state::{DeserializeState, SerializeState};
use std::vec::Vec;

use crate::ast::*;

/// A constant expression.
#[derive(
    Debug,
    PartialEq,
    Eq,
    PartialOrd,
    Ord,
    Hash,
    Clone,
    SerializeState,
    DeserializeState,
    Drive,
    DriveMut,
    DriveTwo,
)]
#[serde_state(state_implements = DedupSerializerState)] // Avoid corecursive impls due to perfect derive
pub struct ConstantExpr(pub HashConsed<(ConstantExprKind, Ty)>);

#[derive(
    Debug,
    PartialEq,
    Eq,
    PartialOrd,
    Ord,
    Hash,
    Clone,
    VariantName,
    EnumIsA,
    EnumAsGetters,
    SerializeState,
    DeserializeState,
    Drive,
    DriveMut,
    DriveTwo,
)]
#[cfg_attr(feature = "charon_on_charon", charon::variants_prefix("C"))]
pub enum ConstantExprKind {
    #[serde_state(stateless)]
    Literal(Literal),
    /// In most situations:
    /// Enumeration with one variant with no fields, structure with
    /// no fields, unit (encoded as a 0-tuple).
    ///
    /// Less frequently: arbitrary ADT values.
    ///
    /// We eliminate this case in a micro-pass.
    Adt(Option<VariantId>, Vec<ConstantExpr>),
    Array(Vec<ConstantExpr>),
    /// The value is a top-level constant/static.
    ///
    /// We eliminate this case in a micro-pass.
    ///
    /// Remark: constants can actually have generic parameters.
    /// ```text
    /// struct V<const N: usize, T> {
    ///   x: [T; N],
    /// }
    ///
    /// impl<const N: usize, T> V<N, T> {
    ///   const LEN: usize = N; // This has generics <N, T>
    /// }
    ///
    /// fn use_v<const N: usize, T>(v: V<N, T>) {
    ///   let l = V::<N, T>::LEN; // We need to provided a substitution here
    /// }
    /// ```
    Global(GlobalDeclRef),
    /// A trait associated constant.
    ///
    /// Ex.:
    /// ```text
    /// impl Foo for Bar {
    ///   const C : usize = 32; // <-
    /// }
    /// ```
    TraitConst(TraitRef, AssocConstId),
    /// A reference to the vtable `static` item for this trait ref. This can be normalized for
    /// cases where we do emit a vtable item. That's not always the case for builtin traits, e.g.
    /// for `MetaSized`.
    VTableRef(TraitRef),
    /// The integer discriminant value corresponding to this enum variant.
    Discriminant(TypeDeclRef, VariantId),
    /// A shared reference to a constant value.
    ///
    /// We eliminate this case in a micro-pass.
    Ref(ConstantExpr, Option<UnsizingMetadata>),
    /// A pointer to a mutable static.
    ///
    /// We eliminate this case in a micro-pass.
    Ptr(RefKind, ConstantExpr, Option<UnsizingMetadata>),
    /// A const generic var
    Var(ConstGenericDbVar),
    /// A call to a `const fn` or a constant's initializer.
    Call(FnPtr, Vec<ConstantExpr>),
    /// Function definition -- this is a ZST constant
    FnDef(FnPtr),
    /// A function pointer to a function item; this is an actual pointer to that function item.
    ///
    /// We eliminate this case in a micro-pass.
    FnPtr(FnPtr),
    /// The size of the given type.
    SizeOf(Ty),
    /// The alignment of the given type.
    AlignOf(Ty),
    /// The `TypeId` value for a type.
    TypeId(Ty),
    /// A pointer with no provenance (e.g. 0 for the null pointer)
    ///
    /// We eliminate this case in a micro-pass.
    PtrNoProvenance(#[serde(with = "scalar_value_ser_de")] u128),
    /// Raw memory value obtained from constant evaluation. Used when a more structured
    /// representation isn't possible (e.g. for unions) or just isn't implemented yet.
    RawMemory(Vec<Byte>),
    /// A constant expression that Charon still doesn't handle, along with the reason why.
    Opaque(String),
}

/// A primitive value.
///
/// Those are for instance used for the constant operands [crate::expressions::Operand::Const]
#[derive(
    Debug,
    PartialEq,
    Eq,
    Clone,
    VariantName,
    EnumIsA,
    EnumAsGetters,
    Serialize,
    Deserialize,
    SerializeState,
    DeserializeState,
    Drive,
    DriveMut,
    DriveTwo,
    Hash,
    PartialOrd,
    Ord,
)]
#[cfg_attr(feature = "charon_on_charon", charon::variants_prefix("V"))]
#[serde_state(stateless)]
pub enum Literal {
    Scalar(ScalarValue),
    Float(FloatValue),
    Bool(bool),
    Char(char),
    ByteStr(Vec<u8>),
    Str(String),
}

/// A scalar value.
#[derive(
    Debug,
    PartialEq,
    Eq,
    Copy,
    Clone,
    EnumIsA,
    EnumAsGetters,
    VariantName,
    VariantIndexArity,
    Hash,
    PartialOrd,
    Ord,
    Serialize,
    Deserialize,
    SerializeState,
    DeserializeState,
    Drive,
    DriveMut,
    DriveTwo,
)]
#[cfg_attr(feature = "charon_on_charon", charon::variants_suffix("Scalar"))]
#[serde_state(stateless)]
pub enum ScalarValue {
    Unsigned(UIntTy, #[serde(with = "scalar_value_ser_de")] u128),
    Signed(IntTy, #[serde(with = "scalar_value_ser_de")] i128),
}

/// This is simlar to the Scalar value above. However, instead of storing
/// the float value itself, we store its String representation. This allows
/// to derive the Eq and Ord traits, which are not implemented for floats
#[derive(
    Debug,
    PartialEq,
    Eq,
    Clone,
    Serialize,
    Deserialize,
    Hash,
    PartialOrd,
    Ord,
    Drive,
    DriveMut,
    DriveTwo,
)]
pub struct FloatValue {
    #[cfg_attr(feature = "charon_on_charon", charon::rename("float_value"))]
    pub value: String,
    #[cfg_attr(feature = "charon_on_charon", charon::rename("float_ty"))]
    pub ty: FloatTy,
}

#[derive(
    Debug,
    PartialEq,
    Eq,
    PartialOrd,
    Ord,
    Clone,
    Hash,
    SerializeState,
    DeserializeState,
    Drive,
    DriveMut,
    DriveTwo,
)]
#[cfg_attr(feature = "charon_on_charon", charon::variants_prefix("Prov"))]
pub enum Provenance {
    Global(GlobalDeclRef),
    Function(FunDeclRef),
    Unknown,
}

/// A byte, in the MiniRust sense: it can either be uninitialized, a concrete u8 value,
/// or part of a pointer with provenance (e.g. to a global or a function)
#[derive(
    Debug,
    PartialEq,
    Eq,
    PartialOrd,
    Ord,
    Clone,
    Hash,
    SerializeState,
    DeserializeState,
    Drive,
    DriveMut,
    DriveTwo,
)]
pub enum Byte {
    /// An uninitialized byte
    Uninit,
    /// A concrete byte value
    Value(u8),
    /// A byte that is part of a pointer with provenance. The u8 is the offset within the
    /// pointer. Note that we do not have an actual value for this pointer byte, unlike
    /// MiniRust, as that is non-deterministic.
    Provenance(Provenance, u8),
}

macro_rules! static_constant {
    ($e:expr) => {{
        use std::sync::LazyLock;
        static CONSTANT: LazyLock<ConstantExpr> = LazyLock::new(|| $e);
        CONSTANT.clone()
    }};
}

impl ConstantExpr {
    pub fn new(kind: ConstantExprKind, ty: Ty) -> Self {
        Self(HashConsed::new((kind, ty)))
    }

    pub fn kind(&self) -> &ConstantExprKind {
        &self.0.inner().0
    }

    pub fn ty(&self) -> &Ty {
        &self.0.inner().1
    }

    pub fn with_contents_mut<R>(
        &mut self,
        f: impl FnOnce(&mut ConstantExprKind, &mut Ty) -> R,
    ) -> R {
        self.0.with_inner_mut(|(kind, ty)| f(kind, ty))
    }

    pub fn mk_unit() -> Self {
        static_constant!(ConstantExpr::new(
            ConstantExprKind::Adt(None, Vec::new()),
            Ty::mk_unit(),
        ))
    }

    pub fn mk_usize(value: u128) -> Self {
        if value == 0 {
            static_constant!(ScalarValue::mk_usize(0).to_constant())
        } else {
            ScalarValue::mk_usize(value).to_constant()
        }
    }

    pub fn as_usize_literal(&self) -> Option<u128> {
        match self.kind() {
            ConstantExprKind::Literal(Literal::Scalar(ScalarValue::Unsigned(
                UIntTy::Usize,
                value,
            ))) => Some(*value),
            _ => None,
        }
    }
}

impl Literal {
    pub fn char_from_le_bytes(bits: u128) -> Self {
        let b: [u8; 4] = bits.to_le_bytes()[0..4].try_into().unwrap();
        Literal::Char(std::char::from_u32(u32::from_le_bytes(b)).unwrap())
    }

    pub fn from_bits(lit_ty: &LiteralTy, bits: u128) -> Option<Self> {
        match *lit_ty {
            LiteralTy::Int(int_ty) => Some(Literal::Scalar(ScalarValue::from_bits(
                IntegerTy::Signed(int_ty),
                bits,
            ))),
            LiteralTy::UInt(uint_ty) => Some(Literal::Scalar(ScalarValue::from_bits(
                IntegerTy::Unsigned(uint_ty),
                bits,
            ))),
            LiteralTy::Bool => match bits {
                0 => Some(Literal::Bool(false)),
                1 => Some(Literal::Bool(true)),
                _ => None,
            },
            LiteralTy::Char => Some(Literal::char_from_le_bytes(bits)),
            LiteralTy::Float(_) => None,
        }
    }
}

impl ScalarValue {
    fn ptr_size_max(ptr_size: ByteCount, signed: bool) -> u128 {
        match ptr_size {
            2 => {
                if signed {
                    i16::MAX as u128
                } else {
                    u16::MAX as u128
                }
            }
            4 => {
                if signed {
                    i32::MAX as u128
                } else {
                    u32::MAX as u128
                }
            }
            8 => {
                if signed {
                    i64::MAX as u128
                } else {
                    u64::MAX as u128
                }
            }
            _ => panic!("`ptr_size_max`: unsupported ptr size {ptr_size}"),
        }
    }

    fn ptr_size_min(ptr_size: ByteCount, signed: bool) -> i128 {
        match ptr_size {
            2 => {
                if signed {
                    i16::MIN as i128
                } else {
                    u16::MIN as i128
                }
            }
            4 => {
                if signed {
                    i32::MIN as i128
                } else {
                    u32::MIN as i128
                }
            }
            8 => {
                if signed {
                    i64::MIN as i128
                } else {
                    u64::MIN as i128
                }
            }
            _ => panic!("`ptr_size_min`: unsupported ptr size {ptr_size}"),
        }
    }

    pub fn ty(&self) -> IntegerTy {
        match self {
            ScalarValue::Signed(ty, _) => IntegerTy::Signed(*ty),
            ScalarValue::Unsigned(ty, _) => IntegerTy::Unsigned(*ty),
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
    pub fn as_uint(&self) -> Option<u128> {
        match self {
            ScalarValue::Unsigned(_, v) => Some(*v),
            _ => None,
        }
    }

    pub fn uint_is_in_bounds(ptr_size: ByteCount, ty: UIntTy, v: u128) -> bool {
        match ty {
            UIntTy::Usize => v <= Self::ptr_size_max(ptr_size, false),
            UIntTy::U8 => v <= (u8::MAX as u128),
            UIntTy::U16 => v <= (u16::MAX as u128),
            UIntTy::U32 => v <= (u32::MAX as u128),
            UIntTy::U64 => v <= (u64::MAX as u128),
            UIntTy::U128 => true,
        }
    }

    pub fn from_unchecked_uint(ty: UIntTy, v: u128) -> ScalarValue {
        ScalarValue::Unsigned(ty, v)
    }

    pub fn from_uint(ptr_size: ByteCount, ty: UIntTy, v: u128) -> Option<Self> {
        if !ScalarValue::uint_is_in_bounds(ptr_size, ty, v) {
            None
        } else {
            Some(ScalarValue::from_unchecked_uint(ty, v))
        }
    }

    pub fn mk_usize(value: u128) -> Self {
        ScalarValue::Unsigned(UIntTy::Usize, value)
    }

    /// When computing the result of binary operations, we convert the values
    /// to i128 then back to the target type (while performing dynamic checks
    /// of course).
    pub fn as_int(&self) -> Option<i128> {
        match self {
            ScalarValue::Signed(_, v) => Some(*v),
            _ => None,
        }
    }

    pub fn int_is_in_bounds(ptr_size: ByteCount, ty: IntTy, v: i128) -> bool {
        match ty {
            IntTy::Isize => {
                v >= Self::ptr_size_min(ptr_size, true)
                    && v <= Self::ptr_size_max(ptr_size, true) as i128
            }
            IntTy::I8 => v >= (i8::MIN as i128) && v <= (i8::MAX as i128),
            IntTy::I16 => v >= (i16::MIN as i128) && v <= (i16::MAX as i128),
            IntTy::I32 => v >= (i32::MIN as i128) && v <= (i32::MAX as i128),
            IntTy::I64 => v >= (i64::MIN as i128) && v <= (i64::MAX as i128),
            IntTy::I128 => true,
        }
    }

    pub fn from_unchecked_int(ty: IntTy, v: i128) -> ScalarValue {
        ScalarValue::Signed(ty, v)
    }

    /// Most integers are represented as `u128` by rustc. We must be careful not to sign-extend.
    pub fn to_bits(&self) -> u128 {
        match *self {
            ScalarValue::Unsigned(_, v) => v,
            ScalarValue::Signed(_, v) => u128::from_le_bytes(v.to_le_bytes()),
        }
    }

    /// Translates little endian bytes into a corresponding `ScalarValue`.
    /// This needs to do the round-trip to the correct integer type to guarantee
    /// that the values are correctly sign-extended (e.g. if the bytes encode -1i8, taking all 16 bytes
    /// would lead to the value 255i128 instead of -1i128).
    pub fn from_le_bytes(ty: IntegerTy, bytes: [u8; 16]) -> Self {
        macro_rules! from_le_bytes {
            ($m:ident, $b:ident, [$(($i_ty: ty, $i:ident, $s:ident, $n_ty:ty, $t:ty)),*]) => {
                match $m {
                    $(
                        IntegerTy::$s(<$i_ty>::$i) => {
                            let n = size_of::<$n_ty>();
                            let b: [u8; _] = $b[0..n].try_into().unwrap();
                            ScalarValue::$s(<$i_ty>::$i, <$n_ty>::from_le_bytes(b) as $t)
                        }
                    )*
                }
            }
        }

        from_le_bytes!(
            ty,
            bytes,
            [
                (IntTy, Isize, Signed, isize, i128),
                (IntTy, I8, Signed, i8, i128),
                (IntTy, I16, Signed, i16, i128),
                (IntTy, I32, Signed, i32, i128),
                (IntTy, I64, Signed, i64, i128),
                (IntTy, I128, Signed, i128, i128),
                (UIntTy, Usize, Unsigned, usize, u128),
                (UIntTy, U8, Unsigned, u8, u128),
                (UIntTy, U16, Unsigned, u16, u128),
                (UIntTy, U32, Unsigned, u32, u128),
                (UIntTy, U64, Unsigned, u64, u128),
                (UIntTy, U128, Unsigned, u128, u128)
            ]
        )
    }

    pub fn from_bits(ty: IntegerTy, bits: u128) -> Self {
        let bytes = bits.to_le_bytes();
        Self::from_le_bytes(ty, bytes)
    }

    /// **Warning**: most constants are stored as u128 by rustc. When converting
    /// to i128, it is not correct to do `v as i128`, we must reinterpret the
    /// bits (see [ScalarValue::from_le_bytes]).
    pub fn from_int(ptr_size: ByteCount, ty: IntTy, v: i128) -> Option<ScalarValue> {
        if !ScalarValue::int_is_in_bounds(ptr_size, ty, v) {
            None
        } else {
            Some(ScalarValue::from_unchecked_int(ty, v))
        }
    }

    /// Increment the value, staying within the same integer type. Returns `None` on overflow.
    pub fn add(self, n: u128) -> Option<Self> {
        Some(match self {
            ScalarValue::Unsigned(ty, v) => ScalarValue::Unsigned(ty, v.checked_add(n)?),
            ScalarValue::Signed(ty, v) => {
                ScalarValue::Signed(ty, v.checked_add(n.try_into().unwrap())?)
            }
        })
    }

    pub fn to_constant(self) -> ConstantExpr {
        let literal_ty = match self {
            ScalarValue::Signed(int_ty, _) => LiteralTy::Int(int_ty),
            ScalarValue::Unsigned(uint_ty, _) => LiteralTy::UInt(uint_ty),
        };
        ConstantExpr::new(
            ConstantExprKind::Literal(Literal::Scalar(self)),
            TyKind::Literal(literal_ty).into_ty(),
        )
    }
}

/// Custom serializer that stores 128 bit integers as strings to avoid overflow.
pub(crate) mod scalar_value_ser_de {
    use std::{marker::PhantomData, str::FromStr};

    use serde::de::{Deserializer, Error};

    pub fn serialize<S, V>(val: &V, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::ser::Serializer,
        V: ToString,
    {
        serializer.serialize_str(&val.to_string())
    }

    /// Stateful variant for types that derive `SerializeState`: the state is irrelevant for a
    /// scalar, so we delegate to the stateless [`serialize`].
    pub fn serialize_state<S, State: ?Sized, V>(
        val: &V,
        _state: &State,
        serializer: S,
    ) -> Result<S::Ok, S::Error>
    where
        S: serde::ser::Serializer,
        V: ToString,
    {
        serialize(val, serializer)
    }

    pub fn deserialize<'de, D, V>(deserializer: D) -> Result<V, D::Error>
    where
        D: Deserializer<'de>,
        V: FromStr,
    {
        struct Visitor<V> {
            _val: PhantomData<V>,
        }
        impl<'de, V> serde::de::Visitor<'de> for Visitor<V>
        where
            V: FromStr,
        {
            type Value = V;
            fn expecting(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
                write!(f, "ScalarValue value")
            }
            fn visit_str<E>(self, v: &str) -> Result<Self::Value, E>
            where
                E: Error,
            {
                v.parse()
                    .map_err(|_| E::custom("Could not parse 128 bit integer!"))
            }
        }
        deserializer.deserialize_str(Visitor { _val: PhantomData })
    }

    /// Stateful variant for types that derive `DeserializeState`: the state is irrelevant for a
    /// scalar, so we delegate to the stateless [`deserialize`].
    pub fn deserialize_state<'de, D, State: ?Sized, V>(
        _state: &State,
        deserializer: D,
    ) -> Result<V, D::Error>
    where
        D: Deserializer<'de>,
        V: FromStr,
    {
        deserialize(deserializer)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_big_endian_scalars() {
        let u128 = 0x12345678901234567890123456789012u128;
        let le_bytes = u128.to_le_bytes();

        let le_scalar = ScalarValue::from_le_bytes(IntegerTy::Unsigned(UIntTy::U128), le_bytes);
        assert_eq!(le_scalar, ScalarValue::Unsigned(UIntTy::U128, u128));

        let i64 = 0x1234567890123456i64;
        let le_bytes = (i64 as i128).to_le_bytes();
        let le_scalar = ScalarValue::from_le_bytes(IntegerTy::Signed(IntTy::I64), le_bytes);
        assert_eq!(le_scalar, ScalarValue::Signed(IntTy::I64, i64 as i128));
    }
}
