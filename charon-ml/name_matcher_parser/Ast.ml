type integer_type =
  | Isize
  | I8
  | I16
  | I32
  | I64
  | I128
  | Usize
  | U8
  | U16
  | U32
  | U64
  | U128

type literal_type = TInteger of integer_type | TBool | TChar
type type_var = int
type region = int
type const_generic_var = int
type const_generic = CgVar of const_generic_var option | CgConst of int
type ref_kind = RMut | RShared
type assumed_ty = TBox | TArray | TSlice

type name_elem = Ident of string | Impl of ty
and name = name_elem list
and adt_id = TAdtId of name | TAssumed of assumed_ty

and ty =
  | TAdt of adt_id * generic_args
  | TLiteral of literal_type
  | TVar of int option
  | TRef of region option * ty * ref_kind

and generic_arg =
  | GRegion of region
  | GType of ty
  | GConstGeneric of const_generic

and generic_args = generic_arg list
