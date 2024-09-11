(** Pretty-printing for primitive values *)

open Values
open Types

let integer_type_to_string = function
  | Isize -> "isize"
  | I8 -> "i8"
  | I16 -> "i16"
  | I32 -> "i32"
  | I64 -> "i64"
  | I128 -> "i128"
  | Usize -> "usize"
  | U8 -> "u8"
  | U16 -> "u16"
  | U32 -> "u32"
  | U64 -> "u64"
  | U128 -> "u128"

let float_type_to_string = function
  | F16 -> "f16"
  | F32 -> "f32"
  | F64 -> "f64"
  | F128 -> "f128"

let literal_type_to_string (ty : literal_type) : string =
  match ty with
  | TInteger ity -> integer_type_to_string ity
  | TFloat fty -> float_type_to_string fty
  | TBool -> "bool"
  | TChar -> "char"

let big_int_to_string (bi : big_int) : string = Z.to_string bi

let scalar_value_to_string (sv : scalar_value) : string =
  big_int_to_string sv.value ^ ": " ^ integer_type_to_string sv.int_ty

let float_value_to_string (fv : float_value) : string =
  fv.float_value ^ ": " ^ float_type_to_string fv.float_ty

let literal_to_string (lit : literal) : string =
  match lit with
  | VScalar sv -> scalar_value_to_string sv
  | VFloat fv -> float_value_to_string fv
  | VBool b -> Bool.to_string b
  | VChar c -> String.make 1 c
  | VStr s -> "\"" ^ s ^ "\""
  | VByteStr bs -> "[" ^ String.concat ", " (List.map string_of_int bs) ^ "]"
