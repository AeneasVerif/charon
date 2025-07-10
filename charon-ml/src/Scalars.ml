open Values

(** The minimum/maximum values an integer type can have depending on its type *)

let i8_min = Z.of_string "-128"
let i8_max = Z.of_string "127"
let i16_min = Z.of_string "-32768"
let i16_max = Z.of_string "32767"
let i32_min = Z.of_string "-2147483648"
let i32_max = Z.of_string "2147483647"
let i64_min = Z.of_string "-9223372036854775808"
let i64_max = Z.of_string "9223372036854775807"
let i128_min = Z.of_string "-170141183460469231731687303715884105728"
let i128_max = Z.of_string "170141183460469231731687303715884105727"
let u8_min = Z.of_string "0"
let u8_max = Z.of_string "255"
let u16_min = Z.of_string "0"
let u16_max = Z.of_string "65535"
let u32_min = Z.of_string "0"
let u32_max = Z.of_string "4294967295"
let u64_min = Z.of_string "0"
let u64_max = Z.of_string "18446744073709551615"
let u128_min = Z.of_string "0"
let u128_max = Z.of_string "340282366920938463463374607431768211455"

(** The bounds for isize and usize vary with the architecture.

    Note that we use those bounds only to check that the values are *in range*
    when:
    - deserializing
    - using the interpreter in *concrete* mode and evaluating operations like
      addition, negation, etc. It is thus ok to not use the precise bounds. *)

let isize_min ptr_size =
  match ptr_size with
  | 8 -> i64_min
  | 4 -> i32_min
  | 2 -> i16_min
  | _ -> raise (Failure "Unsupported target pointer size")

let isize_max ptr_size =
  match ptr_size with
  | 8 -> i64_max
  | 4 -> i32_max
  | 2 -> i16_max
  | _ -> raise (Failure "Unsupported target pointer size")

let usize_min ptr_size =
  match ptr_size with
  | 8 -> u64_min
  | 4 -> u32_min
  | 2 -> u16_min
  | _ -> raise (Failure "Unsupported target pointer size")

let usize_max ptr_size =
  match ptr_size with
  | 8 -> u64_max
  | 4 -> u32_max
  | 2 -> u16_max
  | _ -> raise (Failure "Unsupported target pointer size")

let scalar_min ptr_size (int_ty : integer_type) : big_int =
  match int_ty with
  | Isize -> isize_min ptr_size
  | I8 -> i8_min
  | I16 -> i16_min
  | I32 -> i32_min
  | I64 -> i64_min
  | I128 -> i128_min
  | Usize -> usize_min ptr_size
  | U8 -> u8_min
  | U16 -> u16_min
  | U32 -> u32_min
  | U64 -> u64_min
  | U128 -> u128_min

let scalar_max ptr_size (int_ty : integer_type) : big_int =
  match int_ty with
  | Isize -> isize_max ptr_size
  | I8 -> i8_max
  | I16 -> i16_max
  | I32 -> i32_max
  | I64 -> i64_max
  | I128 -> i128_max
  | Usize -> usize_max ptr_size
  | U8 -> u8_max
  | U16 -> u16_max
  | U32 -> u32_max
  | U64 -> u64_max
  | U128 -> u128_max

(** Check that an integer value is in range *)
let check_int_in_range ptr_size (int_ty : integer_type) (i : big_int) : bool =
  Z.leq (scalar_min ptr_size int_ty) i && Z.leq i (scalar_max ptr_size int_ty)

(** Check that a scalar value is correct (the integer value it contains is in
    range) *)
let check_scalar_value_in_range ptr_size (v : scalar_value) : bool =
  check_int_in_range ptr_size v.int_ty v.value

(** Make a scalar value, while checking the value is in range *)
let mk_scalar ptr_size (int_ty : integer_type) (i : big_int) :
    (scalar_value, unit) result =
  if check_int_in_range ptr_size int_ty i then Ok { value = i; int_ty }
  else Error ()

let integer_type_is_signed (int_ty : integer_type) : bool =
  match int_ty with
  | Isize | I8 | I16 | I32 | I64 | I128 -> true
  | Usize | U8 | U16 | U32 | U64 | U128 -> false
