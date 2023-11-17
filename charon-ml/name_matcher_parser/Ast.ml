type type_var = int
type region = int
type const_generic_var = int
type const_generic = CgVar of const_generic_var option | CgConst of int
type ref_kind = RMut | RShared

type name_elem = Ident of string | Impl of ty
and name = name_elem list
and adt_id = TName of name | TArray | TSlice

and ty =
  | TTy of adt_id * generic_args  (** Adt, primitive type, etc. *)
  | TVar of int option
  | TRef of region option * ty * ref_kind

and generic_arg =
  | GRegion of region option
  | GType of ty
  | GConstGeneric of const_generic

and generic_args = generic_arg list

type inst_name = { name : name; generics : generic_args }
