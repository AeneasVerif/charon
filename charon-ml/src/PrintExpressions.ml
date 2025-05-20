(** Pretty-printing for expressions *)

open Types
open Expressions
open LlbcAst
open PrintUtils
open PrintTypes

let fun_decl_id_to_string = PrintTypes.fun_decl_id_to_string

let local_id_to_pretty_string (id : local_id) : string =
  "v@" ^ LocalId.to_string id

let local_to_string (v : local) : string =
  match v.name with
  | None -> local_id_to_pretty_string v.index
  | Some name -> name ^ "^" ^ LocalId.to_string v.index

let local_id_to_string (env : 'a fmt_env) (id : LocalId.id) : string =
  match List.find_opt (fun (i, _) -> i = id) env.locals with
  | None -> local_id_to_pretty_string id
  | Some (_, name) -> (
      match name with
      | None -> local_id_to_pretty_string id
      | Some name -> name ^ "^" ^ LocalId.to_string id)

let (var_id_to_pretty_string
    [@ocaml.alert deprecated "use [local_id_to_pretty_string] instead"]) =
  local_id_to_pretty_string

let (var_id_to_string
    [@ocaml.alert deprecated "use [local_id_to_string] instead"]) =
  local_id_to_string

let (var_to_string [@ocaml.alert deprecated "use [local_to_string] instead"]) =
  local_to_string

let rec projection_elem_to_string (env : 'a fmt_env) (sub : string)
    (pe : projection_elem) : string =
  match pe with
  | Deref -> "*(" ^ sub ^ ")"
  | ProjIndex (off, from_end) ->
      let idx_pre = if from_end then "-" else "" in
      "(" ^ sub ^ ")[" ^ idx_pre ^ operand_to_string env off ^ "]"
  | Subslice (from, to_, from_end) ->
      let idx_pre = if from_end then "-" else "" in
      "(" ^ sub ^ ")[" ^ idx_pre ^ operand_to_string env from ^ ".."
      ^ operand_to_string env to_ ^ "]"
  | Field (ProjTuple _, fid) -> "(" ^ sub ^ ")." ^ FieldId.to_string fid
  | Field (ProjAdt (adt_id, opt_variant_id), fid) -> (
      let field_name =
        match adt_field_to_string env adt_id opt_variant_id fid with
        | Some field_name -> field_name
        | None -> FieldId.to_string fid
      in
      match opt_variant_id with
      | None -> "(" ^ sub ^ ")." ^ field_name
      | Some variant_id ->
          let variant_name = adt_variant_to_string env adt_id variant_id in
          "(" ^ sub ^ " as " ^ variant_name ^ ")." ^ field_name)

and place_to_string (env : 'a fmt_env) (p : place) : string =
  match p.kind with
  | PlaceLocal var_id -> local_id_to_string env var_id
  | PlaceProjection (subplace, pe) ->
      let subplace = place_to_string env subplace in
      projection_elem_to_string env subplace pe

and cast_kind_to_string (env : 'a fmt_env) (cast : cast_kind) : string =
  match cast with
  | CastScalar (src, tgt) ->
      "cast<" ^ literal_type_to_string src ^ "," ^ literal_type_to_string tgt
      ^ ">"
  | CastFnPtr (src, tgt) | CastRawPtr (src, tgt) | CastTransmute (src, tgt) ->
      "cast<" ^ ty_to_string env src ^ "," ^ ty_to_string env tgt ^ ">"
  | CastUnsize (src, tgt) ->
      "unsize<" ^ ty_to_string env src ^ "," ^ ty_to_string env tgt ^ ">"

and nullop_to_string (env : 'a fmt_env) (op : nullop) : string =
  match op with
  | SizeOf -> "size_of"
  | AlignOf -> "align_of"
  | OffsetOf _ -> "offset_of(?)"
  | UbChecks -> "ub_checks"

and unop_to_string (env : 'a fmt_env) (unop : unop) : string =
  match unop with
  | Not -> "¬"
  | Neg -> "-"
  | PtrMetadata -> "ptr_metadata"
  | Cast cast_kind -> cast_kind_to_string env cast_kind
  | ArrayToSlice _ -> "to_slice"

and binop_to_string (binop : binop) : string =
  match binop with
  | BitXor -> "^"
  | BitAnd -> "&"
  | BitOr -> "|"
  | Eq -> "=="
  | Lt -> "<"
  | Le -> "<="
  | Ne -> "!="
  | Ge -> ">="
  | Gt -> ">"
  | Div -> "/"
  | Rem -> "%"
  | Add -> "+"
  | Sub -> "-"
  | Mul -> "*"
  | WrappingAdd -> "wrapping.+"
  | WrappingSub -> "wrapping.-"
  | WrappingMul -> "wrapping.*"
  | CheckedAdd -> "checked.+"
  | CheckedSub -> "checked.-"
  | CheckedMul -> "checked.*"
  | Shl -> "<<"
  | Shr -> ">>"
  | Cmp -> "cmp"
  | Offset -> "offset"

and builtin_fun_id_to_string (aid : builtin_fun_id) : string =
  match aid with
  | BoxNew -> "alloc::boxed::Box::new"
  | ArrayToSliceShared -> "@ArrayToSliceShared"
  | ArrayToSliceMut -> "@ArrayToSliceMut"
  | ArrayRepeat -> "@ArrayRepeat"
  | Index { is_array; mutability; is_range } ->
      let ty = if is_array then "Array" else "Slice" in
      let op = if is_range then "SubSlice" else "Index" in
      let mutability = ref_kind_to_string mutability in
      "@" ^ ty ^ op ^ mutability
  | PtrFromParts mut ->
      let mut = if mut = RMut then "Mut" else "" in
      "@PtrFromParts" ^ mut

and fun_id_to_string (env : 'a fmt_env) (fid : fun_id) : string =
  match fid with
  | FRegular fid -> fun_decl_id_to_string env fid
  | FBuiltin aid -> builtin_fun_id_to_string aid

and fun_id_or_trait_method_ref_to_string (env : 'a fmt_env)
    (r : fun_id_or_trait_method_ref) : string =
  match r with
  | TraitMethod (trait_ref, method_name, _) ->
      trait_ref_to_string env trait_ref ^ "::" ^ method_name
  | FunId fid -> fun_id_to_string env fid

and fn_ptr_to_string (env : 'a fmt_env) (ptr : fn_ptr) : string =
  let generics = generic_args_to_string env ptr.generics in
  fun_id_or_trait_method_ref_to_string env ptr.func ^ generics

and constant_expr_to_string (env : 'a fmt_env) (cv : constant_expr) : string =
  match cv.value with
  | CLiteral lit ->
      "(" ^ literal_to_string lit ^ " : " ^ ty_to_string env cv.ty ^ ")"
  | CVar var -> const_generic_db_var_to_string env var
  | CTraitConst (trait_ref, const_name) ->
      let trait_ref = trait_ref_to_string env trait_ref in
      trait_ref ^ const_name
  | CFnPtr fn_ptr -> fn_ptr_to_string env fn_ptr
  | CRawMemory bytes ->
      "RawMemory([" ^ String.concat ", " (List.map string_of_int bytes) ^ "])"
  | COpaque reason -> "Opaque(" ^ reason ^ ")"

and operand_to_string (env : 'a fmt_env) (op : operand) : string =
  match op with
  | Copy p -> "copy " ^ place_to_string env p
  | Move p -> "move " ^ place_to_string env p
  | Constant cv -> constant_expr_to_string env cv

and rvalue_to_string (env : 'a fmt_env) (rv : rvalue) : string =
  match rv with
  | Use op -> operand_to_string env op
  | RvRef (p, bk) -> begin
      let p = place_to_string env p in
      match bk with
      | BShared -> "&" ^ p
      | BMut -> "&mut " ^ p
      | BTwoPhaseMut -> "&two-phase " ^ p
      | BUniqueImmutable -> "&uniq " ^ p
      | BShallow -> "&shallow " ^ p
    end
  | RawPtr (p, pk) -> begin
      let p = place_to_string env p in
      match pk with
      | RShared -> "&raw const " ^ p
      | RMut -> "&raw mut " ^ p
    end
  | NullaryOp (op, ty) ->
      nullop_to_string env op ^ "<" ^ ty_to_string env ty ^ ">"
  | UnaryOp (unop, op) ->
      unop_to_string env unop ^ " " ^ operand_to_string env op
  | BinaryOp (binop, op1, op2) ->
      operand_to_string env op1 ^ " " ^ binop_to_string binop ^ " "
      ^ operand_to_string env op2
  | Discriminant (p, _) -> "discriminant(" ^ place_to_string env p ^ ")"
  | Len (place, ty, const_generics) ->
      let const_generics =
        match const_generics with
        | None -> []
        | Some cg -> [ cg ]
      in
      "len<"
      ^ String.concat ", "
          (ty_to_string env ty
          :: List.map (const_generic_to_string env) const_generics)
      ^ ">(" ^ place_to_string env place ^ ")"
  | Global global_ref ->
      let generics = generic_args_to_string env global_ref.global_generics in
      "global " ^ global_decl_id_to_string env global_ref.global_id ^ generics
  | GlobalRef (global_ref, RShared) ->
      let generics = generic_args_to_string env global_ref.global_generics in
      "&global " ^ global_decl_id_to_string env global_ref.global_id ^ generics
  | GlobalRef (global_ref, RMut) ->
      let generics = generic_args_to_string env global_ref.global_generics in
      "&raw mut global "
      ^ global_decl_id_to_string env global_ref.global_id
      ^ generics
  | Repeat (v, _, len) ->
      "[" ^ operand_to_string env v ^ ";"
      ^ const_generic_to_string env len
      ^ "]"
  | ShallowInitBox (op, _) ->
      "shallow-init-box(" ^ operand_to_string env op ^ ")"
  | Aggregate (akind, ops) -> (
      let ops = List.map (operand_to_string env) ops in
      match akind with
      | AggregatedAdt (type_id, opt_variant_id, opt_field_id, _generics) -> (
          match type_id with
          | TTuple -> "(" ^ String.concat ", " ops ^ ")"
          | TAdtId def_id ->
              let adt_name = type_decl_id_to_string env def_id in
              let variant_name =
                match opt_variant_id with
                | None -> adt_name
                | Some variant_id ->
                    adt_name ^ "::"
                    ^ adt_variant_to_string env def_id variant_id
              in
              let fields =
                match adt_field_names env def_id opt_variant_id with
                | None -> "(" ^ String.concat ", " ops ^ ")"
                | Some field_names ->
                    let field_names =
                      match opt_field_id with
                      | None -> field_names
                      (* Only keep the selected field *)
                      | Some field_id ->
                          [ List.nth field_names (FieldId.to_int field_id) ]
                    in
                    let fields = List.combine field_names ops in
                    let fields =
                      List.map
                        (fun (field, value) -> field ^ " = " ^ value ^ ";")
                        fields
                    in
                    let fields = String.concat " " fields in
                    "{ " ^ fields ^ " }"
              in
              variant_name ^ " " ^ fields
          | TBuiltin _ -> raise (Failure "Unreachable"))
      | AggregatedArray (_ty, _cg) -> "[" ^ String.concat ", " ops ^ "]"
      | AggregatedRawPtr (_, refk) ->
          let refk =
            match refk with
            | RMut -> "*mut"
            | RShared -> "*const"
          in
          refk ^ " (" ^ String.concat ", " ops ^ ")"
      | AggregatedClosure (fid, generics) ->
          "{"
          ^ fun_decl_id_to_string env fid
          ^ generic_args_to_string env generics
          ^ "}" ^ " {" ^ String.concat ", " ops ^ "}")
