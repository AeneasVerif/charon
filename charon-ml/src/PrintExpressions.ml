(** Pretty-printing for expressions *)

open Types
open Expressions
open LlbcAst
open PrintUtils
open PrintTypes

let fun_decl_id_to_string = PrintTypes.fun_decl_id_to_string
let var_id_to_pretty_string (id : var_id) : string = "v@" ^ VarId.to_string id

let var_to_string (v : var) : string =
  match v.name with
  | None -> var_id_to_pretty_string v.index
  | Some name -> name ^ "^" ^ VarId.to_string v.index

let var_id_to_string (env : ('a, 'b) fmt_env) (id : VarId.id) : string =
  match List.find_opt (fun (i, _) -> i = id) env.locals with
  | None -> var_id_to_pretty_string id
  | Some (_, name) -> (
      match name with
      | None -> var_id_to_pretty_string id
      | Some name -> name ^ "^" ^ VarId.to_string id)

let rec projection_to_string (env : ('a, 'b) fmt_env) (s : string)
    (p : projection) : string =
  match p with
  | [] -> s
  | pe :: p' ->
      let s =
        match pe with
        | Deref -> "*(" ^ s ^ ")"
        | DerefBox -> "deref_box(" ^ s ^ ")"
        | Field (ProjTuple _, fid) -> "(" ^ s ^ ")." ^ FieldId.to_string fid
        | Field (ProjAdt (adt_id, opt_variant_id), fid) -> (
            let field_name =
              match adt_field_to_string env adt_id opt_variant_id fid with
              | Some field_name -> field_name
              | None -> FieldId.to_string fid
            in
            match opt_variant_id with
            | None -> "(" ^ s ^ ")." ^ field_name
            | Some variant_id ->
                let variant_name =
                  adt_variant_to_string env adt_id variant_id
                in
                "(" ^ s ^ " as " ^ variant_name ^ ")." ^ field_name)
      in
      projection_to_string env s p'

let place_to_string (env : ('a, 'b) fmt_env) (p : place) : string =
  let var = var_id_to_string env p.var_id in
  projection_to_string env var p.projection

let cast_kind_to_string (env : ('a, 'b) fmt_env) (cast : cast_kind) : string =
  match cast with
  | CastScalar (src, tgt) ->
      "cast<" ^ literal_type_to_string src ^ "," ^ literal_type_to_string tgt
      ^ ">"
  | CastFnPtr (src, tgt) | CastRawPtr (src, tgt) | CastTransmute (src, tgt) ->
      "cast<" ^ ty_to_string env src ^ "," ^ ty_to_string env tgt ^ ">"
  | CastUnsize (src, tgt) ->
      "unsize<" ^ ty_to_string env src ^ "," ^ ty_to_string env tgt ^ ">"

let nullop_to_string (env : ('a, 'b) fmt_env) (op : nullop) : string =
  match op with
  | SizeOf -> "size_of"
  | AlignOf -> "align_of"
  | OffsetOf _ -> "offset_of(?)"
  | UbChecks -> "ub_checks"

let unop_to_string (env : ('a, 'b) fmt_env) (unop : unop) : string =
  match unop with
  | Not -> "¬"
  | Neg -> "-"
  | Cast cast_kind -> cast_kind_to_string env cast_kind

let binop_to_string (binop : binop) : string =
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
  | CheckedAdd -> "checked.+"
  | CheckedSub -> "checked.-"
  | CheckedMul -> "checked.*"
  | Shl -> "<<"
  | Shr -> ">>"

let assumed_fun_id_to_string (aid : assumed_fun_id) : string =
  match aid with
  | BoxNew -> "alloc::boxed::Box::new"
  | BoxFree -> "alloc::alloc::box_free"
  | ArrayIndexShared -> "@ArrayIndexShared"
  | ArrayIndexMut -> "@ArrayIndexMut"
  | ArrayToSliceShared -> "@ArrayToSliceShared"
  | ArrayToSliceMut -> "@ArrayToSliceMut"
  | ArrayRepeat -> "@ArrayRepeat"
  | SliceIndexShared -> "@SliceIndexShared"
  | SliceIndexMut -> "@SliceIndexMut"

let fun_id_to_string (env : ('a, 'b) fmt_env) (fid : fun_id) : string =
  match fid with
  | FRegular fid -> fun_decl_id_to_string env fid
  | FAssumed aid -> assumed_fun_id_to_string aid

let fun_id_or_trait_method_ref_to_string (env : ('a, 'b) fmt_env)
    (r : fun_id_or_trait_method_ref) : string =
  match r with
  | TraitMethod (trait_ref, method_name, _) ->
      trait_ref_to_string env trait_ref ^ "::" ^ method_name
  | FunId fid -> fun_id_to_string env fid

let fn_ptr_to_string (env : ('a, 'b) fmt_env) (ptr : fn_ptr) : string =
  let generics = generic_args_to_string env ptr.generics in
  fun_id_or_trait_method_ref_to_string env ptr.func ^ generics

let constant_expr_to_string (env : ('a, 'b) fmt_env) (cv : constant_expr) :
    string =
  match cv.value with
  | CLiteral lit ->
      "(" ^ literal_to_string lit ^ " : " ^ ty_to_string env cv.ty ^ ")"
  | CVar vid -> const_generic_var_id_to_string env vid
  | CTraitConst (trait_ref, const_name) ->
      let trait_ref = trait_ref_to_string env trait_ref in
      trait_ref ^ const_name
  | CFnPtr fn_ptr -> fn_ptr_to_string env fn_ptr

let operand_to_string (env : ('a, 'b) fmt_env) (op : operand) : string =
  match op with
  | Copy p -> "copy " ^ place_to_string env p
  | Move p -> "move " ^ place_to_string env p
  | Constant cv -> constant_expr_to_string env cv

let rvalue_to_string (env : ('a, 'b) fmt_env) (rv : rvalue) : string =
  match rv with
  | Use op -> operand_to_string env op
  | RvRef (p, bk) -> begin
      let p = place_to_string env p in
      match bk with
      | BShared -> "&" ^ p
      | BMut -> "&mut " ^ p
      | BTwoPhaseMut -> "&two-phase " ^ p
      | BShallow -> "&shallow " ^ p
    end
  | RawPtr (p, pk) -> begin
      let p = place_to_string env p in
      match pk with RShared -> "&raw const " ^ p | RMut -> "&raw mut " ^ p
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
        match const_generics with None -> [] | Some cg -> [ cg ]
      in
      "len<"
      ^ String.concat ", "
          (ty_to_string env ty
          :: List.map (const_generic_to_string env) const_generics)
      ^ ">(" ^ place_to_string env place ^ ")"
  | Global global_ref ->
      let generics = generic_args_to_string env global_ref.global_generics in
      "global " ^ global_decl_id_to_string env global_ref.global_id ^ generics
  | ShallowInitBox (op, ty) ->
      "shallow_init_box<" ^ ty_to_string env ty ^ ">("
      ^ operand_to_string env op ^ ")"
  | Aggregate (akind, ops) -> (
      let ops = List.map (operand_to_string env) ops in
      match akind with
      | AggregatedAdt (type_id, opt_variant_id, _generics) -> (
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
          | TAssumed _ -> raise (Failure "Unreachable"))
      | AggregatedArray (_ty, _cg) -> "[" ^ String.concat ", " ops ^ "]"
      | AggregatedClosure (fid, generics) ->
          "{"
          ^ fun_decl_id_to_string env fid
          ^ generic_args_to_string env generics
          ^ "}" ^ " {" ^ String.concat ", " ops ^ "}")
