(** Pretty-printing for expressions *)

module T = Types
module TU = TypesUtils
module E = Expressions
module A = LlbcAst
open PrintUtils
module PT = PrintTypes
module PPV = PrintPrimitiveValues

let var_id_to_string (id : E.VarId.id) : string = "v@" ^ E.VarId.to_string id

type expr_formatter = {
  rvar_to_string : T.RegionVarId.id -> string;
  r_to_string : T.RegionId.id -> string;
  type_var_id_to_string : T.TypeVarId.id -> string;
  type_decl_id_to_string : T.TypeDeclId.id -> string;
  const_generic_var_id_to_string : T.ConstGenericVarId.id -> string;
  adt_variant_to_string : T.TypeDeclId.id -> T.VariantId.id -> string;
  adt_field_to_string :
    T.TypeDeclId.id -> T.VariantId.id option -> T.FieldId.id -> string option;
  var_id_to_string : E.VarId.id -> string;
  adt_field_names :
    T.TypeDeclId.id -> T.VariantId.id option -> string list option;
  fun_decl_id_to_string : A.FunDeclId.id -> string;
  global_decl_id_to_string : A.GlobalDeclId.id -> string;
  trait_decl_id_to_string : T.TraitDeclId.id -> string;
  trait_impl_id_to_string : T.TraitImplId.id -> string;
  trait_clause_id_to_string : T.TraitClauseId.id -> string;
}

let expr_to_etype_formatter (fmt : expr_formatter) : PT.etype_formatter =
  {
    PT.r_to_string = PT.erased_region_to_string;
    PT.type_var_id_to_string = fmt.type_var_id_to_string;
    PT.type_decl_id_to_string = fmt.type_decl_id_to_string;
    PT.const_generic_var_id_to_string = fmt.const_generic_var_id_to_string;
    PT.global_decl_id_to_string = fmt.global_decl_id_to_string;
    PT.trait_decl_id_to_string = fmt.trait_decl_id_to_string;
    PT.trait_impl_id_to_string = fmt.trait_impl_id_to_string;
    PT.trait_clause_id_to_string = fmt.trait_clause_id_to_string;
  }

let expr_to_rtype_formatter (fmt : expr_formatter) : PT.rtype_formatter =
  {
    PT.r_to_string = PT.region_to_string fmt.r_to_string;
    PT.type_var_id_to_string = fmt.type_var_id_to_string;
    PT.type_decl_id_to_string = fmt.type_decl_id_to_string;
    PT.const_generic_var_id_to_string = fmt.const_generic_var_id_to_string;
    PT.global_decl_id_to_string = fmt.global_decl_id_to_string;
    PT.trait_decl_id_to_string = fmt.trait_decl_id_to_string;
    PT.trait_impl_id_to_string = fmt.trait_impl_id_to_string;
    PT.trait_clause_id_to_string = fmt.trait_clause_id_to_string;
  }

let expr_to_stype_formatter (fmt : expr_formatter) : PT.stype_formatter =
  {
    PT.r_to_string = PT.region_to_string fmt.rvar_to_string;
    PT.type_var_id_to_string = fmt.type_var_id_to_string;
    PT.type_decl_id_to_string = fmt.type_decl_id_to_string;
    PT.const_generic_var_id_to_string = fmt.const_generic_var_id_to_string;
    PT.global_decl_id_to_string = fmt.global_decl_id_to_string;
    PT.trait_decl_id_to_string = fmt.trait_decl_id_to_string;
    PT.trait_impl_id_to_string = fmt.trait_impl_id_to_string;
    PT.trait_clause_id_to_string = fmt.trait_clause_id_to_string;
  }

let rec projection_to_string (fmt : expr_formatter) (s : string)
    (p : E.projection) : string =
  match p with
  | [] -> s
  | pe :: p' ->
      let s =
        match pe with
        | E.Deref -> "*(" ^ s ^ ")"
        | E.DerefBox -> "deref_box(" ^ s ^ ")"
        | E.Field (E.ProjOption variant_id, fid) ->
            assert (variant_id = T.option_some_id);
            assert (fid = T.FieldId.zero);
            "(" ^ s ^ " as Option::Some)." ^ T.FieldId.to_string fid
        | E.Field (E.ProjTuple _, fid) ->
            "(" ^ s ^ ")." ^ T.FieldId.to_string fid
        | E.Field (E.ProjAdt (adt_id, opt_variant_id), fid) -> (
            let field_name =
              match fmt.adt_field_to_string adt_id opt_variant_id fid with
              | Some field_name -> field_name
              | None -> T.FieldId.to_string fid
            in
            match opt_variant_id with
            | None -> "(" ^ s ^ ")." ^ field_name
            | Some variant_id ->
                let variant_name =
                  fmt.adt_variant_to_string adt_id variant_id
                in
                "(" ^ s ^ " as " ^ variant_name ^ ")." ^ field_name)
      in
      projection_to_string fmt s p'

let place_to_string (fmt : expr_formatter) (p : E.place) : string =
  let var = fmt.var_id_to_string p.E.var_id in
  projection_to_string fmt var p.E.projection

let cast_kind_to_string (_fmt : expr_formatter) (cast : E.cast_kind) : string =
  match cast with
  | CastInteger (src, tgt) ->
      "cast<"
      ^ PPV.integer_type_to_string src
      ^ ","
      ^ PPV.integer_type_to_string tgt
      ^ ">"

let unop_to_string (fmt : expr_formatter) (unop : E.unop) : string =
  match unop with
  | E.Not -> "¬"
  | E.Neg -> "-"
  | E.Cast cast_kind -> cast_kind_to_string fmt cast_kind

let binop_to_string (binop : E.binop) : string =
  match binop with
  | E.BitXor -> "^"
  | E.BitAnd -> "&"
  | E.BitOr -> "|"
  | E.Eq -> "=="
  | E.Lt -> "<"
  | E.Le -> "<="
  | E.Ne -> "!="
  | E.Ge -> ">="
  | E.Gt -> ">"
  | E.Div -> "/"
  | E.Rem -> "%"
  | E.Add -> "+"
  | E.Sub -> "-"
  | E.Mul -> "*"
  | E.Shl -> "<<"
  | E.Shr -> ">>"

let assumed_fun_id_to_string (aid : E.assumed_fun_id) (generics : string) :
    string =
  match aid with
  | BoxNew -> "alloc::boxed::Box" ^ generics ^ "::new"
  | BoxFree -> "alloc::alloc::box_free" ^ generics
  | ArrayIndexShared -> "@ArrayIndexShared" ^ generics
  | ArrayIndexMut -> "@ArrayIndexMut" ^ generics
  | ArrayToSliceShared -> "@ArrayToSliceShared" ^ generics
  | ArrayToSliceMut -> "@ArrayToSliceMut" ^ generics
  | ArrayRepeat -> "@ArrayRepeat" ^ generics
  | SliceLen -> "@SliceLen" ^ generics
  | SliceIndexShared -> "@SliceIndexShared" ^ generics
  | SliceIndexMut -> "@SliceIndexMut" ^ generics

let fun_id_or_trait_method_ref_to_string (fmt : expr_formatter)
    (r : E.fun_id_or_trait_method_ref) (generics : string) : string =
  let ty_fmt = expr_to_etype_formatter fmt in
  match r with
  | TraitMethod (trait_ref, method_name, _) ->
      PT.trait_ref_to_string ty_fmt trait_ref ^ "::" ^ method_name ^ generics
  | FunId (Regular fid) -> fmt.fun_decl_id_to_string fid ^ generics
  | FunId (Assumed aid) -> assumed_fun_id_to_string aid generics

let fn_ptr_to_string (fmt : expr_formatter) (ptr : E.fn_ptr) : string =
  let ty_fmt = expr_to_etype_formatter fmt in
  let generics = PT.generic_args_to_string ty_fmt ptr.generics in
  fun_id_or_trait_method_ref_to_string fmt ptr.func generics

let constant_expr_to_string (fmt : expr_formatter) (cv : E.constant_expr) :
    string =
  match cv.E.value with
  | E.CLiteral lit ->
      "(" ^ PPV.literal_to_string lit ^ " : "
      ^ PT.ety_to_string (expr_to_etype_formatter fmt) cv.E.ty
      ^ ")"
  | E.CVar vid -> fmt.const_generic_var_id_to_string vid
  | E.CTraitConst (trait_ref, generics, const_name) ->
      let fmt = expr_to_etype_formatter fmt in
      let trait_ref = PT.etrait_ref_to_string fmt trait_ref in
      let generics = PT.egeneric_args_to_string fmt generics in
      trait_ref ^ generics ^ const_name
  | E.CFnPtr fn_ptr -> fn_ptr_to_string fmt fn_ptr

let operand_to_string (fmt : expr_formatter) (op : E.operand) : string =
  match op with
  | E.Copy p -> "copy " ^ place_to_string fmt p
  | E.Move p -> "move " ^ place_to_string fmt p
  | E.Constant cv -> constant_expr_to_string fmt cv

let rvalue_to_string (fmt : expr_formatter) (rv : E.rvalue) : string =
  match rv with
  | E.Use op -> operand_to_string fmt op
  | E.RvRef (p, bk) -> (
      let p = place_to_string fmt p in
      match bk with
      | E.Shared -> "&" ^ p
      | E.Mut -> "&mut " ^ p
      | E.TwoPhaseMut -> "&two-phase " ^ p
      | E.Shallow -> "&shallow " ^ p)
  | E.UnaryOp (unop, op) ->
      unop_to_string fmt unop ^ " " ^ operand_to_string fmt op
  | E.BinaryOp (binop, op1, op2) ->
      operand_to_string fmt op1 ^ " " ^ binop_to_string binop ^ " "
      ^ operand_to_string fmt op2
  | E.Discriminant p -> "discriminant(" ^ place_to_string fmt p ^ ")"
  | E.Global gid -> "global " ^ fmt.global_decl_id_to_string gid
  | E.Aggregate (akind, ops) -> (
      let ops = List.map (operand_to_string fmt) ops in
      match akind with
      | E.AggregatedAdt (type_id, opt_variant_id, _generics) -> (
          match type_id with
          | Tuple -> "(" ^ String.concat ", " ops ^ ")"
          | AdtId def_id ->
              let adt_name = fmt.type_decl_id_to_string def_id in
              let variant_name =
                match opt_variant_id with
                | None -> adt_name
                | Some variant_id ->
                    adt_name ^ "::"
                    ^ fmt.adt_variant_to_string def_id variant_id
              in
              let fields =
                match fmt.adt_field_names def_id opt_variant_id with
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
          | Assumed _ -> raise (Failure "Unreachable"))
      | E.AggregatedArray (_ty, _cg) -> "[" ^ String.concat ", " ops ^ "]")
