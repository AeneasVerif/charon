open Names
module T = Types
module TU = TypesUtils
module E = Expressions
module A = LlbcAst

let option_to_string (to_string : 'a -> string) (x : 'a option) : string =
  match x with Some x -> "Some (" ^ to_string x ^ ")" | None -> "None"

let name_to_string (name : name) : string = Names.name_to_string name
let fun_name_to_string (name : fun_name) : string = name_to_string name
let global_name_to_string (name : global_name) : string = name_to_string name

(** Pretty-printing for types *)
module Types = struct
  let type_var_to_string (tv : T.type_var) : string = tv.name

  let region_var_to_string (rv : T.region_var) : string =
    match rv.name with
    | Some name -> name
    | None -> T.RegionVarId.to_string rv.index

  let region_var_id_to_string (rid : T.RegionVarId.id) : string =
    "rv@" ^ T.RegionVarId.to_string rid

  let region_id_to_string (rid : T.RegionId.id) : string =
    "r@" ^ T.RegionId.to_string rid

  let region_to_string (rid_to_string : 'rid -> string) (r : 'rid T.region) :
      string =
    match r with Static -> "'static" | Var rid -> rid_to_string rid

  let erased_region_to_string (_ : T.erased_region) : string = "'_"

  let ref_kind_to_string (rk : T.ref_kind) : string =
    match rk with Mut -> "Mut" | Shared -> "Shared"

  let assumed_ty_to_string (_ : T.assumed_ty) : string = "Box"

  type 'r type_formatter = {
    r_to_string : 'r -> string;
    type_var_id_to_string : T.TypeVarId.id -> string;
    type_decl_id_to_string : T.TypeDeclId.id -> string;
  }

  type stype_formatter = T.RegionVarId.id T.region type_formatter
  type rtype_formatter = T.RegionId.id T.region type_formatter
  type etype_formatter = T.erased_region type_formatter

  let integer_type_to_string = function
    | T.Isize -> "isize"
    | T.I8 -> "i8"
    | T.I16 -> "i16"
    | T.I32 -> "i32"
    | T.I64 -> "i64"
    | T.I128 -> "i128"
    | T.Usize -> "usize"
    | T.U8 -> "u8"
    | T.U16 -> "u16"
    | T.U32 -> "u32"
    | T.U64 -> "u64"
    | T.U128 -> "u128"

  let type_id_to_string (fmt : 'r type_formatter) (id : T.type_id) : string =
    match id with
    | T.AdtId id -> fmt.type_decl_id_to_string id
    | T.Tuple -> ""
    | T.Assumed aty -> (
        match aty with
        | Box -> "alloc::boxed::Box"
        | Vec -> "alloc::vec::Vec"
        | Option -> "core::option::Option")

  let rec ty_to_string (fmt : 'r type_formatter) (ty : 'r T.ty) : string =
    match ty with
    | T.Adt (id, regions, tys) ->
        let is_tuple = match id with T.Tuple -> true | _ -> false in
        let params = params_to_string fmt is_tuple regions tys in
        type_id_to_string fmt id ^ params
    | T.TypeVar tv -> fmt.type_var_id_to_string tv
    | T.Bool -> "bool"
    | T.Char -> "char"
    | T.Never -> "⊥"
    | T.Integer int_ty -> integer_type_to_string int_ty
    | T.Str -> "str"
    | T.Array aty -> "[" ^ ty_to_string fmt aty ^ "; ?]"
    | T.Slice sty -> "[" ^ ty_to_string fmt sty ^ "]"
    | T.Ref (r, rty, ref_kind) -> (
        match ref_kind with
        | T.Mut ->
            "&" ^ fmt.r_to_string r ^ " mut (" ^ ty_to_string fmt rty ^ ")"
        | T.Shared ->
            "&" ^ fmt.r_to_string r ^ " (" ^ ty_to_string fmt rty ^ ")")

  and params_to_string (fmt : 'r type_formatter) (is_tuple : bool)
      (regions : 'r list) (types : 'r T.ty list) : string =
    let regions = List.map fmt.r_to_string regions in
    let types = List.map (ty_to_string fmt) types in
    let params = String.concat ", " (List.append regions types) in
    if is_tuple then "(" ^ params ^ ")"
    else if List.length regions + List.length types > 0 then "<" ^ params ^ ">"
    else ""

  let sty_to_string (fmt : stype_formatter) (ty : T.sty) : string =
    ty_to_string fmt ty

  let rty_to_string (fmt : rtype_formatter) (ty : T.rty) : string =
    ty_to_string fmt ty

  let ety_to_string (fmt : etype_formatter) (ty : T.ety) : string =
    ty_to_string fmt ty

  let field_to_string fmt (f : T.field) : string =
    match f.field_name with
    | Some field_name -> field_name ^ " : " ^ ty_to_string fmt f.field_ty
    | None -> ty_to_string fmt f.field_ty

  let variant_to_string fmt (v : T.variant) : string =
    v.variant_name ^ "("
    ^ String.concat ", " (List.map (field_to_string fmt) v.fields)
    ^ ")"

  let type_decl_to_string (type_decl_id_to_string : T.TypeDeclId.id -> string)
      (def : T.type_decl) : string =
    let regions = def.region_params in
    let types = def.type_params in
    let rid_to_string rid =
      match List.find_opt (fun rv -> rv.T.index = rid) regions with
      | Some rv -> region_var_to_string rv
      | None -> failwith "Unreachable"
    in
    let r_to_string = region_to_string rid_to_string in
    let type_var_id_to_string id =
      match List.find_opt (fun tv -> tv.T.index = id) types with
      | Some tv -> type_var_to_string tv
      | None -> failwith "Unreachable"
    in
    let fmt = { r_to_string; type_var_id_to_string; type_decl_id_to_string } in
    let name = name_to_string def.name in
    let params =
      if List.length regions + List.length types > 0 then
        let regions = List.map region_var_to_string regions in
        let types = List.map type_var_to_string types in
        let params = String.concat ", " (List.append regions types) in
        "<" ^ params ^ ">"
      else ""
    in
    match def.kind with
    | T.Struct fields ->
        if List.length fields > 0 then
          let fields =
            String.concat ","
              (List.map (fun f -> "\n  " ^ field_to_string fmt f) fields)
          in
          "struct " ^ name ^ params ^ "{" ^ fields ^ "}"
        else "struct " ^ name ^ params ^ "{}"
    | T.Enum variants ->
        let variants =
          List.map (fun v -> "|  " ^ variant_to_string fmt v) variants
        in
        let variants = String.concat "\n" variants in
        "enum " ^ name ^ params ^ " =\n" ^ variants
    | T.Opaque -> "opaque type " ^ name ^ params

  let type_ctx_to_adt_variant_to_string_fun
      (ctx : T.type_decl T.TypeDeclId.Map.t) :
      T.TypeDeclId.id -> T.VariantId.id -> string =
   fun def_id variant_id ->
    let def = T.TypeDeclId.Map.find def_id ctx in
    match def.kind with
    | Struct _ | Opaque -> failwith "Unreachable"
    | Enum variants ->
        let variant = T.VariantId.nth variants variant_id in
        name_to_string def.name ^ "::" ^ variant.variant_name

  let type_ctx_to_adt_field_names_fun (ctx : T.type_decl T.TypeDeclId.Map.t) :
      T.TypeDeclId.id -> T.VariantId.id option -> string list option =
   fun def_id opt_variant_id ->
    let def = T.TypeDeclId.Map.find def_id ctx in
    let fields = TU.type_decl_get_fields def opt_variant_id in
    (* There are two cases: either all the fields have names, or none of them
     * has names *)
    let has_names =
      List.exists (fun f -> Option.is_some f.T.field_name) fields
    in
    if has_names then
      let fields = List.map (fun f -> Option.get f.T.field_name) fields in
      Some fields
    else None

  let type_ctx_to_adt_field_to_string_fun (ctx : T.type_decl T.TypeDeclId.Map.t)
      :
      T.TypeDeclId.id -> T.VariantId.id option -> T.FieldId.id -> string option
      =
   fun def_id opt_variant_id field_id ->
    let def = T.TypeDeclId.Map.find def_id ctx in
    let fields = TU.type_decl_get_fields def opt_variant_id in
    let field = T.FieldId.nth fields field_id in
    field.T.field_name
end

module PT = Types (* local module *)

(** Pretty-printing for primitive values *)
module PrimitiveValues = struct
  open PrimitiveValues

  let big_int_to_string (bi : big_int) : string = Z.to_string bi

  let scalar_value_to_string (sv : scalar_value) : string =
    big_int_to_string sv.value ^ ": " ^ PT.integer_type_to_string sv.int_ty

  let primitive_value_to_string (cv : primitive_value) : string =
    match cv with
    | Scalar sv -> scalar_value_to_string sv
    | Bool b -> Bool.to_string b
    | Char c -> String.make 1 c
    | String s -> s
end

module PPV = PrimitiveValues (* local module *)

(** Pretty-printing for LLBC AST (generic functions) *)
module LlbcAst = struct
  let var_to_string (var : A.var) : string =
    match var.name with
    | None -> E.VarId.to_string var.index
    | Some name -> name

  let var_id_to_string (id : E.VarId.id) : string =
    "var@" ^ E.VarId.to_string id

  type ast_formatter = {
    rvar_to_string : T.RegionVarId.id -> string;
    r_to_string : T.RegionId.id -> string;
    type_var_id_to_string : T.TypeVarId.id -> string;
    type_decl_id_to_string : T.TypeDeclId.id -> string;
    adt_variant_to_string : T.TypeDeclId.id -> T.VariantId.id -> string;
    adt_field_to_string :
      T.TypeDeclId.id -> T.VariantId.id option -> T.FieldId.id -> string option;
    var_id_to_string : E.VarId.id -> string;
    adt_field_names :
      T.TypeDeclId.id -> T.VariantId.id option -> string list option;
    fun_decl_id_to_string : A.FunDeclId.id -> string;
    global_decl_id_to_string : A.GlobalDeclId.id -> string;
  }

  let ast_to_etype_formatter (fmt : ast_formatter) : PT.etype_formatter =
    {
      PT.r_to_string = PT.erased_region_to_string;
      PT.type_var_id_to_string = fmt.type_var_id_to_string;
      PT.type_decl_id_to_string = fmt.type_decl_id_to_string;
    }

  let ast_to_rtype_formatter (fmt : ast_formatter) : PT.rtype_formatter =
    {
      PT.r_to_string = PT.region_to_string fmt.r_to_string;
      PT.type_var_id_to_string = fmt.type_var_id_to_string;
      PT.type_decl_id_to_string = fmt.type_decl_id_to_string;
    }

  let ast_to_stype_formatter (fmt : ast_formatter) : PT.stype_formatter =
    {
      PT.r_to_string = PT.region_to_string fmt.rvar_to_string;
      PT.type_var_id_to_string = fmt.type_var_id_to_string;
      PT.type_decl_id_to_string = fmt.type_decl_id_to_string;
    }

  let fun_decl_to_ast_formatter (type_decls : T.type_decl T.TypeDeclId.Map.t)
      (fun_decls : A.fun_decl A.FunDeclId.Map.t)
      (global_decls : A.global_decl A.GlobalDeclId.Map.t) (fdef : A.fun_decl) :
      ast_formatter =
    let rvar_to_string r =
      let rvar = T.RegionVarId.nth fdef.signature.region_params r in
      PT.region_var_to_string rvar
    in
    let r_to_string r = PT.region_id_to_string r in

    let type_var_id_to_string vid =
      let var = T.TypeVarId.nth fdef.signature.type_params vid in
      PT.type_var_to_string var
    in
    let type_decl_id_to_string def_id =
      let def = T.TypeDeclId.Map.find def_id type_decls in
      name_to_string def.name
    in
    let adt_variant_to_string =
      PT.type_ctx_to_adt_variant_to_string_fun type_decls
    in
    let var_id_to_string vid =
      let var = E.VarId.nth (Option.get fdef.body).locals vid in
      var_to_string var
    in
    let adt_field_names = PT.type_ctx_to_adt_field_names_fun type_decls in
    let adt_field_to_string =
      PT.type_ctx_to_adt_field_to_string_fun type_decls
    in
    let fun_decl_id_to_string def_id =
      let def = A.FunDeclId.Map.find def_id fun_decls in
      fun_name_to_string def.name
    in
    let global_decl_id_to_string def_id =
      let def = A.GlobalDeclId.Map.find def_id global_decls in
      global_name_to_string def.name
    in
    {
      rvar_to_string;
      r_to_string;
      type_var_id_to_string;
      type_decl_id_to_string;
      adt_variant_to_string;
      var_id_to_string;
      adt_field_names;
      adt_field_to_string;
      fun_decl_id_to_string;
      global_decl_id_to_string;
    }

  let rec projection_to_string (fmt : ast_formatter) (inside : string)
      (p : E.projection) : string =
    match p with
    | [] -> inside
    | pe :: p' -> (
        let s = projection_to_string fmt inside p' in
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
                "(" ^ s ^ " as " ^ variant_name ^ ")." ^ field_name))

  let place_to_string (fmt : ast_formatter) (p : E.place) : string =
    let var = fmt.var_id_to_string p.E.var_id in
    projection_to_string fmt var p.E.projection

  let unop_to_string (unop : E.unop) : string =
    match unop with
    | E.Not -> "¬"
    | E.Neg -> "-"
    | E.Cast (src, tgt) ->
        "cast<"
        ^ PT.integer_type_to_string src
        ^ ","
        ^ PT.integer_type_to_string tgt
        ^ ">"

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

  let operand_to_string (fmt : ast_formatter) (op : E.operand) : string =
    match op with
    | E.Copy p -> "copy " ^ place_to_string fmt p
    | E.Move p -> "move " ^ place_to_string fmt p
    | E.Constant (ty, cv) ->
        "("
        ^ PPV.primitive_value_to_string cv
        ^ " : "
        ^ PT.ety_to_string (ast_to_etype_formatter fmt) ty
        ^ ")"

  let rvalue_to_string (fmt : ast_formatter) (rv : E.rvalue) : string =
    match rv with
    | E.Use op -> operand_to_string fmt op
    | E.Ref (p, bk) -> (
        let p = place_to_string fmt p in
        match bk with
        | E.Shared -> "&" ^ p
        | E.Mut -> "&mut " ^ p
        | E.TwoPhaseMut -> "&two-phase " ^ p)
    | E.UnaryOp (unop, op) ->
        unop_to_string unop ^ " " ^ operand_to_string fmt op
    | E.BinaryOp (binop, op1, op2) ->
        operand_to_string fmt op1 ^ " " ^ binop_to_string binop ^ " "
        ^ operand_to_string fmt op2
    | E.Discriminant p -> "discriminant(" ^ place_to_string fmt p ^ ")"
    | E.Aggregate (akind, ops) -> (
        let ops = List.map (operand_to_string fmt) ops in
        match akind with
        | E.AggregatedTuple -> "(" ^ String.concat ", " ops ^ ")"
        | E.AggregatedOption (variant_id, _ty) ->
            if variant_id == T.option_none_id then (
              assert (ops == []);
              "@Option::None")
            else if variant_id == T.option_some_id then (
              assert (List.length ops == 1);
              let op = List.hd ops in
              "@Option::Some(" ^ op ^ ")")
            else raise (Failure "Unreachable")
        | E.AggregatedAdt (def_id, opt_variant_id, _regions, _types) ->
            let adt_name = fmt.type_decl_id_to_string def_id in
            let variant_name =
              match opt_variant_id with
              | None -> adt_name
              | Some variant_id ->
                  adt_name ^ "::" ^ fmt.adt_variant_to_string def_id variant_id
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
            variant_name ^ " " ^ fields)

  let rec statement_to_string (fmt : ast_formatter) (indent : string)
      (indent_incr : string) (st : A.statement) : string =
    raw_statement_to_string fmt indent indent_incr st.content

  and raw_statement_to_string (fmt : ast_formatter) (indent : string)
      (indent_incr : string) (st : A.raw_statement) : string =
    match st with
    | A.Assign (p, rv) ->
        indent ^ place_to_string fmt p ^ " := " ^ rvalue_to_string fmt rv
    | A.AssignGlobal { dst; global } ->
        indent ^ fmt.var_id_to_string dst ^ " := global "
        ^ fmt.global_decl_id_to_string global
    | A.FakeRead p -> indent ^ "fake_read " ^ place_to_string fmt p
    | A.SetDiscriminant (p, variant_id) ->
        (* TODO: improve this to lookup the variant name by using the def id *)
        indent ^ "set_discriminant(" ^ place_to_string fmt p ^ ", "
        ^ T.VariantId.to_string variant_id
        ^ ")"
    | A.Drop p -> indent ^ "drop " ^ place_to_string fmt p
    | A.Assert a ->
        let cond = operand_to_string fmt a.A.cond in
        if a.A.expected then indent ^ "assert(" ^ cond ^ ")"
        else indent ^ "assert(¬" ^ cond ^ ")"
    | A.Call call ->
        let ty_fmt = ast_to_etype_formatter fmt in
        let t_params =
          if List.length call.A.type_args > 0 then
            "<"
            ^ String.concat ","
                (List.map (PT.ty_to_string ty_fmt) call.A.type_args)
            ^ ">"
          else ""
        in
        let args = List.map (operand_to_string fmt) call.A.args in
        let args = "(" ^ String.concat ", " args ^ ")" in
        let name_args =
          match call.A.func with
          | A.Regular fid -> fmt.fun_decl_id_to_string fid ^ t_params
          | A.Assumed fid -> (
              match fid with
              | A.Replace -> "core::mem::replace" ^ t_params
              | A.BoxNew -> "alloc::boxed::Box" ^ t_params ^ "::new"
              | A.BoxDeref ->
                  "core::ops::deref::Deref<Box" ^ t_params ^ ">::deref"
              | A.BoxDerefMut ->
                  "core::ops::deref::DerefMut" ^ t_params ^ "::deref_mut"
              | A.BoxFree -> "alloc::alloc::box_free" ^ t_params
              | A.VecNew -> "alloc::vec::Vec" ^ t_params ^ "::new"
              | A.VecPush -> "alloc::vec::Vec" ^ t_params ^ "::push"
              | A.VecInsert -> "alloc::vec::Vec" ^ t_params ^ "::insert"
              | A.VecLen -> "alloc::vec::Vec" ^ t_params ^ "::len"
              | A.VecIndex ->
                  "core::ops::index::Index<alloc::vec::Vec" ^ t_params
                  ^ ">::index"
              | A.VecIndexMut ->
                  "core::ops::index::IndexMut<alloc::vec::Vec" ^ t_params
                  ^ ">::index_mut")
        in
        let dest = place_to_string fmt call.A.dest in
        indent ^ dest ^ " := move " ^ name_args ^ args
    | A.Panic -> indent ^ "panic"
    | A.Return -> indent ^ "return"
    | A.Break i -> indent ^ "break " ^ string_of_int i
    | A.Continue i -> indent ^ "continue " ^ string_of_int i
    | A.Nop -> indent ^ "nop"
    | A.Sequence (st1, st2) ->
        statement_to_string fmt indent indent_incr st1
        ^ ";\n"
        ^ statement_to_string fmt indent indent_incr st2
    | A.Switch (op, tgts) -> (
        let op = operand_to_string fmt op in
        match tgts with
        | A.If (true_st, false_st) ->
            let inner_indent = indent ^ indent_incr in
            let inner_to_string =
              statement_to_string fmt inner_indent indent_incr
            in
            let true_st = inner_to_string true_st in
            let false_st = inner_to_string false_st in
            indent ^ "if (" ^ op ^ ") {\n" ^ true_st ^ "\n" ^ indent ^ "}\n"
            ^ indent ^ "else {\n" ^ false_st ^ "\n" ^ indent ^ "}"
        | A.SwitchInt (_ty, branches, otherwise) ->
            let indent1 = indent ^ indent_incr in
            let indent2 = indent1 ^ indent_incr in
            let inner_to_string2 =
              statement_to_string fmt indent2 indent_incr
            in
            let branches =
              List.map
                (fun (svl, be) ->
                  let svl =
                    List.map
                      (fun sv -> "| " ^ PPV.scalar_value_to_string sv)
                      svl
                  in
                  let svl = String.concat " " svl in
                  indent1 ^ svl ^ " => {\n" ^ inner_to_string2 be ^ "\n"
                  ^ indent1 ^ "}")
                branches
            in
            let branches = String.concat "\n" branches in
            let branches =
              branches ^ "\n" ^ indent1 ^ "_ => {\n"
              ^ inner_to_string2 otherwise ^ "\n" ^ indent1 ^ "}"
            in
            indent ^ "switch (" ^ op ^ ") {\n" ^ branches ^ "\n" ^ indent ^ "}")
    | A.Loop loop_st ->
        indent ^ "loop {\n"
        ^ statement_to_string fmt (indent ^ indent_incr) indent_incr loop_st
        ^ "\n" ^ indent ^ "}"

  let var_to_string (v : A.var) : string =
    match v.name with None -> var_id_to_string v.index | Some name -> name

  let fun_decl_to_string (fmt : ast_formatter) (indent : string)
      (indent_incr : string) (def : A.fun_decl) : string =
    let sty_fmt = ast_to_stype_formatter fmt in
    let sty_to_string = PT.sty_to_string sty_fmt in
    let ety_fmt = ast_to_etype_formatter fmt in
    let ety_to_string = PT.ety_to_string ety_fmt in
    let sg = def.signature in

    (* Function name *)
    let name = fun_name_to_string def.A.name in

    (* Region/type parameters *)
    let regions = sg.region_params in
    let types = sg.type_params in
    let params =
      if List.length regions + List.length types = 0 then ""
      else
        let regions = List.map PT.region_var_to_string regions in
        let types = List.map PT.type_var_to_string types in
        "<" ^ String.concat "," (List.append regions types) ^ ">"
    in

    (* Return type *)
    let ret_ty = sg.output in
    let ret_ty =
      if TU.ty_is_unit ret_ty then "" else " -> " ^ sty_to_string ret_ty
    in

    (* We print the declaration differently if it is opaque (no body) or transparent
     * (we have access to a body) *)
    match def.body with
    | None ->
        (* Arguments *)
        let input_tys = sg.inputs in
        let args = List.map sty_to_string input_tys in
        let args = String.concat ", " args in

        (* Put everything together *)
        indent ^ "opaque fn " ^ name ^ params ^ "(" ^ args ^ ")" ^ ret_ty
    | Some body ->
        (* Arguments *)
        let inputs = List.tl body.locals in
        let inputs, _aux_locals =
          Collections.List.split_at inputs body.arg_count
        in
        let args = List.combine inputs sg.inputs in
        let args =
          List.map
            (fun (var, rty) -> var_to_string var ^ " : " ^ sty_to_string rty)
            args
        in
        let args = String.concat ", " args in

        (* All the locals (with erased regions) *)
        let locals =
          List.map
            (fun var ->
              indent ^ indent_incr ^ var_to_string var ^ " : "
              ^ ety_to_string var.var_ty ^ ";")
            body.locals
        in
        let locals = String.concat "\n" locals in

        (* Body *)
        let body =
          statement_to_string fmt (indent ^ indent_incr) indent_incr body.body
        in

        (* Put everything together *)
        indent ^ "fn " ^ name ^ params ^ "(" ^ args ^ ")" ^ ret_ty ^ " {\n"
        ^ locals ^ "\n\n" ^ body ^ "\n" ^ indent ^ "}"
end

module PA = LlbcAst (* local module *)

(** Pretty-printing for ASTs (functions based on a definition context) *)
module Module = struct
  (** This function pretty-prints a type definition by using a definition
      context *)
  let type_decl_to_string (type_context : T.type_decl T.TypeDeclId.Map.t)
      (def : T.type_decl) : string =
    let type_decl_id_to_string (id : T.TypeDeclId.id) : string =
      let def = T.TypeDeclId.Map.find id type_context in
      name_to_string def.name
    in
    PT.type_decl_to_string type_decl_id_to_string def

  (** Generate an [ast_formatter] by using a definition context in combination
      with the variables local to a function's definition *)
  let def_ctx_to_ast_formatter (type_context : T.type_decl T.TypeDeclId.Map.t)
      (fun_context : A.fun_decl A.FunDeclId.Map.t)
      (global_context : A.global_decl A.GlobalDeclId.Map.t) (def : A.fun_decl) :
      PA.ast_formatter =
    let rvar_to_string vid =
      let var = T.RegionVarId.nth def.signature.region_params vid in
      PT.region_var_to_string var
    in
    let r_to_string vid =
      (* TODO: we might want something more informative *)
      PT.region_id_to_string vid
    in
    let type_var_id_to_string vid =
      let var = T.TypeVarId.nth def.signature.type_params vid in
      PT.type_var_to_string var
    in
    let type_decl_id_to_string def_id =
      let def = T.TypeDeclId.Map.find def_id type_context in
      name_to_string def.name
    in
    let fun_decl_id_to_string def_id =
      let def = A.FunDeclId.Map.find def_id fun_context in
      fun_name_to_string def.name
    in
    let global_decl_id_to_string def_id =
      let def = A.GlobalDeclId.Map.find def_id global_context in
      global_name_to_string def.name
    in
    let var_id_to_string vid =
      let var = E.VarId.nth (Option.get def.body).locals vid in
      PA.var_to_string var
    in
    let adt_variant_to_string =
      PT.type_ctx_to_adt_variant_to_string_fun type_context
    in
    let adt_field_to_string =
      PT.type_ctx_to_adt_field_to_string_fun type_context
    in
    let adt_field_names = PT.type_ctx_to_adt_field_names_fun type_context in
    {
      rvar_to_string;
      r_to_string;
      type_var_id_to_string;
      type_decl_id_to_string;
      adt_variant_to_string;
      adt_field_to_string;
      var_id_to_string;
      adt_field_names;
      fun_decl_id_to_string;
      global_decl_id_to_string;
    }

  (** This function pretty-prints a function definition by using a definition
      context *)
  let fun_decl_to_string (type_context : T.type_decl T.TypeDeclId.Map.t)
      (fun_context : A.fun_decl A.FunDeclId.Map.t)
      (global_context : A.global_decl A.GlobalDeclId.Map.t) (def : A.fun_decl) :
      string =
    let fmt =
      def_ctx_to_ast_formatter type_context fun_context global_context def
    in
    PA.fun_decl_to_string fmt "" "  " def

  let module_to_string (m : Crates.llbc_crate) : string =
    let types_defs_map, funs_defs_map, globals_defs_map =
      Crates.compute_defs_maps m
    in

    (* The types *)
    let type_decls =
      List.map (type_decl_to_string types_defs_map) m.Crates.types
    in

    (* The functions *)
    let fun_decls =
      List.map
        (fun_decl_to_string types_defs_map funs_defs_map globals_defs_map)
        m.Crates.functions
    in

    (* Put everything together *)
    let all_defs = List.append type_decls fun_decls in
    String.concat "\n\n" all_defs
end
