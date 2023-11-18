(** Utilities to identify Rust definitions by matching on their names.

    Identifying Rust definitions is non trivial because of:
    - the impl blocks, which are identified by their types
    - trait instances, which don't have a name (and which we identify
      with trait references)

    For this reason, we define:
    - a small pattern matching language for Rust names
    - a parser for this language
    - matchers which check if a name matches a pattern
    - helpers to derive patterns from names (useful when one identifies
      some external functions that need custom treatment, as it avoids
      writing patterns by hand)

    Here are some examples of patterns:
    - "core::mem::replace": the function `core::mem::replace`
    - "alloc::vec::{alloc::vec::Vec<@T>}::push": the function `push` in any
      impl block of type `alloc::vec::Vec<T>`, where T is a type variable.
      Note that "@T" means that this matches any type variable. In case
      we need stronger constraints, we can add indices: "@T1". All the
      occurrences of "@T1" must match the same variable (ex.: "Foo<@T, @T>"
      would match `Foo<T1, T2` as well as `Foo<T, T>`, while "Foo<@T1, @T1>"
      only matches `Foo<T, T>`).
    - for the types we put inside blocks, we have syntax for arrays, slices,
      and references:
      - "[@T; @C]": slice
      - "&@R mut @T": mutable reference

    Remark: `Box` is treated as a primitive type, which means that one only
    needs to type "Box" (instead of "alloc::boxed::Box").
 *)

(* The "raw" name matcher patterns *)
module RNM = Name_matcher_parser.Interface
module T = Types

type ref_kind = T.ref_kind [@@deriving show]
type integer_type = T.integer_type [@@deriving show]
type literal_type = T.literal_type [@@deriving show]
type assumed_ty = T.assumed_ty [@@deriving show]
type region = int [@@deriving show]
type const_generic_var = int [@@deriving show]
type big_int = PrimitiveValues.big_int [@@deriving show]

type const_generic = CgVar of const_generic_var option | CgValue of big_int
[@@deriving show]

(* We define a more precise version of the patterns, where for instance
   we detect the primitive types like `bool` (note that we also treat
   `Box` as a primitive type. *)
type name = name_elem list
and name_elem = PeIdent of string | PeImpl of ty
and type_id = TAdtId of name | TTuple | TAssumed of assumed_ty

and ty =
  | TAdt of type_id * generic_args
  | TVar of int option
  | TLiteral of literal_type
  | TRef of region option * ty * ref_kind

and generic_args = {
  regions : region option list;
  types : ty list;
  const_generics : const_generic list;
}
[@@deriving show]

type inst_name = { name : name; generics : generic_args } [@@deriving show]

let empty_generic_args = { regions = []; types = []; const_generics = [] }

(*
 * Conversion from the "raw" patterns
 *)
let convert_ref_kind (rk : RNM.ref_kind) : ref_kind =
  match rk with RMut -> RMut | RShared -> RShared

let rec convert_name (n : RNM.name) = List.map convert_name_elem n

and convert_name_elem (e : RNM.name_elem) : name_elem =
  match e with Ident s -> PeIdent s | Impl ty -> PeImpl (convert_ty ty)

and convert_ty (ty : RNM.ty) : ty =
  match ty with
  | TTy (name, generics) -> convert_tty name generics
  | TVar v -> TVar v
  | TRef (r, ty, rk) -> TRef (r, convert_ty ty, convert_ref_kind rk)

and convert_generic_args (gl : RNM.generic_args) : generic_args =
  let rec convert (regions : region option list) (types : ty list)
      (cgs : const_generic list) (gl : RNM.generic_args) : generic_args =
    match gl with
    | [] ->
        {
          regions = List.rev regions;
          types = List.rev types;
          const_generics = List.rev cgs;
        }
    | g :: gl -> (
        match g with
        | GRegion r ->
            assert (types = []);
            assert (cgs = []);
            convert (r :: regions) types cgs gl
        | GType ty ->
            assert (cgs = []);
            convert regions (convert_ty ty :: types) cgs gl
        | GConstGeneric cg ->
            convert regions types (convert_const_generic cg :: cgs) gl)
  in
  convert [] [] [] gl

and convert_const_generic (cg : RNM.const_generic) : const_generic =
  match cg with CgVar v -> CgVar v | CgValue v -> CgValue v

and convert_tty (name : RNM.type_id) (generics : RNM.generic_args) : ty =
  let generics = convert_generic_args generics in
  let mk_assumed (id : assumed_ty) : ty = TAdt (TAssumed id, generics) in
  let mk_literal (ty : literal_type) : ty =
    assert (generics = empty_generic_args);
    TLiteral ty
  in
  let mk_scalar (ty : integer_type) : ty = mk_literal (TInteger ty) in
  match name with
  | TArray -> mk_assumed TArray
  | TSlice -> mk_assumed TSlice
  | TTuple ->
      assert (generics.regions = []);
      assert (generics.const_generics = []);
      TAdt (TTuple, generics)
  | TName n -> (
      let n = convert_name n in
      match n with
      | [ PeIdent "Box" ] | [ PeIdent "alloc"; PeIdent "boxed"; PeIdent "Box" ]
        ->
          mk_assumed TBox
      | [ PeIdent "str" ] -> mk_assumed TStr
      | [ PeIdent "bool" ] -> mk_literal TBool
      | [ PeIdent "char" ] -> mk_literal TChar
      | [ PeIdent "isize" ] -> mk_scalar Isize
      | [ PeIdent "i8" ] -> mk_scalar I8
      | [ PeIdent "i16" ] -> mk_scalar I16
      | [ PeIdent "i32" ] -> mk_scalar I32
      | [ PeIdent "i64" ] -> mk_scalar I64
      | [ PeIdent "i128" ] -> mk_scalar I128
      | [ PeIdent "Usize" ] -> mk_scalar Usize
      | [ PeIdent "u8" ] -> mk_scalar U8
      | [ PeIdent "u16" ] -> mk_scalar U16
      | [ PeIdent "u32" ] -> mk_scalar U32
      | [ PeIdent "u64" ] -> mk_scalar U64
      | [ PeIdent "u128" ] -> mk_scalar U128
      | n -> TAdt (TAdtId n, generics))

let convert_inst_name (n : RNM.inst_name) : inst_name =
  let { name; generics } : RNM.inst_name = n in
  let name = convert_name name in
  let generics = convert_generic_args generics in
  { name; generics }

(*
 * Parse patterns
 *)
let parse_name_pattern (s : string) : name =
  let pat = RNM.parse_name_pattern s in
  convert_name pat

let parse_inst_name_pattern (s : string) : inst_name =
  let pat = RNM.parse_inst_name_pattern s in
  convert_inst_name pat

(*
 * Match a name
 *)

module IntMap = Collections.IntMap

(* Context to lookup definitions *)
type ctx = { type_decls : T.type_decl T.TypeDeclId.Map.t }

(* Small helper to store the mappings from variables to variables *)
type maps = {
  rmap : T.RegionId.id IntMap.t ref;
  tmap : T.TypeVarId.id IntMap.t ref;
  cmap : T.ConstGenericVarId.id IntMap.t ref;
}

let mk_empty_maps () =
  { rmap = ref IntMap.empty; tmap = ref IntMap.empty; cmap = ref IntMap.empty }

(** Update a map and check that there are no incompatible
    constraints at the same time *)
let update_map (m : 'a IntMap.t ref) (id : int) (v : 'a) : bool =
  match IntMap.find_opt id !m with
  | None ->
      (* Simply update *)
      m := IntMap.add id v !m;
      true
  | Some v' ->
      (* Check the binding *)
      v = v'

let update_rmap (m : maps) = update_map m.rmap
let update_tmap (m : maps) = update_map m.tmap
let update_cmap (m : maps) = update_map m.cmap

let opt_update_rmap (m : maps) (id : int option) (r : T.RegionId.id) : bool =
  match id with None -> true | Some id -> update_rmap m id r

let opt_update_cmap (m : maps) (id : int option) (x : T.ConstGenericVarId.id) :
    bool =
  match id with None -> true | Some id -> update_cmap m id x

let match_region (m : maps) (id : int option) (r : T.region) : bool =
  match r with RVar r -> opt_update_rmap m id r | _ -> false

let rec match_name (ctx : ctx) (p : name) (n : T.name) : bool =
  match (p, n) with
  | [], [] -> true
  | PeIdent pid :: p, PeIdent (id, _) :: n -> pid = id && match_name ctx p n
  | PeImpl pty :: p, PeImpl impl :: n ->
      match_ty ctx pty impl.ty && match_name ctx p n
  | _ -> false

and match_type_id (ctx : ctx) (pid : type_id) (id : T.type_id) : bool =
  match (pid, id) with
  | TAdtId pid, TAdtId id ->
      (* Lookup the type decl and match the name *)
      let d = T.TypeDeclId.Map.find id ctx.type_decls in
      match_name ctx pid d.name
  | TTuple, TTuple -> true
  | TAssumed aid, TAssumed paid -> aid = paid
  | _ -> false

and match_ty_aux (ctx : ctx) (m : maps) (pty : ty) (ty : T.ty) : bool =
  match (pty, ty) with
  | TAdt (pid, pgenerics), TAdt (id, generics) ->
      match_type_id ctx pid id
      && match_generic_args_aux ctx m pgenerics generics
  | TLiteral plit, TLiteral lit -> plit = lit
  | TVar None, TVar _ ->
      (* No constraints to check *)
      true
  | TVar (Some pv), TVar v ->
      (* Update and check the constraints map *)
      update_tmap m pv v
  | TRef (pr, pty, prk), TRef (r, ty, rk) ->
      match_region m pr r && match_ty_aux ctx m pty ty && prk = rk
  | _ -> false

and match_ty (ctx : ctx) (pty : ty) (ty : T.ty) : bool =
  match_ty_aux ctx (mk_empty_maps ()) pty ty

and match_generic_args_aux (ctx : ctx) (m : maps) (pgenerics : generic_args)
    (generics : T.generic_args) : bool =
  let { regions; types; const_generics; trait_refs = _ } : T.generic_args =
    generics
  in
  let { regions = pregions; types = ptypes; const_generics = pconst_generics } =
    pgenerics
  in
  if
    List.length regions = List.length pregions
    && List.length types = List.length ptypes
    && List.length const_generics = List.length pconst_generics
  then
    List.for_all2 (match_region m) pregions regions
    && List.for_all2 (match_ty_aux ctx m) ptypes types
    && List.for_all2 (match_const_generic ctx m) pconst_generics const_generics
  else false

and match_generic_args (ctx : ctx) (pgenerics : generic_args)
    (generics : T.generic_args) : bool =
  match_generic_args_aux ctx (mk_empty_maps ()) pgenerics generics

and match_const_generic (_ctx : ctx) (m : maps) (pcg : const_generic)
    (cg : T.const_generic) : bool =
  match (pcg, cg) with
  | CgVar pv, CGVar v -> opt_update_cmap m pv v
  | CgValue pv, CGValue v -> (
      match v with VScalar v -> v.value = pv | _ -> false)
  | _ -> false

let match_inst_name (ctx : ctx) (p : inst_name) (n : T.name)
    (generics : T.generic_args) : bool =
  match_name ctx p.name n && match_generic_args ctx p.generics generics

let mk_name_matcher (ctx : ctx) (pat : string) : T.name -> bool =
  let pat = parse_name_pattern pat in
  match_name ctx pat

let mk_inst_name_matcher (ctx : ctx) (pat : string) :
    T.name -> T.generic_args -> bool =
  let pat = parse_inst_name_pattern pat in
  match_inst_name ctx pat

(*
 * Helpers to convert names to patterns
 *)

(* We use this to store the constraints maps (the map from variable
   ids to option pattern variable ids) *)
type constraints = {
  rmap : int option T.RegionId.Map.t;
  tmap : int option T.TypeVarId.Map.t;
  cmap : int option T.ConstGenericVarId.Map.t;
}

let type_var_to_pattern (m : constraints) (v : T.TypeVarId.id) : int option =
  T.TypeVarId.Map.find v m.tmap

let region_to_pattern (m : constraints) (r : T.region) : int option =
  match r with
  | RVar r -> T.RegionId.Map.find r m.rmap
  | _ -> raise (Failure "Unimplemented")

let const_generic_to_pattern (m : constraints) (cg : T.const_generic) :
    const_generic =
  match cg with
  | CGVar v -> CgVar (T.ConstGenericVarId.Map.find v m.cmap)
  | CGValue (VScalar v) -> CgValue v.value
  | _ -> raise (Failure "Unimplemented")

(** Visitor to compute constraints map.

    We essentially count the occurrences of (type, region, const generic)
    variables. If a variable appears once, it doesn't have any constraints
    (we use the @R, @T, @C patterns). If a variable appears more than once,
    we give it an identifier (@T1, etc.).
*)
let mk_compute_constraints_map_visitor () =
  (* The sets of variables we encounter *)
  let rset = ref T.RegionId.Set.empty in
  let tset = ref T.TypeVarId.Set.empty in
  let cset = ref T.ConstGenericVarId.Set.empty in
  (* The sets of variables we encounter twice *)
  let rset_dup = ref T.RegionId.Set.empty in
  let tset_dup = ref T.TypeVarId.Set.empty in
  let cset_dup = ref T.ConstGenericVarId.Set.empty in
  (* Helpers *)
  let register_var (type s e)
      (module S : Collections.Set with type t = s and type elt = e)
      (set : S.t ref) (set_dup : S.t ref) (x : S.elt) : unit =
    (* If the variable has already been registered, add it to the duplicate
       set, otherwise register it in the "regular" set *)
    if S.mem x !set then set_dup := S.add x !set_dup else set := S.add x !set
  in
  let register_region_var =
    register_var (module T.RegionId.Set) rset rset_dup
  in
  let register_type_var = register_var (module T.TypeVarId.Set) tset tset_dup in
  let register_const_generic_var =
    register_var (module T.ConstGenericVarId.Set) cset cset_dup
  in
  (* TODO: we can't parameterize with a module M satisfying Collections.Map,
     because we would then need to introduce a constraint on the polymorphic
     type 'a M.t, which is not possible in OCaml *)
  let get_var_pattern_ids (type s e)
      (module S : Collections.Set with type t = s and type elt = e)
      (set : S.t ref) (set_dup : S.t ref) (id_gen : int ref) :
      (S.elt * int option) list =
    List.map
      (fun x ->
        let id =
          if S.mem x !set_dup then (
            let id = !id_gen in
            id_gen := id + 1;
            Some id)
          else None
        in
        (x, id))
      (S.elements !set)
  in
  let get_constraints () : constraints =
    let rmap =
      T.RegionId.Map.of_list
        (get_var_pattern_ids (module T.RegionId.Set) rset rset_dup (ref 0))
    in
    let tmap =
      T.TypeVarId.Map.of_list
        (get_var_pattern_ids (module T.TypeVarId.Set) tset tset_dup (ref 0))
    in
    let cmap =
      T.ConstGenericVarId.Map.of_list
        (get_var_pattern_ids
           (module T.ConstGenericVarId.Set)
           cset cset_dup (ref 0))
    in
    { rmap; tmap; cmap }
  in
  let visitor =
    object
      inherit [_] Types.iter_ty
      method! visit_region_id _ id = register_region_var id
      method! visit_type_var_id _ id = register_type_var id
      method! visit_const_generic_var_id _ id = register_const_generic_var id
    end
  in
  (visitor, get_constraints)

let rec name_to_pattern_aux (ctx : ctx) (n : T.name) : name =
  match n with
  | [] -> []
  | e :: n -> path_elem_to_pattern ctx e :: name_to_pattern_aux ctx n

and path_elem_to_pattern (ctx : ctx) (e : T.path_elem) : name_elem =
  match e with
  | PeIdent (s, _) -> PeIdent s
  | PeImpl impl -> impl_elem_to_pattern ctx impl

and impl_elem_to_pattern (ctx : ctx) (impl : T.impl_elem) : name_elem =
  PeImpl (ty_to_pattern ctx impl.ty)

and ty_to_pattern_aux (ctx : ctx) (m : constraints) (ty : T.ty) : ty =
  match ty with
  | TAdt (id, generics) ->
      TAdt (id_to_pattern ctx id, generic_args_to_pattern_aux ctx m generics)
  | TVar v -> TVar (type_var_to_pattern m v)
  | TLiteral lit -> TLiteral lit
  | TRef (r, ty, rk) ->
      TRef (region_to_pattern m r, ty_to_pattern_aux ctx m ty, rk)
  | TNever | TRawPtr _ | TArrow _ | TTraitType _ ->
      raise (Failure "Unimplemented")

and ty_to_pattern (ctx : ctx) (ty : T.ty) : ty =
  (* Compute the constraints map *)
  let visitor, get_constraints = mk_compute_constraints_map_visitor () in
  visitor#visit_ty () ty;
  let m = get_constraints () in
  (* Convert the type *)
  ty_to_pattern_aux ctx m ty

and generic_args_to_pattern_aux (ctx : ctx) (m : constraints)
    (generics : T.generic_args) : generic_args =
  let { regions; types; const_generics; trait_refs = _ } : T.generic_args =
    generics
  in
  {
    regions = List.map (region_to_pattern m) regions;
    types = List.map (ty_to_pattern_aux ctx m) types;
    const_generics = List.map (const_generic_to_pattern m) const_generics;
  }

and id_to_pattern (ctx : ctx) (id : T.type_id) : type_id =
  match id with
  | TAdtId id ->
      (* Lookup the declaration *)
      let d = T.TypeDeclId.Map.find id ctx.type_decls in
      TAdtId (name_to_pattern_aux ctx d.name)
  | TTuple -> TTuple
  | TAssumed aty -> TAssumed aty

let generic_args_to_pattern (ctx : ctx) (generics : T.generic_args) :
    generic_args =
  (* Compute the constraints map *)
  let visitor, get_constraints = mk_compute_constraints_map_visitor () in
  visitor#visit_generic_args () generics;
  let m = get_constraints () in
  (* Convert the type *)
  generic_args_to_pattern_aux ctx m generics

let name_to_pattern (ctx : ctx) (n : T.name) : name =
  (* Convert the name to a pattern *)
  let pat = name_to_pattern_aux ctx n in
  (* Sanity check: the name should match the pattern *)
  assert (match_name ctx pat n);
  (* Return *)
  pat

let inst_name_to_pattern (ctx : ctx) (n : T.name) (generics : T.generic_args) :
    inst_name =
  (* Convert the name to a pattern *)
  let pat =
    let name = name_to_pattern_aux ctx n in
    let generics = generic_args_to_pattern ctx generics in
    { name; generics }
  in
  (* Sanity check: the name should match the pattern *)
  assert (match_inst_name ctx pat n generics);
  (* Return *)
  pat

(*
 * Convert patterns to strings
 *)
let literal_type_to_string (lit : literal_type) : string =
  match lit with
  | TBool -> "bool"
  | TChar -> "char"
  | TInteger ty -> (
      match ty with
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
      | U128 -> "u128")

let type_var_to_string (v : int option) : string =
  match v with None -> "@T" | Some v -> "@T" ^ string_of_int v

let region_var_to_string (v : int option) : string =
  match v with None -> "@R" | Some v -> "@R" ^ string_of_int v

let const_generic_var_to_string (v : int option) : string =
  match v with None -> "@C" | Some v -> "@C" ^ string_of_int v

let const_generic_to_string (cg : const_generic) : string =
  match cg with
  | CgVar v -> const_generic_var_to_string v
  | CgValue v -> Z.to_string v

let rec name_to_string_aux (n : name) : string =
  String.concat "::" (List.map name_elem_to_string n)

and name_elem_to_string (e : name_elem) : string =
  match e with PeIdent s -> s | PeImpl ty -> "{" ^ ty_to_string ty ^ "}"

and ty_to_string (ty : ty) : string =
  match ty with
  | TAdt (id, generics) -> (
      match id with
      | TTuple ->
          assert (generics.regions = []);
          assert (generics.const_generics = []);
          "(" ^ String.concat ", " (List.map ty_to_string generics.types) ^ ")"
      | TAssumed TArray -> (
          match generics with
          | { regions = []; types = [ ty ]; const_generics = [ cg ] } ->
              "[" ^ ty_to_string ty ^ "; " ^ const_generic_to_string cg ^ "]"
          | _ -> raise (Failure "Ill-formed pattern"))
      | TAssumed TSlice -> (
          match generics with
          | { regions = []; types = [ ty ]; const_generics = [] } ->
              "[" ^ ty_to_string ty ^ "]"
          | _ -> raise (Failure "Ill-formed pattern"))
      | TAssumed TStr ->
          assert (generics = empty_generic_args);
          "str"
      | TAssumed TBox -> (
          match generics with
          | { regions = []; types = [ ty ]; const_generics = [] } ->
              "Box<" ^ ty_to_string ty ^ ">"
          | _ -> raise (Failure "Ill-formed pattern"))
      | TAdtId id -> name_to_string_aux id ^ generic_args_to_string generics)
  | TVar v -> type_var_to_string v
  | TLiteral lit -> literal_type_to_string lit
  | TRef (r, ty, rk) ->
      let rk = match rk with RMut -> "mut " | RShared -> "" in
      "&" ^ region_var_to_string r ^ " " ^ rk ^ ty_to_string ty

and generic_args_to_string (generics : generic_args) : string =
  let { regions; types; const_generics } = generics in
  let regions = List.map region_var_to_string regions in
  let types = List.map ty_to_string types in
  let const_generics = List.map const_generic_to_string const_generics in
  let generics = List.concat [ regions; types; const_generics ] in
  if generics = [] then "" else "<" ^ String.concat ", " generics ^ ">"
