(** WARNING: this file is partially auto-generated. Do not edit `OfJson.ml` by
    hand. Edit `generate_ml/templates/OfJson.ml` instead, or improve the code
    generation tool so avoid the need for hand-writing things.

    `generate_ml/templates/OfJson.ml` contains the manual definitions and some
    `(* __REPLACEn__ *)` comments. These comments are replaced by auto-generated
    definitions by running `make generate-asts` in the crate root. The
    code-generation code is in `charon/src/bin/generate-asts`. *)

open Yojson.Basic
open OfJsonBasic
open Identifiers
open Generated_Meta
open Generated_Values
open Generated_Types
open Generated_Expressions
open Generated_GAst
open Generated_FullAst
open Scalars
module FileId = IdGen ()
module HashConsId = IdGen ()

(** The default logger *)
let log = Logging.llbc_of_json_logger

module FileTbl = Hashtbl.Make (struct
  type t = FileId.id

  let equal = FileId.equal_id
  let hash = Hashtbl.hash
end)

type of_json_ctx = {
  id_to_file_map : file FileTbl.t;
  ty_hashcons_map : ty HashConsId.Map.t ref;
  tref_hashcons_map : trait_ref HashConsId.Map.t ref;
}

let empty_of_json_ctx : of_json_ctx =
  {
    id_to_file_map = FileTbl.create 8;
    ty_hashcons_map = ref HashConsId.Map.empty;
    tref_hashcons_map = ref HashConsId.Map.empty;
  }

let hash_consed_val_of_json (map : 'a HashConsId.Map.t ref)
    (of_json : of_json_ctx -> json -> ('a, string) result) (ctx : of_json_ctx)
    (js : json) : ('a, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Untagged", json) ] -> of_json ctx json
    | `Assoc [ ("HashConsedValue", `List [ `Int id; json ]) ] ->
        let* v = of_json ctx json in
        let id = HashConsId.of_int id in
        map := HashConsId.Map.add id v !map;
        Ok v
    | `Assoc [ ("Deduplicated", `Int id) ] -> begin
        let id = HashConsId.of_int id in
        match HashConsId.Map.find_opt id !map with
        | Some v -> Ok v
        | None ->
            Error
              "Hash-consing key not found; there is a serialization mismatch \
               between Rust and OCaml"
      end
    | _ -> Error "")

let path_buf_of_json = string_of_json

let big_int_of_json _ (js : json) : (big_int, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Int i -> Ok (Z.of_int i)
    | `String is -> Ok (Z.of_string is)
    | _ -> Error "")

let opt_indexed_map_of_json :
    'a0 'a1.
    (of_json_ctx -> json -> ('a0, string) result) ->
    (of_json_ctx -> json -> ('a1, string) result) ->
    of_json_ctx ->
    json ->
    ('a1 option list, string) result =
 fun arg0_of_json arg1_of_json ctx js ->
  list_of_json (option_of_json arg1_of_json) ctx js

let rec ___ = ()

and abi_of_json (ctx : of_json_ctx) (js : json) : (abi, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `String "Rust" -> Ok AbiRust
    | `String "C" -> Ok AbiC
    | `Assoc [ ("Other", _0) ] ->
        let* _0 = string_of_json ctx _0 in
        Ok (AbiOther _0)
    | _ -> Error "")

and abort_kind_of_json (ctx : of_json_ctx) (js : json) :
    (abort_kind, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Panic", _0) ] ->
        let* _0 = option_of_json name_of_json ctx _0 in
        Ok (Panic _0)
    | `String "UndefinedBehavior" -> Ok UndefinedBehavior
    | `String "UnwindTerminate" -> Ok UnwindTerminate
    | _ -> Error "")

and aggregate_kind_of_json (ctx : of_json_ctx) (js : json) :
    (aggregate_kind, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Adt", `List [ _0; _1; _2 ]) ] ->
        let* _0 = type_decl_ref_of_json ctx _0 in
        let* _1 = option_of_json variant_id_of_json ctx _1 in
        let* _2 = option_of_json field_id_of_json ctx _2 in
        Ok (AggregatedAdt (_0, _1, _2))
    | `Assoc [ ("Array", `List [ _0; _1 ]) ] ->
        let* _0 = ty_of_json ctx _0 in
        let* _1 = box_of_json constant_expr_of_json ctx _1 in
        Ok (AggregatedArray (_0, _1))
    | `Assoc [ ("RawPtr", `List [ _0; _1 ]) ] ->
        let* _0 = ty_of_json ctx _0 in
        let* _1 = ref_kind_of_json ctx _1 in
        Ok (AggregatedRawPtr (_0, _1))
    | _ -> Error "")

and assertion_of_json (ctx : of_json_ctx) (js : json) :
    (assertion, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc
        [ ("cond", cond); ("expected", expected); ("check_kind", check_kind) ]
      ->
        let* cond = operand_of_json ctx cond in
        let* expected = bool_of_json ctx expected in
        let* check_kind =
          option_of_json builtin_assert_kind_of_json ctx check_kind
        in
        Ok ({ cond; expected; check_kind } : assertion)
    | _ -> Error "")

and assoc_const_id_of_json (ctx : of_json_ctx) (js : json) :
    (assoc_const_id, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | x -> AssocConstId.id_of_json ctx x
    | _ -> Error "")

and assoc_type_id_of_json (ctx : of_json_ctx) (js : json) :
    (assoc_type_id, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | x -> AssocTypeId.id_of_json ctx x
    | _ -> Error "")

and binop_of_json (ctx : of_json_ctx) (js : json) : (binop, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `String "BitXor" -> Ok BitXor
    | `String "BitAnd" -> Ok BitAnd
    | `String "BitOr" -> Ok BitOr
    | `String "Eq" -> Ok Eq
    | `String "Lt" -> Ok Lt
    | `String "Le" -> Ok Le
    | `String "Ne" -> Ok Ne
    | `String "Ge" -> Ok Ge
    | `String "Gt" -> Ok Gt
    | `Assoc [ ("Add", _0) ] ->
        let* _0 = overflow_mode_of_json ctx _0 in
        Ok (Add _0)
    | `Assoc [ ("Sub", _0) ] ->
        let* _0 = overflow_mode_of_json ctx _0 in
        Ok (Sub _0)
    | `Assoc [ ("Mul", _0) ] ->
        let* _0 = overflow_mode_of_json ctx _0 in
        Ok (Mul _0)
    | `Assoc [ ("Div", _0) ] ->
        let* _0 = overflow_mode_of_json ctx _0 in
        Ok (Div _0)
    | `Assoc [ ("Rem", _0) ] ->
        let* _0 = overflow_mode_of_json ctx _0 in
        Ok (Rem _0)
    | `String "AddChecked" -> Ok AddChecked
    | `String "SubChecked" -> Ok SubChecked
    | `String "MulChecked" -> Ok MulChecked
    | `Assoc [ ("Shl", _0) ] ->
        let* _0 = overflow_mode_of_json ctx _0 in
        Ok (Shl _0)
    | `Assoc [ ("Shr", _0) ] ->
        let* _0 = overflow_mode_of_json ctx _0 in
        Ok (Shr _0)
    | `String "Offset" -> Ok Offset
    | `String "Cmp" -> Ok Cmp
    | _ -> Error "")

and binder_of_json :
    'a0.
    (of_json_ctx -> json -> ('a0, string) result) ->
    of_json_ctx ->
    json ->
    ('a0 binder, string) result =
 fun arg0_of_json ctx js ->
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("params", params); ("skip_binder", skip_binder); ("kind", _) ]
      ->
        let* binder_params = generic_params_of_json ctx params in
        let* binder_value = arg0_of_json ctx skip_binder in
        Ok ({ binder_params; binder_value } : _ binder)
    | _ -> Error "")

and binder_kind_of_json (ctx : of_json_ctx) (js : json) :
    (binder_kind, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("TraitType", `List [ _0; _1 ]) ] ->
        let* _0 = trait_decl_id_of_json ctx _0 in
        let* _1 = assoc_type_id_of_json ctx _1 in
        Ok (BKTraitType (_0, _1))
    | `Assoc [ ("TraitMethod", `List [ _0; _1 ]) ] ->
        let* _0 = trait_decl_id_of_json ctx _0 in
        let* _1 = trait_method_id_of_json ctx _1 in
        Ok (BKTraitMethod (_0, _1))
    | `String "InherentImplBlock" -> Ok BKInherentImplBlock
    | `String "Dyn" -> Ok BKDyn
    | `String "Other" -> Ok BKOther
    | _ -> Error "")

and borrow_kind_of_json (ctx : of_json_ctx) (js : json) :
    (borrow_kind, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `String "Shared" -> Ok BShared
    | `String "Mut" -> Ok BMut
    | `String "TwoPhaseMut" -> Ok BTwoPhaseMut
    | `String "Shallow" -> Ok BShallow
    | `String "UniqueImmutable" -> Ok BUniqueImmutable
    | _ -> Error "")

and borrowck_statement_of_json (ctx : of_json_ctx) (js : json) :
    (borrowck_statement, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("FakeRead", _0) ] ->
        let* _0 = place_of_json ctx _0 in
        Ok (FakeRead _0)
    | `Assoc
        [
          ( "SetType",
            `Assoc [ ("place", place); ("ty", ty); ("variance", variance) ] );
        ] ->
        let* place = place_of_json ctx place in
        let* ty = ty_of_json ctx ty in
        let* variance = variance_of_json ctx variance in
        Ok (SetType (place, ty, variance))
    | `Assoc [ ("SetOutlives", `List [ _0; _1 ]) ] ->
        let* _0 = ty_of_json ctx _0 in
        let* _1 = region_of_json ctx _1 in
        Ok (SetOutlives (_0, _1))
    | `Assoc [ ("PredicateHolds", _0) ] ->
        let* _0 = trait_ref_of_json ctx _0 in
        Ok (PredicateHolds _0)
    | _ -> Error "")

and builtin_assert_kind_of_json (ctx : of_json_ctx) (js : json) :
    (builtin_assert_kind, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("BoundsCheck", `Assoc [ ("len", len); ("index", index) ]) ] ->
        let* len = operand_of_json ctx len in
        let* index = operand_of_json ctx index in
        Ok (BoundsCheck (len, index))
    | `Assoc [ ("Overflow", `List [ _0; _1; _2 ]) ] ->
        let* _0 = binop_of_json ctx _0 in
        let* _1 = operand_of_json ctx _1 in
        let* _2 = operand_of_json ctx _2 in
        Ok (Overflow (_0, _1, _2))
    | `Assoc [ ("OverflowNeg", _0) ] ->
        let* _0 = operand_of_json ctx _0 in
        Ok (OverflowNeg _0)
    | `Assoc [ ("DivisionByZero", _0) ] ->
        let* _0 = operand_of_json ctx _0 in
        Ok (DivisionByZero _0)
    | `Assoc [ ("RemainderByZero", _0) ] ->
        let* _0 = operand_of_json ctx _0 in
        Ok (RemainderByZero _0)
    | `Assoc
        [
          ( "MisalignedPointerDereference",
            `Assoc [ ("required", required); ("found", found) ] );
        ] ->
        let* required = operand_of_json ctx required in
        let* found = operand_of_json ctx found in
        Ok (MisalignedPointerDereference (required, found))
    | `String "NullPointerDereference" -> Ok NullPointerDereference
    | `String "NullReferenceCreated" -> Ok NullReferenceCreated
    | `Assoc [ ("InvalidEnumConstruction", _0) ] ->
        let* _0 = operand_of_json ctx _0 in
        Ok (InvalidEnumConstruction _0)
    | `String "ResumedAfterReturn" -> Ok ResumedAfterReturn
    | `String "ResumedAfterPanic" -> Ok ResumedAfterPanic
    | `String "ResumedAfterDrop" -> Ok ResumedAfterDrop
    | _ -> Error "")

and builtin_fun_id_of_json (ctx : of_json_ctx) (js : json) :
    (builtin_fun_id, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `String "BoxNew" -> Ok BoxNew
    | `String "ArrayToSliceShared" -> Ok ArrayToSliceShared
    | `String "ArrayToSliceMut" -> Ok ArrayToSliceMut
    | `String "ArrayRepeat" -> Ok ArrayRepeat
    | `Assoc [ ("Index", _0) ] ->
        let* _0 = builtin_index_op_of_json ctx _0 in
        Ok (Index _0)
    | `Assoc [ ("PtrFromParts", _0) ] ->
        let* _0 = ref_kind_of_json ctx _0 in
        Ok (PtrFromParts _0)
    | _ -> Error "")

and builtin_impl_data_of_json (ctx : of_json_ctx) (js : json) :
    (builtin_impl_data, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `String "Auto" -> Ok BuiltinAuto
    | `String "Sized" -> Ok BuiltinSized
    | `String "MetaSized" -> Ok BuiltinMetaSized
    | `String "PointeeSized" -> Ok BuiltinPointeeSized
    | `String "Copy" -> Ok BuiltinCopy
    | `String "Clone" -> Ok BuiltinClone
    | `String "Tuple" -> Ok BuiltinTuple
    | `String "Transmute" -> Ok BuiltinTransmute
    | `String "Unsize" -> Ok BuiltinUnsize
    | `String "Pointee" -> Ok BuiltinPointee
    | `String "DiscriminantKind" -> Ok BuiltinDiscriminantKind
    | `String "Fn" -> Ok BuiltinFn
    | `String "FnMut" -> Ok BuiltinFnMut
    | `String "FnOnce" -> Ok BuiltinFnOnce
    | `String "FnPtr" -> Ok BuiltinFnPtr
    | `String "AsyncFn" -> Ok BuiltinAsyncFn
    | `String "AsyncFnMut" -> Ok BuiltinAsyncFnMut
    | `String "AsyncFnOnce" -> Ok BuiltinAsyncFnOnce
    | `String "Coroutine" -> Ok BuiltinCoroutine
    | `String "Future" -> Ok BuiltinFuture
    | `String "TryAsDynCompatible" -> Ok BuiltinTryAsDynCompatible
    | `String "NoopDestruct" -> Ok BuiltinNoopDestruct
    | `String "UntrackedDestruct" -> Ok BuiltinUntrackedDestruct
    | `String "RemovedAdtClause" -> Ok BuiltinRemovedAdtClause
    | _ -> Error "")

and builtin_index_op_of_json (ctx : of_json_ctx) (js : json) :
    (builtin_index_op, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc
        [
          ("is_array", is_array);
          ("mutability", mutability);
          ("is_range", is_range);
        ] ->
        let* is_array = bool_of_json ctx is_array in
        let* mutability = ref_kind_of_json ctx mutability in
        let* is_range = bool_of_json ctx is_range in
        Ok ({ is_array; mutability; is_range } : builtin_index_op)
    | _ -> Error "")

and builtin_ty_of_json (ctx : of_json_ctx) (js : json) :
    (builtin_ty, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `String "Tuple" -> Ok TTuple
    | `String "Box" -> Ok TBox
    | `String "Str" -> Ok TStr
    | _ -> Error "")

and byte_of_json (ctx : of_json_ctx) (js : json) : (byte, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `String "Uninit" -> Ok Uninit
    | `Assoc [ ("Value", _0) ] ->
        let* _0 = int_of_json ctx _0 in
        Ok (Value _0)
    | `Assoc [ ("Provenance", `List [ _0; _1 ]) ] ->
        let* _0 = provenance_of_json ctx _0 in
        let* _1 = int_of_json ctx _1 in
        Ok (Provenance (_0, _1))
    | _ -> Error "")

and call_of_json (ctx : of_json_ctx) (js : json) : (call, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("func", func); ("args", args); ("dest", dest) ] ->
        let* func = fn_operand_of_json ctx func in
        let* args = list_of_json operand_of_json ctx args in
        let* dest = place_of_json ctx dest in
        Ok ({ func; args; dest } : call)
    | _ -> Error "")

and cast_kind_of_json (ctx : of_json_ctx) (js : json) :
    (cast_kind, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Scalar", `List [ _0; _1 ]) ] ->
        let* _0 = literal_type_of_json ctx _0 in
        let* _1 = literal_type_of_json ctx _1 in
        Ok (CastScalar (_0, _1))
    | `Assoc [ ("RawPtr", `List [ _0; _1 ]) ] ->
        let* _0 = ty_of_json ctx _0 in
        let* _1 = ty_of_json ctx _1 in
        Ok (CastRawPtr (_0, _1))
    | `Assoc [ ("FnPtr", `List [ _0; _1 ]) ] ->
        let* _0 = ty_of_json ctx _0 in
        let* _1 = ty_of_json ctx _1 in
        Ok (CastFnPtr (_0, _1))
    | `Assoc [ ("Unsize", `List [ _0; _1; _2 ]) ] ->
        let* _0 = ty_of_json ctx _0 in
        let* _1 = ty_of_json ctx _1 in
        let* _2 = unsizing_metadata_of_json ctx _2 in
        Ok (CastUnsize (_0, _1, _2))
    | `Assoc [ ("Transmute", `List [ _0; _1 ]) ] ->
        let* _0 = ty_of_json ctx _0 in
        let* _1 = ty_of_json ctx _1 in
        Ok (CastTransmute (_0, _1))
    | `Assoc [ ("Concretize", `List [ _0; _1 ]) ] ->
        let* _0 = ty_of_json ctx _0 in
        let* _1 = ty_of_json ctx _1 in
        Ok (CastConcretize (_0, _1))
    | _ -> Error "")

and const_generic_param_of_json (ctx : of_json_ctx) (js : json) :
    (const_generic_param, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("index", index); ("name", name); ("ty", ty) ] ->
        let* index = const_generic_var_id_of_json ctx index in
        let* name = string_of_json ctx name in
        let* ty = ty_of_json ctx ty in
        Ok ({ index; name; ty } : const_generic_param)
    | _ -> Error "")

and const_generic_var_id_of_json (ctx : of_json_ctx) (js : json) :
    (const_generic_var_id, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | x -> ConstGenericVarId.id_of_json ctx x
    | _ -> Error "")

and constant_expr_of_json (ctx : of_json_ctx) (js : json) :
    (constant_expr, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("kind", kind); ("ty", ty) ] ->
        let* kind = constant_expr_kind_of_json ctx kind in
        let* ty = ty_of_json ctx ty in
        Ok ({ kind; ty } : constant_expr)
    | _ -> Error "")

and constant_expr_kind_of_json (ctx : of_json_ctx) (js : json) :
    (constant_expr_kind, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Literal", _0) ] ->
        let* _0 = literal_of_json ctx _0 in
        Ok (CLiteral _0)
    | `Assoc [ ("Adt", `List [ _0; _1 ]) ] ->
        let* _0 = option_of_json variant_id_of_json ctx _0 in
        let* _1 = list_of_json constant_expr_of_json ctx _1 in
        Ok (CAdt (_0, _1))
    | `Assoc [ ("Array", _0) ] ->
        let* _0 = list_of_json constant_expr_of_json ctx _0 in
        Ok (CArray _0)
    | `Assoc [ ("Global", _0) ] ->
        let* _0 = global_decl_ref_of_json ctx _0 in
        Ok (CGlobal _0)
    | `Assoc [ ("TraitConst", `List [ _0; _1 ]) ] ->
        let* _0 = trait_ref_of_json ctx _0 in
        let* _1 = assoc_const_id_of_json ctx _1 in
        Ok (CTraitConst (_0, _1))
    | `Assoc [ ("VTableRef", _0) ] ->
        let* _0 = trait_ref_of_json ctx _0 in
        Ok (CVTableRef _0)
    | `Assoc [ ("Ref", `List [ _0; _1 ]) ] ->
        let* _0 = box_of_json constant_expr_of_json ctx _0 in
        let* _1 = option_of_json unsizing_metadata_of_json ctx _1 in
        Ok (CRef (_0, _1))
    | `Assoc [ ("Ptr", `List [ _0; _1; _2 ]) ] ->
        let* _0 = ref_kind_of_json ctx _0 in
        let* _1 = box_of_json constant_expr_of_json ctx _1 in
        let* _2 = option_of_json unsizing_metadata_of_json ctx _2 in
        Ok (CPtr (_0, _1, _2))
    | `Assoc [ ("Var", _0) ] ->
        let* _0 = de_bruijn_var_of_json const_generic_var_id_of_json ctx _0 in
        Ok (CVar _0)
    | `Assoc [ ("Call", `List [ _0; _1 ]) ] ->
        let* _0 = fn_ptr_of_json ctx _0 in
        let* _1 = list_of_json constant_expr_of_json ctx _1 in
        Ok (CCall (_0, _1))
    | `Assoc [ ("FnDef", _0) ] ->
        let* _0 = fn_ptr_of_json ctx _0 in
        Ok (CFnDef _0)
    | `Assoc [ ("FnPtr", _0) ] ->
        let* _0 = fn_ptr_of_json ctx _0 in
        Ok (CFnPtr _0)
    | `Assoc [ ("TypeId", _0) ] ->
        let* _0 = ty_of_json ctx _0 in
        Ok (CTypeId _0)
    | `Assoc [ ("PtrNoProvenance", _0) ] ->
        let* _0 = big_int_of_json ctx _0 in
        Ok (CPtrNoProvenance _0)
    | `Assoc [ ("RawMemory", _0) ] ->
        let* _0 = list_of_json byte_of_json ctx _0 in
        Ok (CRawMemory _0)
    | `Assoc [ ("Opaque", _0) ] ->
        let* _0 = string_of_json ctx _0 in
        Ok (COpaque _0)
    | _ -> Error "")

and de_bruijn_id_of_json (ctx : of_json_ctx) (js : json) :
    (de_bruijn_id, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | x -> int_of_json ctx x
    | _ -> Error "")

and de_bruijn_var_of_json :
    'a0.
    (of_json_ctx -> json -> ('a0, string) result) ->
    of_json_ctx ->
    json ->
    ('a0 de_bruijn_var, string) result =
 fun arg0_of_json ctx js ->
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Bound", `List [ _0; _1 ]) ] ->
        let* _0 = de_bruijn_id_of_json ctx _0 in
        let* _1 = arg0_of_json ctx _1 in
        Ok (Bound (_0, _1))
    | `Assoc [ ("Free", _0) ] ->
        let* _0 = arg0_of_json ctx _0 in
        Ok (Free _0)
    | _ -> Error "")

and disambiguator_of_json (ctx : of_json_ctx) (js : json) :
    (disambiguator, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | x -> Disambiguator.id_of_json ctx x
    | _ -> Error "")

and drop_kind_of_json (ctx : of_json_ctx) (js : json) :
    (drop_kind, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `String "Precise" -> Ok Precise
    | `String "Conditional" -> Ok Conditional
    | _ -> Error "")

and dyn_predicate_of_json (ctx : of_json_ctx) (js : json) :
    (dyn_predicate, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("binder", binder) ] ->
        let* binder = binder_of_json ty_of_json ctx binder in
        Ok ({ binder } : dyn_predicate)
    | _ -> Error "")

and field_id_of_json (ctx : of_json_ctx) (js : json) : (field_id, string) result
    =
  combine_error_msgs js __FUNCTION__
    (match js with
    | x -> FieldId.id_of_json ctx x
    | _ -> Error "")

and file_id_of_json (ctx : of_json_ctx) (js : json) : (file_id, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | json ->
        let* file_id = FileId.id_of_json ctx json in
        let file = FileTbl.find ctx.id_to_file_map file_id in
        Ok file
    | _ -> Error "")

and float_type_of_json (ctx : of_json_ctx) (js : json) :
    (float_type, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `String "F16" -> Ok F16
    | `String "F32" -> Ok F32
    | `String "F64" -> Ok F64
    | `String "F128" -> Ok F128
    | _ -> Error "")

and float_value_of_json (ctx : of_json_ctx) (js : json) :
    (float_value, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("value", value); ("ty", ty) ] ->
        let* float_value = string_of_json ctx value in
        let* float_ty = float_type_of_json ctx ty in
        Ok ({ float_value; float_ty } : float_value)
    | _ -> Error "")

and fn_operand_of_json (ctx : of_json_ctx) (js : json) :
    (fn_operand, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Regular", _0) ] ->
        let* _0 = fn_ptr_of_json ctx _0 in
        Ok (FnOpRegular _0)
    | `Assoc [ ("Dynamic", _0) ] ->
        let* _0 = operand_of_json ctx _0 in
        Ok (FnOpDynamic _0)
    | _ -> Error "")

and fn_ptr_of_json (ctx : of_json_ctx) (js : json) : (fn_ptr, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("kind", kind); ("generics", generics) ] ->
        let* kind = box_of_json fn_ptr_kind_of_json ctx kind in
        let* generics = box_of_json generic_args_of_json ctx generics in
        Ok ({ kind; generics } : fn_ptr)
    | _ -> Error "")

and fn_ptr_kind_of_json (ctx : of_json_ctx) (js : json) :
    (fn_ptr_kind, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Fun", _0) ] ->
        let* _0 = fun_id_of_json ctx _0 in
        Ok (FunId _0)
    | `Assoc [ ("Trait", `List [ _0; _1 ]) ] ->
        let* _0 = trait_ref_of_json ctx _0 in
        let* _1 = trait_method_id_of_json ctx _1 in
        Ok (TraitMethod (_0, _1))
    | _ -> Error "")

and fun_decl_id_of_json (ctx : of_json_ctx) (js : json) :
    (fun_decl_id, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | x -> FunDeclId.id_of_json ctx x
    | _ -> Error "")

and fun_decl_ref_of_json (ctx : of_json_ctx) (js : json) :
    (fun_decl_ref, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("id", id); ("generics", generics) ] ->
        let* id = fun_decl_id_of_json ctx id in
        let* generics = box_of_json generic_args_of_json ctx generics in
        Ok ({ id; generics } : fun_decl_ref)
    | _ -> Error "")

and fun_id_of_json (ctx : of_json_ctx) (js : json) : (fun_id, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Regular", _0) ] ->
        let* _0 = fun_decl_id_of_json ctx _0 in
        Ok (FRegular _0)
    | `Assoc [ ("Builtin", _0) ] ->
        let* _0 = builtin_fun_id_of_json ctx _0 in
        Ok (FBuiltin _0)
    | _ -> Error "")

and fun_sig_of_json (ctx : of_json_ctx) (js : json) : (fun_sig, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc
        [
          ("is_unsafe", is_unsafe);
          ("abi", abi);
          ("is_variadic", is_variadic);
          ("inputs", inputs);
          ("output", output);
        ] ->
        let* is_unsafe = bool_of_json ctx is_unsafe in
        let* abi = abi_of_json ctx abi in
        let* is_variadic = bool_of_json ctx is_variadic in
        let* inputs = list_of_json ty_of_json ctx inputs in
        let* output = ty_of_json ctx output in
        Ok ({ is_unsafe; abi; is_variadic; inputs; output } : fun_sig)
    | _ -> Error "")

and generic_args_of_json (ctx : of_json_ctx) (js : json) :
    (generic_args, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc
        [
          ("regions", regions);
          ("types", types);
          ("const_generics", const_generics);
          ("trait_refs", trait_refs);
        ] ->
        let* regions =
          index_vec_of_json region_id_of_json region_of_json ctx regions
        in
        let* types =
          index_vec_of_json type_var_id_of_json ty_of_json ctx types
        in
        let* const_generics =
          index_vec_of_json const_generic_var_id_of_json constant_expr_of_json
            ctx const_generics
        in
        let* trait_refs =
          index_vec_of_json trait_clause_id_of_json trait_ref_of_json ctx
            trait_refs
        in
        Ok ({ regions; types; const_generics; trait_refs } : generic_args)
    | _ -> Error "")

and generic_params_of_json (ctx : of_json_ctx) (js : json) :
    (generic_params, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc
        [
          ("regions", regions);
          ("types", types);
          ("const_generics", const_generics);
          ("trait_clauses", trait_clauses);
          ("regions_outlive", regions_outlive);
          ("types_outlive", types_outlive);
          ("trait_type_constraints", trait_type_constraints);
        ] ->
        let* regions =
          index_vec_of_json region_id_of_json region_param_of_json ctx regions
        in
        let* types =
          index_vec_of_json type_var_id_of_json type_param_of_json ctx types
        in
        let* const_generics =
          index_vec_of_json const_generic_var_id_of_json
            const_generic_param_of_json ctx const_generics
        in
        let* trait_clauses =
          index_vec_of_json trait_clause_id_of_json trait_param_of_json ctx
            trait_clauses
        in
        let* regions_outlive =
          list_of_json
            (region_binder_of_json
               (outlives_pred_of_json region_of_json region_of_json))
            ctx regions_outlive
        in
        let* types_outlive =
          list_of_json
            (region_binder_of_json
               (outlives_pred_of_json ty_of_json region_of_json))
            ctx types_outlive
        in
        let* trait_type_constraints =
          index_vec_of_json trait_type_constraint_id_of_json
            (region_binder_of_json trait_type_constraint_of_json)
            ctx trait_type_constraints
        in
        Ok
          ({
             regions;
             types;
             const_generics;
             trait_clauses;
             regions_outlive;
             types_outlive;
             trait_type_constraints;
           }
            : generic_params)
    | _ -> Error "")

and global_decl_id_of_json (ctx : of_json_ctx) (js : json) :
    (global_decl_id, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | x -> GlobalDeclId.id_of_json ctx x
    | _ -> Error "")

and global_decl_ref_of_json (ctx : of_json_ctx) (js : json) :
    (global_decl_ref, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("id", id); ("generics", generics) ] ->
        let* id = global_decl_id_of_json ctx id in
        let* generics = box_of_json generic_args_of_json ctx generics in
        Ok ({ id; generics } : global_decl_ref)
    | _ -> Error "")

and hash_consed_of_json :
    'a0.
    (of_json_ctx -> json -> ('a0, string) result) ->
    of_json_ctx ->
    json ->
    ('a0 hash_consed, string) result =
 fun arg0_of_json ctx js ->
  combine_error_msgs js __FUNCTION__
    (match js with
    | json -> Error "use `hash_consed_val_of_json` instead"
    | _ -> Error "")

and impl_elem_of_json (ctx : of_json_ctx) (js : json) :
    (impl_elem, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Ty", _0) ] ->
        let* _0 = box_of_json (binder_of_json ty_of_json) ctx _0 in
        Ok (ImplElemTy _0)
    | `Assoc [ ("Trait", _0) ] ->
        let* _0 = trait_impl_id_of_json ctx _0 in
        Ok (ImplElemTrait _0)
    | _ -> Error "")

and index_vec_of_json :
    'a0 'a1.
    (of_json_ctx -> json -> ('a0, string) result) ->
    (of_json_ctx -> json -> ('a1, string) result) ->
    of_json_ctx ->
    json ->
    ('a1 list, string) result =
 fun arg0_of_json arg1_of_json ctx js ->
  combine_error_msgs js __FUNCTION__
    (match js with
    | json -> list_of_json arg1_of_json ctx json
    | _ -> Error "")

and int_ty_of_json (ctx : of_json_ctx) (js : json) : (int_ty, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `String "Isize" -> Ok Isize
    | `String "I8" -> Ok I8
    | `String "I16" -> Ok I16
    | `String "I32" -> Ok I32
    | `String "I64" -> Ok I64
    | `String "I128" -> Ok I128
    | _ -> Error "")

and lifetime_mutability_of_json (ctx : of_json_ctx) (js : json) :
    (lifetime_mutability, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `String "Mutable" -> Ok LtMutable
    | `String "Shared" -> Ok LtShared
    | `String "Unknown" -> Ok LtUnknown
    | _ -> Error "")

and literal_of_json (ctx : of_json_ctx) (js : json) : (literal, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Scalar", _0) ] ->
        let* _0 = scalar_value_of_json ctx _0 in
        Ok (VScalar _0)
    | `Assoc [ ("Float", _0) ] ->
        let* _0 = float_value_of_json ctx _0 in
        Ok (VFloat _0)
    | `Assoc [ ("Bool", _0) ] ->
        let* _0 = bool_of_json ctx _0 in
        Ok (VBool _0)
    | `Assoc [ ("Char", _0) ] ->
        let* _0 = char_of_json ctx _0 in
        Ok (VChar _0)
    | `Assoc [ ("ByteStr", _0) ] ->
        let* _0 = list_of_json int_of_json ctx _0 in
        Ok (VByteStr _0)
    | `Assoc [ ("Str", _0) ] ->
        let* _0 = string_of_json ctx _0 in
        Ok (VStr _0)
    | _ -> Error "")

and literal_type_of_json (ctx : of_json_ctx) (js : json) :
    (literal_type, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Int", _0) ] ->
        let* _0 = int_ty_of_json ctx _0 in
        Ok (TInt _0)
    | `Assoc [ ("UInt", _0) ] ->
        let* _0 = u_int_ty_of_json ctx _0 in
        Ok (TUInt _0)
    | `Assoc [ ("Float", _0) ] ->
        let* _0 = float_type_of_json ctx _0 in
        Ok (TFloat _0)
    | `String "Bool" -> Ok TBool
    | `String "Char" -> Ok TChar
    | _ -> Error "")

and loc_of_json (ctx : of_json_ctx) (js : json) : (loc, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("line", line); ("col", col) ] ->
        let* line = int_of_json ctx line in
        let* col = int_of_json ctx col in
        Ok ({ line; col } : loc)
    | _ -> Error "")

and local_id_of_json (ctx : of_json_ctx) (js : json) : (local_id, string) result
    =
  combine_error_msgs js __FUNCTION__
    (match js with
    | x -> LocalId.id_of_json ctx x
    | _ -> Error "")

and name_of_json (ctx : of_json_ctx) (js : json) : (name, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | x -> list_of_json path_elem_of_json ctx x
    | _ -> Error "")

and nullop_of_json (ctx : of_json_ctx) (js : json) : (nullop, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `String "SizeOf" -> Ok SizeOf
    | `String "AlignOf" -> Ok AlignOf
    | `Assoc [ ("OffsetOf", `List [ _0; _1; _2 ]) ] ->
        let* _0 = type_decl_ref_of_json ctx _0 in
        let* _1 = option_of_json variant_id_of_json ctx _1 in
        let* _2 = field_id_of_json ctx _2 in
        Ok (OffsetOf (_0, _1, _2))
    | `String "UbChecks" -> Ok UbChecks
    | `String "OverflowChecks" -> Ok OverflowChecks
    | `String "ContractChecks" -> Ok ContractChecks
    | _ -> Error "")

and operand_of_json (ctx : of_json_ctx) (js : json) : (operand, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Copy", _0) ] ->
        let* _0 = place_of_json ctx _0 in
        Ok (Copy _0)
    | `Assoc [ ("Move", _0) ] ->
        let* _0 = place_of_json ctx _0 in
        Ok (Move _0)
    | `Assoc [ ("Const", _0) ] ->
        let* _0 = box_of_json constant_expr_of_json ctx _0 in
        Ok (Constant _0)
    | _ -> Error "")

and outlives_pred_of_json :
    'a0 'a1.
    (of_json_ctx -> json -> ('a0, string) result) ->
    (of_json_ctx -> json -> ('a1, string) result) ->
    of_json_ctx ->
    json ->
    (('a0, 'a1) outlives_pred, string) result =
 fun arg0_of_json arg1_of_json ctx js ->
  combine_error_msgs js __FUNCTION__
    (match js with
    | `List [ _0; _1 ] ->
        let* _0 = arg0_of_json ctx _0 in
        let* _1 = arg1_of_json ctx _1 in
        Ok (_0, _1)
    | _ -> Error "")

and overflow_mode_of_json (ctx : of_json_ctx) (js : json) :
    (overflow_mode, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `String "Panic" -> Ok OPanic
    | `String "UB" -> Ok OUB
    | `String "Wrap" -> Ok OWrap
    | _ -> Error "")

and path_elem_of_json (ctx : of_json_ctx) (js : json) :
    (path_elem, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Ident", `List [ _0; _1 ]) ] ->
        let* _0 = string_of_json ctx _0 in
        let* _1 = disambiguator_of_json ctx _1 in
        Ok (PeIdent (_0, _1))
    | `Assoc [ ("Impl", _0) ] ->
        let* _0 = impl_elem_of_json ctx _0 in
        Ok (PeImpl _0)
    | `Assoc [ ("Instantiated", _0) ] ->
        let* _0 = box_of_json (binder_of_json generic_args_of_json) ctx _0 in
        Ok (PeInstantiated _0)
    | `Assoc [ ("Target", _0) ] ->
        let* _0 = string_of_json ctx _0 in
        Ok (PeTarget _0)
    | _ -> Error "")

and place_of_json (ctx : of_json_ctx) (js : json) : (place, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("kind", kind); ("ty", ty) ] ->
        let* kind = place_kind_of_json ctx kind in
        let* ty = ty_of_json ctx ty in
        Ok ({ kind; ty } : place)
    | _ -> Error "")

and place_kind_of_json (ctx : of_json_ctx) (js : json) :
    (place_kind, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Local", _0) ] ->
        let* _0 = local_id_of_json ctx _0 in
        Ok (PlaceLocal _0)
    | `Assoc [ ("Projection", `List [ _0; _1 ]) ] ->
        let* _0 = box_of_json place_of_json ctx _0 in
        let* _1 = projection_elem_of_json ctx _1 in
        Ok (PlaceProjection (_0, _1))
    | `Assoc [ ("Global", _0) ] ->
        let* _0 = global_decl_ref_of_json ctx _0 in
        Ok (PlaceGlobal _0)
    | _ -> Error "")

and predicate_origin_of_json (ctx : of_json_ctx) (js : json) :
    (predicate_origin, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `String "WhereClauseOnFn" -> Ok WhereClauseOnFn
    | `String "WhereClauseOnType" -> Ok WhereClauseOnType
    | `String "WhereClauseOnImpl" -> Ok WhereClauseOnImpl
    | `String "TraitSelf" -> Ok TraitSelf
    | `String "WhereClauseOnTrait" -> Ok WhereClauseOnTrait
    | `Assoc [ ("TraitItem", _0) ] ->
        let* _0 = assoc_type_id_of_json ctx _0 in
        Ok (TraitItem _0)
    | `String "Dyn" -> Ok OriginDyn
    | _ -> Error "")

and projection_elem_of_json (ctx : of_json_ctx) (js : json) :
    (projection_elem, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `String "Deref" -> Ok Deref
    | `Assoc [ ("Field", `List [ _0; _1 ]) ] ->
        let* _0 = option_of_json variant_id_of_json ctx _0 in
        let* _1 = field_id_of_json ctx _1 in
        Ok (Field (_0, _1))
    | `String "PtrMetadata" -> Ok PtrMetadata
    | `Assoc
        [ ("Index", `Assoc [ ("offset", offset); ("from_end", from_end) ]) ] ->
        let* offset = box_of_json operand_of_json ctx offset in
        let* from_end = bool_of_json ctx from_end in
        Ok (ProjIndex (offset, from_end))
    | `Assoc
        [
          ( "Subslice",
            `Assoc [ ("from", from); ("to", to_); ("from_end", from_end) ] );
        ] ->
        let* from = box_of_json operand_of_json ctx from in
        let* to_ = box_of_json operand_of_json ctx to_ in
        let* from_end = bool_of_json ctx from_end in
        Ok (Subslice (from, to_, from_end))
    | _ -> Error "")

and provenance_of_json (ctx : of_json_ctx) (js : json) :
    (provenance, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Global", _0) ] ->
        let* _0 = global_decl_ref_of_json ctx _0 in
        Ok (ProvGlobal _0)
    | `Assoc [ ("Function", _0) ] ->
        let* _0 = fun_decl_ref_of_json ctx _0 in
        Ok (ProvFunction _0)
    | `String "Unknown" -> Ok ProvUnknown
    | _ -> Error "")

and ref_kind_of_json (ctx : of_json_ctx) (js : json) : (ref_kind, string) result
    =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `String "Mut" -> Ok RMut
    | `String "Shared" -> Ok RShared
    | _ -> Error "")

and region_of_json (ctx : of_json_ctx) (js : json) : (region, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Var", _0) ] ->
        let* _0 = de_bruijn_var_of_json region_id_of_json ctx _0 in
        Ok (RVar _0)
    | `String "Static" -> Ok RStatic
    | `Assoc [ ("Body", _0) ] ->
        let* _0 = region_id_of_json ctx _0 in
        Ok (RBody _0)
    | `String "Erased" -> Ok RErased
    | _ -> Error "")

and region_binder_of_json :
    'a0.
    (of_json_ctx -> json -> ('a0, string) result) ->
    of_json_ctx ->
    json ->
    ('a0 region_binder, string) result =
 fun arg0_of_json ctx js ->
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("regions", regions); ("skip_binder", skip_binder) ] ->
        let* binder_regions =
          index_vec_of_json region_id_of_json region_param_of_json ctx regions
        in
        let* binder_value = arg0_of_json ctx skip_binder in
        Ok ({ binder_regions; binder_value } : _ region_binder)
    | _ -> Error "")

and region_id_of_json (ctx : of_json_ctx) (js : json) :
    (region_id, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | x -> RegionId.id_of_json ctx x
    | _ -> Error "")

and region_param_of_json (ctx : of_json_ctx) (js : json) :
    (region_param, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc
        [
          ("index", index);
          ("name", name);
          ("variance", variance);
          ("mutability", mutability);
        ] ->
        let* index = region_id_of_json ctx index in
        let* name = option_of_json string_of_json ctx name in
        let* variance = variance_of_json ctx variance in
        let* mutability = lifetime_mutability_of_json ctx mutability in
        Ok ({ index; name; variance; mutability } : region_param)
    | _ -> Error "")

and rvalue_of_json (ctx : of_json_ctx) (js : json) : (rvalue, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Use", `List [ _0; _1 ]) ] ->
        let* _0 = operand_of_json ctx _0 in
        let* _1 = with_retag_of_json ctx _1 in
        Ok (Use (_0, _1))
    | `Assoc
        [
          ( "Ref",
            `Assoc
              [
                ("place", place); ("kind", kind); ("ptr_metadata", ptr_metadata);
              ] );
        ] ->
        let* place = place_of_json ctx place in
        let* kind = borrow_kind_of_json ctx kind in
        let* ptr_metadata = operand_of_json ctx ptr_metadata in
        Ok (RvRef (place, kind, ptr_metadata))
    | `Assoc
        [
          ( "RawPtr",
            `Assoc
              [
                ("place", place); ("kind", kind); ("ptr_metadata", ptr_metadata);
              ] );
        ] ->
        let* place = place_of_json ctx place in
        let* kind = ref_kind_of_json ctx kind in
        let* ptr_metadata = operand_of_json ctx ptr_metadata in
        Ok (RawPtr (place, kind, ptr_metadata))
    | `Assoc [ ("BinaryOp", `List [ _0; _1; _2 ]) ] ->
        let* _0 = binop_of_json ctx _0 in
        let* _1 = operand_of_json ctx _1 in
        let* _2 = operand_of_json ctx _2 in
        Ok (BinaryOp (_0, _1, _2))
    | `Assoc [ ("UnaryOp", `List [ _0; _1 ]) ] ->
        let* _0 = unop_of_json ctx _0 in
        let* _1 = operand_of_json ctx _1 in
        Ok (UnaryOp (_0, _1))
    | `Assoc [ ("NullaryOp", `List [ _0; _1 ]) ] ->
        let* _0 = nullop_of_json ctx _0 in
        let* _1 = ty_of_json ctx _1 in
        Ok (NullaryOp (_0, _1))
    | `Assoc [ ("Discriminant", _0) ] ->
        let* _0 = place_of_json ctx _0 in
        Ok (Discriminant _0)
    | `Assoc [ ("Aggregate", `List [ _0; _1 ]) ] ->
        let* _0 = aggregate_kind_of_json ctx _0 in
        let* _1 = list_of_json operand_of_json ctx _1 in
        Ok (Aggregate (_0, _1))
    | `Assoc [ ("Len", `List [ _0; _1; _2 ]) ] ->
        let* _0 = place_of_json ctx _0 in
        let* _1 = ty_of_json ctx _1 in
        let* _2 = option_of_json (box_of_json constant_expr_of_json) ctx _2 in
        Ok (Len (_0, _1, _2))
    | `Assoc [ ("Repeat", `List [ _0; _1; _2 ]) ] ->
        let* _0 = operand_of_json ctx _0 in
        let* _1 = ty_of_json ctx _1 in
        let* _2 = box_of_json constant_expr_of_json ctx _2 in
        Ok (Repeat (_0, _1, _2))
    | _ -> Error "")

and scalar_value_of_json (ctx : of_json_ctx) (js : json) :
    (scalar_value, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Unsigned", `List [ _0; _1 ]) ] ->
        let* _0 = u_int_ty_of_json ctx _0 in
        let* _1 = big_int_of_json ctx _1 in
        Ok (UnsignedScalar (_0, _1))
    | `Assoc [ ("Signed", `List [ _0; _1 ]) ] ->
        let* _0 = int_ty_of_json ctx _0 in
        let* _1 = big_int_of_json ctx _1 in
        Ok (SignedScalar (_0, _1))
    | _ -> Error "")

and span_of_json (ctx : of_json_ctx) (js : json) : (span, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("data", data); ("generated_from_span", generated_from_span) ] ->
        let* data = span_data_of_json ctx data in
        let* generated_from_span =
          option_of_json span_data_of_json ctx generated_from_span
        in
        Ok ({ data; generated_from_span } : span)
    | _ -> Error "")

and span_data_of_json (ctx : of_json_ctx) (js : json) :
    (span_data, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("file_id", file_id); ("beg", beg); ("end", end_) ] ->
        let* file = file_id_of_json ctx file_id in
        let* beg_loc = loc_of_json ctx beg in
        let* end_loc = loc_of_json ctx end_ in
        Ok ({ file; beg_loc; end_loc } : span_data)
    | _ -> Error "")

and trait_assoc_ty_impl_of_json (ctx : of_json_ctx) (js : json) :
    (trait_assoc_ty_impl, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("value", value); ("implied_trait_refs", implied_trait_refs) ] ->
        let* value = ty_of_json ctx value in
        let* implied_trait_refs =
          index_vec_of_json trait_clause_id_of_json trait_ref_of_json ctx
            implied_trait_refs
        in
        Ok ({ value; implied_trait_refs } : trait_assoc_ty_impl)
    | _ -> Error "")

and trait_clause_id_of_json (ctx : of_json_ctx) (js : json) :
    (trait_clause_id, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | x -> TraitClauseId.id_of_json ctx x
    | _ -> Error "")

and trait_decl_id_of_json (ctx : of_json_ctx) (js : json) :
    (trait_decl_id, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | x -> TraitDeclId.id_of_json ctx x
    | _ -> Error "")

and trait_decl_ref_of_json (ctx : of_json_ctx) (js : json) :
    (trait_decl_ref, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("id", id); ("generics", generics) ] ->
        let* id = trait_decl_id_of_json ctx id in
        let* generics = box_of_json generic_args_of_json ctx generics in
        Ok ({ id; generics } : trait_decl_ref)
    | _ -> Error "")

and trait_impl_id_of_json (ctx : of_json_ctx) (js : json) :
    (trait_impl_id, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | x -> TraitImplId.id_of_json ctx x
    | _ -> Error "")

and trait_impl_ref_of_json (ctx : of_json_ctx) (js : json) :
    (trait_impl_ref, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("id", id); ("generics", generics) ] ->
        let* id = trait_impl_id_of_json ctx id in
        let* generics = box_of_json generic_args_of_json ctx generics in
        Ok ({ id; generics } : trait_impl_ref)
    | _ -> Error "")

and trait_method_id_of_json (ctx : of_json_ctx) (js : json) :
    (trait_method_id, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | x -> TraitMethodId.id_of_json ctx x
    | _ -> Error "")

and trait_param_of_json (ctx : of_json_ctx) (js : json) :
    (trait_param, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc
        [
          ("clause_id", clause_id);
          ("span", span);
          ("origin", origin);
          ("trait_", trait);
        ] ->
        let* clause_id = trait_clause_id_of_json ctx clause_id in
        let* span = option_of_json span_of_json ctx span in
        let* origin = predicate_origin_of_json ctx origin in
        let* trait = region_binder_of_json trait_decl_ref_of_json ctx trait in
        Ok ({ clause_id; span; origin; trait } : trait_param)
    | _ -> Error "")

and trait_ref_of_json (ctx : of_json_ctx) (js : json) :
    (trait_ref, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | json ->
        hash_consed_val_of_json ctx.tref_hashcons_map trait_ref_contents_of_json
          ctx json
    | _ -> Error "")

and trait_ref_contents_of_json (ctx : of_json_ctx) (js : json) :
    (trait_ref_contents, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("kind", kind); ("trait_decl_ref", trait_decl_ref) ] ->
        let* kind = trait_ref_kind_of_json ctx kind in
        let* trait_decl_ref =
          region_binder_of_json trait_decl_ref_of_json ctx trait_decl_ref
        in
        Ok ({ kind; trait_decl_ref } : trait_ref_contents)
    | _ -> Error "")

and trait_ref_kind_of_json (ctx : of_json_ctx) (js : json) :
    (trait_ref_kind, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("TraitImpl", _0) ] ->
        let* _0 = trait_impl_ref_of_json ctx _0 in
        Ok (TraitImpl _0)
    | `Assoc [ ("Clause", _0) ] ->
        let* _0 = de_bruijn_var_of_json trait_clause_id_of_json ctx _0 in
        Ok (Clause _0)
    | `Assoc [ ("ParentClause", `List [ _0; _1 ]) ] ->
        let* _0 = box_of_json trait_ref_of_json ctx _0 in
        let* _1 = trait_clause_id_of_json ctx _1 in
        Ok (ParentClause (_0, _1))
    | `Assoc [ ("ItemClause", `List [ _0; _1; _2 ]) ] ->
        let* _0 = box_of_json trait_ref_of_json ctx _0 in
        let* _1 = assoc_type_id_of_json ctx _1 in
        let* _2 = trait_clause_id_of_json ctx _2 in
        Ok (ItemClause (_0, _1, _2))
    | `String "SelfId" -> Ok Self
    | `Assoc
        [
          ( "BuiltinOrAuto",
            `Assoc
              [
                ("builtin_data", builtin_data);
                ("parent_trait_refs", parent_trait_refs);
                ("types", types);
              ] );
        ] ->
        let* builtin_data = builtin_impl_data_of_json ctx builtin_data in
        let* parent_trait_refs =
          index_vec_of_json trait_clause_id_of_json trait_ref_of_json ctx
            parent_trait_refs
        in
        let* types =
          (fun ctx json ->
            Result.map AssocTypeId.map_of_indexed_list
              (opt_indexed_map_of_json assoc_type_id_of_json
                 trait_assoc_ty_impl_of_json ctx json))
            ctx types
        in
        Ok (BuiltinOrAuto (builtin_data, parent_trait_refs, types))
    | `String "Dyn" -> Ok Dyn
    | `Assoc [ ("Unknown", _0) ] ->
        let* _0 = string_of_json ctx _0 in
        Ok (UnknownTrait _0)
    | _ -> Error "")

and trait_type_constraint_of_json (ctx : of_json_ctx) (js : json) :
    (trait_type_constraint, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("trait_ref", trait_ref); ("type_id", type_id); ("ty", ty) ] ->
        let* trait_ref = trait_ref_of_json ctx trait_ref in
        let* type_id = assoc_type_id_of_json ctx type_id in
        let* ty = ty_of_json ctx ty in
        Ok ({ trait_ref; type_id; ty } : trait_type_constraint)
    | _ -> Error "")

and trait_type_constraint_id_of_json (ctx : of_json_ctx) (js : json) :
    (trait_type_constraint_id, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | x -> TraitTypeConstraintId.id_of_json ctx x
    | _ -> Error "")

and ty_of_json (ctx : of_json_ctx) (js : json) : (ty, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | json ->
        hash_consed_val_of_json ctx.ty_hashcons_map ty_kind_of_json ctx json
    | _ -> Error "")

and ty_kind_of_json (ctx : of_json_ctx) (js : json) : (ty_kind, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Adt", _0) ] ->
        let* _0 = type_decl_ref_of_json ctx _0 in
        Ok (TAdt _0)
    | `Assoc [ ("TypeVar", _0) ] ->
        let* _0 = de_bruijn_var_of_json type_var_id_of_json ctx _0 in
        Ok (TVar _0)
    | `Assoc [ ("Literal", _0) ] ->
        let* _0 = literal_type_of_json ctx _0 in
        Ok (TLiteral _0)
    | `String "Never" -> Ok TNever
    | `Assoc [ ("Ref", `List [ _0; _1; _2 ]) ] ->
        let* _0 = region_of_json ctx _0 in
        let* _1 = ty_of_json ctx _1 in
        let* _2 = ref_kind_of_json ctx _2 in
        Ok (TRef (_0, _1, _2))
    | `Assoc [ ("RawPtr", `List [ _0; _1 ]) ] ->
        let* _0 = ty_of_json ctx _0 in
        let* _1 = ref_kind_of_json ctx _1 in
        Ok (TRawPtr (_0, _1))
    | `Assoc [ ("TraitType", `List [ _0; _1; _2 ]) ] ->
        let* _0 = trait_ref_of_json ctx _0 in
        let* _1 = assoc_type_id_of_json ctx _1 in
        let* _2 = generic_args_of_json ctx _2 in
        Ok (TTraitType (_0, _1, _2))
    | `Assoc [ ("DynTrait", _0) ] ->
        let* _0 = dyn_predicate_of_json ctx _0 in
        Ok (TDynTrait _0)
    | `Assoc [ ("FnPtr", _0) ] ->
        let* _0 = region_binder_of_json fun_sig_of_json ctx _0 in
        Ok (TFnPtr _0)
    | `Assoc [ ("FnDef", _0) ] ->
        let* _0 = region_binder_of_json fn_ptr_of_json ctx _0 in
        Ok (TFnDef _0)
    | `Assoc [ ("PtrMetadata", _0) ] ->
        let* _0 = ty_of_json ctx _0 in
        Ok (TPtrMetadata _0)
    | `Assoc [ ("Array", `List [ _0; _1 ]) ] ->
        let* _0 = ty_of_json ctx _0 in
        let* _1 = box_of_json constant_expr_of_json ctx _1 in
        Ok (TArray (_0, _1))
    | `Assoc [ ("Slice", _0) ] ->
        let* _0 = ty_of_json ctx _0 in
        Ok (TSlice _0)
    | `Assoc [ ("Pattern", `List [ _0; _1 ]) ] ->
        let* _0 = ty_of_json ctx _0 in
        let* _1 = type_pattern_of_json ctx _1 in
        Ok (TPattern (_0, _1))
    | `Assoc [ ("Error", _0) ] ->
        let* _0 = string_of_json ctx _0 in
        Ok (TError _0)
    | _ -> Error "")

and type_decl_id_of_json (ctx : of_json_ctx) (js : json) :
    (type_decl_id, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | x -> TypeDeclId.id_of_json ctx x
    | _ -> Error "")

and type_decl_ref_of_json (ctx : of_json_ctx) (js : json) :
    (type_decl_ref, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("id", id); ("generics", generics) ] ->
        let* id = type_id_of_json ctx id in
        let* generics = box_of_json generic_args_of_json ctx generics in
        Ok ({ id; generics } : type_decl_ref)
    | _ -> Error "")

and type_id_of_json (ctx : of_json_ctx) (js : json) : (type_id, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Adt", _0) ] ->
        let* _0 = type_decl_id_of_json ctx _0 in
        Ok (TAdtId _0)
    | `Assoc [ ("Builtin", _0) ] ->
        let* _0 = builtin_ty_of_json ctx _0 in
        Ok (TBuiltin _0)
    | _ -> Error "")

and type_param_of_json (ctx : of_json_ctx) (js : json) :
    (type_param, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("index", index); ("name", name); ("variance", variance) ] ->
        let* index = type_var_id_of_json ctx index in
        let* name = string_of_json ctx name in
        let* variance = variance_of_json ctx variance in
        Ok ({ index; name; variance } : type_param)
    | _ -> Error "")

and type_pattern_of_json (ctx : of_json_ctx) (js : json) :
    (type_pattern, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Range", `List [ _0; _1 ]) ] ->
        let* _0 = box_of_json constant_expr_of_json ctx _0 in
        let* _1 = box_of_json constant_expr_of_json ctx _1 in
        Ok (Range (_0, _1))
    | `Assoc [ ("OrPattern", _0) ] ->
        let* _0 = list_of_json type_pattern_of_json ctx _0 in
        Ok (OrPattern _0)
    | `String "NotNull" -> Ok NotNull
    | _ -> Error "")

and type_var_id_of_json (ctx : of_json_ctx) (js : json) :
    (type_var_id, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | x -> TypeVarId.id_of_json ctx x
    | _ -> Error "")

and u_int_ty_of_json (ctx : of_json_ctx) (js : json) : (u_int_ty, string) result
    =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `String "Usize" -> Ok Usize
    | `String "U8" -> Ok U8
    | `String "U16" -> Ok U16
    | `String "U32" -> Ok U32
    | `String "U64" -> Ok U64
    | `String "U128" -> Ok U128
    | _ -> Error "")

and unop_of_json (ctx : of_json_ctx) (js : json) : (unop, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `String "Not" -> Ok Not
    | `Assoc [ ("Neg", _0) ] ->
        let* _0 = overflow_mode_of_json ctx _0 in
        Ok (Neg _0)
    | `Assoc [ ("Cast", _0) ] ->
        let* _0 = cast_kind_of_json ctx _0 in
        Ok (Cast _0)
    | _ -> Error "")

and unsizing_metadata_of_json (ctx : of_json_ctx) (js : json) :
    (unsizing_metadata, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Length", _0) ] ->
        let* _0 = box_of_json constant_expr_of_json ctx _0 in
        Ok (MetaLength _0)
    | `Assoc [ ("VTable", `List [ _0; _1 ]) ] ->
        let* _0 = trait_ref_of_json ctx _0 in
        let* _1 = box_of_json constant_expr_of_json ctx _1 in
        Ok (MetaVTable (_0, _1))
    | `Assoc [ ("VTableUpcast", _0) ] ->
        let* _0 = list_of_json field_id_of_json ctx _0 in
        Ok (MetaVTableUpcast _0)
    | `String "Unknown" -> Ok MetaUnknown
    | _ -> Error "")

and variance_of_json (ctx : of_json_ctx) (js : json) : (variance, string) result
    =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `String "Covariant" -> Ok Covariant
    | `String "Invariant" -> Ok Invariant
    | `String "Contravariant" -> Ok Contravariant
    | `String "Bivariant" -> Ok Bivariant
    | `String "Unknown" -> Ok VaUnknown
    | _ -> Error "")

and variant_id_of_json (ctx : of_json_ctx) (js : json) :
    (variant_id, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | x -> VariantId.id_of_json ctx x
    | _ -> Error "")

and with_retag_of_json (ctx : of_json_ctx) (js : json) :
    (with_retag, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `String "No" -> Ok NoRetag
    | `String "Yes" -> Ok YesRetag
    | _ -> Error "")

module Ullbc = struct
  open UllbcAst

  let rec ___ = ()

  and block_of_json (ctx : of_json_ctx) (js : json) :
      (Generated_UllbcAst.block, string) result =
    combine_error_msgs js __FUNCTION__
      (match js with
      | `Assoc [ ("statements", statements); ("terminator", terminator) ] ->
          let* statements = list_of_json statement_of_json ctx statements in
          let* terminator = terminator_of_json ctx terminator in
          Ok ({ statements; terminator } : Generated_UllbcAst.block)
      | _ -> Error "")

  and block_id_of_json (ctx : of_json_ctx) (js : json) :
      (Generated_UllbcAst.block_id, string) result =
    combine_error_msgs js __FUNCTION__
      (match js with
      | x -> BlockId.id_of_json ctx x
      | _ -> Error "")

  and statement_of_json (ctx : of_json_ctx) (js : json) :
      (Generated_UllbcAst.statement, string) result =
    combine_error_msgs js __FUNCTION__
      (match js with
      | `Assoc
          [
            ("span", span); ("kind", kind); ("comments_before", comments_before);
          ] ->
          let* span = span_of_json ctx span in
          let* kind = statement_kind_of_json ctx kind in
          let* comments_before =
            list_of_json string_of_json ctx comments_before
          in
          Ok ({ span; kind; comments_before } : Generated_UllbcAst.statement)
      | _ -> Error "")

  and statement_kind_of_json (ctx : of_json_ctx) (js : json) :
      (Generated_UllbcAst.statement_kind, string) result =
    combine_error_msgs js __FUNCTION__
      (match js with
      | `Assoc [ ("Assign", `List [ _0; _1 ]) ] ->
          let* _0 = place_of_json ctx _0 in
          let* _1 = rvalue_of_json ctx _1 in
          Ok (Assign (_0, _1))
      | `Assoc [ ("SetDiscriminant", `List [ _0; _1 ]) ] ->
          let* _0 = place_of_json ctx _0 in
          let* _1 = variant_id_of_json ctx _1 in
          Ok (SetDiscriminant (_0, _1))
      | `Assoc [ ("StorageLive", _0) ] ->
          let* _0 = local_id_of_json ctx _0 in
          Ok (StorageLive _0)
      | `Assoc [ ("StorageDead", _0) ] ->
          let* _0 = local_id_of_json ctx _0 in
          Ok (StorageDead _0)
      | `Assoc [ ("PlaceMention", _0) ] ->
          let* _0 = place_of_json ctx _0 in
          Ok (PlaceMention _0)
      | `Assoc [ ("Borrowck", _0) ] ->
          let* _0 = borrowck_statement_of_json ctx _0 in
          Ok (Borrowck _0)
      | `Assoc
          [
            ( "Assert",
              `Assoc [ ("assert", assert_); ("on_failure", on_failure) ] );
          ] ->
          let* assert_ = assertion_of_json ctx assert_ in
          let* on_failure = abort_kind_of_json ctx on_failure in
          Ok (Assert (assert_, on_failure))
      | `String "Nop" -> Ok Nop
      | _ -> Error "")

  and switch_of_json (ctx : of_json_ctx) (js : json) :
      (Generated_UllbcAst.switch, string) result =
    combine_error_msgs js __FUNCTION__
      (match js with
      | `Assoc [ ("If", `List [ _0; _1 ]) ] ->
          let* _0 = block_id_of_json ctx _0 in
          let* _1 = block_id_of_json ctx _1 in
          Ok (If (_0, _1))
      | `Assoc [ ("SwitchInt", `List [ _0; _1; _2 ]) ] ->
          let* _0 = literal_type_of_json ctx _0 in
          let* _1 =
            list_of_json (pair_of_json literal_of_json block_id_of_json) ctx _1
          in
          let* _2 = block_id_of_json ctx _2 in
          Ok (SwitchInt (_0, _1, _2))
      | _ -> Error "")

  and terminator_of_json (ctx : of_json_ctx) (js : json) :
      (terminator, string) result =
    combine_error_msgs js __FUNCTION__
      (match js with
      | `Assoc
          [
            ("span", span); ("kind", kind); ("comments_before", comments_before);
          ] ->
          let* span = span_of_json ctx span in
          let* kind = terminator_kind_of_json ctx kind in
          let* comments_before =
            list_of_json string_of_json ctx comments_before
          in
          Ok ({ span; kind; comments_before } : terminator)
      | _ -> Error "")

  and terminator_kind_of_json (ctx : of_json_ctx) (js : json) :
      (terminator_kind, string) result =
    combine_error_msgs js __FUNCTION__
      (match js with
      | `Assoc [ ("Goto", `Assoc [ ("target", target) ]) ] ->
          let* target = block_id_of_json ctx target in
          Ok (Goto target)
      | `Assoc [ ("Switch", `Assoc [ ("discr", discr); ("targets", targets) ]) ]
        ->
          let* discr = operand_of_json ctx discr in
          let* targets = switch_of_json ctx targets in
          Ok (Switch (discr, targets))
      | `Assoc
          [
            ( "Call",
              `Assoc
                [ ("call", call); ("target", target); ("on_unwind", on_unwind) ]
            );
          ] ->
          let* call = call_of_json ctx call in
          let* target = block_id_of_json ctx target in
          let* on_unwind = block_id_of_json ctx on_unwind in
          Ok (Call (call, target, on_unwind))
      | `Assoc
          [
            ( "Drop",
              `Assoc
                [
                  ("kind", kind);
                  ("place", place);
                  ("fn_ptr", fn_ptr);
                  ("target", target);
                  ("on_unwind", on_unwind);
                ] );
          ] ->
          let* kind = drop_kind_of_json ctx kind in
          let* place = place_of_json ctx place in
          let* fn_ptr = fn_ptr_of_json ctx fn_ptr in
          let* target = block_id_of_json ctx target in
          let* on_unwind = block_id_of_json ctx on_unwind in
          Ok (Drop (kind, place, fn_ptr, target, on_unwind))
      | `Assoc
          [
            ( "Assert",
              `Assoc
                [
                  ("assert", assert_);
                  ("target", target);
                  ("on_unwind", on_unwind);
                ] );
          ] ->
          let* assert_ = assertion_of_json ctx assert_ in
          let* target = block_id_of_json ctx target in
          let* on_unwind = block_id_of_json ctx on_unwind in
          Ok (TAssert (assert_, target, on_unwind))
      | `Assoc
          [
            ( "InlineAsm",
              `Assoc
                [ ("asm", asm); ("targets", targets); ("on_unwind", on_unwind) ]
            );
          ] ->
          let* asm = string_of_json ctx asm in
          let* targets = list_of_json block_id_of_json ctx targets in
          let* on_unwind = block_id_of_json ctx on_unwind in
          Ok (InlineAsm (asm, targets, on_unwind))
      | `Assoc [ ("Abort", _0) ] ->
          let* _0 = abort_kind_of_json ctx _0 in
          Ok (Abort _0)
      | `String "Return" -> Ok Return
      | `String "UnwindResume" -> Ok UnwindResume
      | _ -> Error "")
end

module Llbc = struct
  open LlbcAst

  let rec ___ = ()

  and block_of_json (ctx : of_json_ctx) (js : json) :
      (Generated_LlbcAst.block, string) result =
    combine_error_msgs js __FUNCTION__
      (match js with
      | `Assoc [ ("span", span); ("id", id); ("statements", statements) ] ->
          let* span = span_of_json ctx span in
          let* block_id = block_id_of_json ctx id in
          let* statements = list_of_json statement_of_json ctx statements in
          Ok ({ span; block_id; statements } : Generated_LlbcAst.block)
      | _ -> Error "")

  and block_id_of_json (ctx : of_json_ctx) (js : json) :
      (Generated_LlbcAst.block_id, string) result =
    combine_error_msgs js __FUNCTION__
      (match js with
      | x -> BlockId.id_of_json ctx x
      | _ -> Error "")

  and statement_of_json (ctx : of_json_ctx) (js : json) :
      (Generated_LlbcAst.statement, string) result =
    combine_error_msgs js __FUNCTION__
      (match js with
      | `Assoc
          [
            ("span", span);
            ("id", id);
            ("kind", kind);
            ("comments_before", comments_before);
          ] ->
          let* span = span_of_json ctx span in
          let* statement_id = statement_id_of_json ctx id in
          let* kind = statement_kind_of_json ctx kind in
          let* comments_before =
            list_of_json string_of_json ctx comments_before
          in
          Ok
            ({ span; statement_id; kind; comments_before }
              : Generated_LlbcAst.statement)
      | _ -> Error "")

  and statement_id_of_json (ctx : of_json_ctx) (js : json) :
      (statement_id, string) result =
    combine_error_msgs js __FUNCTION__
      (match js with
      | x -> StatementId.id_of_json ctx x
      | _ -> Error "")

  and statement_kind_of_json (ctx : of_json_ctx) (js : json) :
      (Generated_LlbcAst.statement_kind, string) result =
    combine_error_msgs js __FUNCTION__
      (match js with
      | `Assoc [ ("Assign", `List [ _0; _1 ]) ] ->
          let* _0 = place_of_json ctx _0 in
          let* _1 = rvalue_of_json ctx _1 in
          Ok (Assign (_0, _1))
      | `Assoc [ ("SetDiscriminant", `List [ _0; _1 ]) ] ->
          let* _0 = place_of_json ctx _0 in
          let* _1 = variant_id_of_json ctx _1 in
          Ok (SetDiscriminant (_0, _1))
      | `Assoc [ ("StorageLive", _0) ] ->
          let* _0 = local_id_of_json ctx _0 in
          Ok (StorageLive _0)
      | `Assoc [ ("StorageDead", _0) ] ->
          let* _0 = local_id_of_json ctx _0 in
          Ok (StorageDead _0)
      | `Assoc [ ("PlaceMention", _0) ] ->
          let* _0 = place_of_json ctx _0 in
          Ok (PlaceMention _0)
      | `Assoc [ ("Borrowck", _0) ] ->
          let* _0 = borrowck_statement_of_json ctx _0 in
          Ok (Borrowck _0)
      | `Assoc
          [
            ( "Drop",
              `Assoc
                [
                  ("place", place);
                  ("fn_ptr", fn_ptr);
                  ("kind", kind);
                  ("on_unwind", on_unwind);
                ] );
          ] ->
          let* place = place_of_json ctx place in
          let* fn_ptr = fn_ptr_of_json ctx fn_ptr in
          let* kind = drop_kind_of_json ctx kind in
          let* on_unwind = block_of_json ctx on_unwind in
          Ok (Drop (place, fn_ptr, kind, on_unwind))
      | `Assoc
          [
            ( "Assert",
              `Assoc
                [
                  ("assert", assert_);
                  ("on_failure", on_failure);
                  ("on_unwind", on_unwind);
                ] );
          ] ->
          let* assert_ = assertion_of_json ctx assert_ in
          let* on_failure = abort_kind_of_json ctx on_failure in
          let* on_unwind = block_of_json ctx on_unwind in
          Ok (Assert (assert_, on_failure, on_unwind))
      | `Assoc
          [
            ( "InlineAsm",
              `Assoc
                [ ("asm", asm); ("targets", targets); ("on_unwind", on_unwind) ]
            );
          ] ->
          let* asm = string_of_json ctx asm in
          let* targets = list_of_json block_of_json ctx targets in
          let* on_unwind = block_of_json ctx on_unwind in
          Ok (InlineAsm (asm, targets, on_unwind))
      | `Assoc [ ("Call", `Assoc [ ("call", call); ("on_unwind", on_unwind) ]) ]
        ->
          let* call = call_of_json ctx call in
          let* on_unwind = block_of_json ctx on_unwind in
          Ok (Call (call, on_unwind))
      | `Assoc [ ("Abort", _0) ] ->
          let* _0 = abort_kind_of_json ctx _0 in
          Ok (Abort _0)
      | `String "Return" -> Ok Return
      | `String "UnwindResume" -> Ok UnwindResume
      | `Assoc [ ("Break", _0) ] ->
          let* _0 = int_of_json ctx _0 in
          Ok (Break _0)
      | `Assoc [ ("Continue", _0) ] ->
          let* _0 = int_of_json ctx _0 in
          Ok (Continue _0)
      | `String "Nop" -> Ok Nop
      | `Assoc [ ("Switch", _0) ] ->
          let* _0 = switch_of_json ctx _0 in
          Ok (Switch _0)
      | `Assoc [ ("Loop", _0) ] ->
          let* _0 = block_of_json ctx _0 in
          Ok (Loop _0)
      | `Assoc [ ("Error", _0) ] ->
          let* _0 = string_of_json ctx _0 in
          Ok (Error _0)
      | _ -> Error "")

  and switch_of_json (ctx : of_json_ctx) (js : json) :
      (Generated_LlbcAst.switch, string) result =
    combine_error_msgs js __FUNCTION__
      (match js with
      | `Assoc [ ("If", `List [ _0; _1; _2 ]) ] ->
          let* _0 = operand_of_json ctx _0 in
          let* _1 = block_of_json ctx _1 in
          let* _2 = block_of_json ctx _2 in
          Ok (If (_0, _1, _2))
      | `Assoc [ ("SwitchInt", `List [ _0; _1; _2; _3 ]) ] ->
          let* _0 = operand_of_json ctx _0 in
          let* _1 = literal_type_of_json ctx _1 in
          let* _2 =
            list_of_json
              (pair_of_json (list_of_json literal_of_json) block_of_json)
              ctx _2
          in
          let* _3 = block_of_json ctx _3 in
          Ok (SwitchInt (_0, _1, _2, _3))
      | `Assoc [ ("Match", `List [ _0; _1; _2 ]) ] ->
          let* _0 = place_of_json ctx _0 in
          let* _1 =
            list_of_json
              (pair_of_json (list_of_json variant_id_of_json) block_of_json)
              ctx _1
          in
          let* _2 = option_of_json block_of_json ctx _2 in
          Ok (Match (_0, _1, _2))
      | _ -> Error "")
end

let rec ___ = ()

and alignment_modifier_of_json (ctx : of_json_ctx) (js : json) :
    (alignment_modifier, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Align", _0) ] ->
        let* _0 = int_of_json ctx _0 in
        Ok (Align _0)
    | `Assoc [ ("Pack", _0) ] ->
        let* _0 = int_of_json ctx _0 in
        Ok (Pack _0)
    | _ -> Error "")

and assoc_item_id_of_json (ctx : of_json_ctx) (js : json) :
    (assoc_item_id, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Type", _0) ] ->
        let* _0 = assoc_type_id_of_json ctx _0 in
        Ok (AssocIdType _0)
    | `Assoc [ ("Method", _0) ] ->
        let* _0 = trait_method_id_of_json ctx _0 in
        Ok (AssocIdMethod _0)
    | `Assoc [ ("Const", _0) ] ->
        let* _0 = assoc_const_id_of_json ctx _0 in
        Ok (AssocIdConst _0)
    | _ -> Error "")

and assoc_item_names_of_json (ctx : of_json_ctx) (js : json) :
    (assoc_item_names, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("types", types); ("methods", methods); ("consts", consts) ] ->
        let* types =
          index_vec_of_json assoc_type_id_of_json trait_item_name_of_json ctx
            types
        in
        let* methods =
          index_vec_of_json trait_method_id_of_json trait_item_name_of_json ctx
            methods
        in
        let* consts =
          index_vec_of_json assoc_const_id_of_json trait_item_name_of_json ctx
            consts
        in
        Ok ({ types; methods; consts } : assoc_item_names)
    | _ -> Error "")

and attr_info_of_json (ctx : of_json_ctx) (js : json) :
    (attr_info, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc
        [
          ("attributes", attributes);
          ("inline", inline);
          ("rename", rename);
          ("public", public);
        ] ->
        let* attributes = list_of_json attribute_of_json ctx attributes in
        let* inline = option_of_json inline_attr_of_json ctx inline in
        let* rename = option_of_json string_of_json ctx rename in
        let* public = bool_of_json ctx public in
        Ok ({ attributes; inline; rename; public } : attr_info)
    | _ -> Error "")

and attribute_of_json (ctx : of_json_ctx) (js : json) :
    (attribute, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `String "Opaque" -> Ok AttrOpaque
    | `String "Exclude" -> Ok AttrExclude
    | `Assoc [ ("Rename", _0) ] ->
        let* _0 = string_of_json ctx _0 in
        Ok (AttrRename _0)
    | `Assoc [ ("VariantsPrefix", _0) ] ->
        let* _0 = string_of_json ctx _0 in
        Ok (AttrVariantsPrefix _0)
    | `Assoc [ ("VariantsSuffix", _0) ] ->
        let* _0 = string_of_json ctx _0 in
        Ok (AttrVariantsSuffix _0)
    | `String "Transparent" -> Ok AttrTransparent
    | `Assoc [ ("IsContract", `Assoc [ ("kind", kind); ("target", target) ]) ]
      ->
        let* kind = string_of_json ctx kind in
        let* target = maybe_assoc_item_id_of_json ctx target in
        Ok (AttrIsContract (kind, target))
    | `Assoc
        [ ("HasContract", `Assoc [ ("kind", kind); ("contract", contract) ]) ]
      ->
        let* kind = string_of_json ctx kind in
        let* contract = fun_decl_id_of_json ctx contract in
        Ok (AttrHasContract (kind, contract))
    | `Assoc [ ("DocComment", _0) ] ->
        let* _0 = string_of_json ctx _0 in
        Ok (AttrDocComment _0)
    | `Assoc [ ("Builtin", _0) ] ->
        let* _0 = rustc_attribute_kind_of_json ctx _0 in
        Ok (AttrBuiltin _0)
    | `Assoc [ ("Unknown", _0) ] ->
        let* _0 = raw_attribute_of_json ctx _0 in
        Ok (AttrUnknown _0)
    | _ -> Error "")

and rustc_attribute_kind_of_json (ctx : of_json_ctx) (js : json) :
    (rustc_attribute_kind, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `String "AutomaticallyDerived" ->
        Ok RustcAttributeKindAutomaticallyDerived
    | `String "Cold" -> Ok RustcAttributeKindCold
    | `Assoc
        [
          ("Deprecated", `Assoc [ ("deprecation", deprecation); ("span", span) ]);
        ] ->
        let* deprecation = rustc_deprecation_of_json ctx deprecation in
        let* span = span_of_json ctx span in
        Ok (RustcAttributeKindDeprecated (deprecation, span))
    | `String "Fundamental" -> Ok RustcAttributeKindFundamental
    | `Assoc [ ("Ignore", `Assoc [ ("span", span); ("reason", reason) ]) ] ->
        let* span = span_of_json ctx span in
        let* reason = option_of_json string_of_json ctx reason in
        Ok (RustcAttributeKindIgnore (span, reason))
    | `Assoc [ ("Inline", `List [ _0; _1 ]) ] ->
        let* _0 = rustc_inline_attr_of_json ctx _0 in
        let* _1 = span_of_json ctx _1 in
        Ok (RustcAttributeKindInline (_0, _1))
    | `Assoc [ ("MayDangle", _0) ] ->
        let* _0 = span_of_json ctx _0 in
        Ok (RustcAttributeKindMayDangle _0)
    | `Assoc [ ("Naked", _0) ] ->
        let* _0 = span_of_json ctx _0 in
        Ok (RustcAttributeKindNaked _0)
    | `String "NoLink" -> Ok RustcAttributeKindNoLink
    | `Assoc [ ("NoMangle", _0) ] ->
        let* _0 = span_of_json ctx _0 in
        Ok (RustcAttributeKindNoMangle _0)
    | `Assoc [ ("NonExhaustive", _0) ] ->
        let* _0 = span_of_json ctx _0 in
        Ok (RustcAttributeKindNonExhaustive _0)
    | `Assoc [ ("Optimize", `List [ _0; _1 ]) ] ->
        let* _0 = rustc_optimize_attr_of_json ctx _0 in
        let* _1 = span_of_json ctx _1 in
        Ok (RustcAttributeKindOptimize (_0, _1))
    | `Assoc [ ("RustcAlign", `Assoc [ ("align", align); ("span", span) ]) ] ->
        let* align = int_of_json ctx align in
        let* span = span_of_json ctx span in
        Ok (RustcAttributeKindRustcAlign (align, span))
    | `String "RustcIntrinsic" -> Ok RustcAttributeKindRustcIntrinsic
    | `String "RustcTestEntrypointMarker" ->
        Ok RustcAttributeKindRustcTestEntrypointMarker
    | `Assoc [ ("ShouldPanic", `Assoc [ ("reason", reason) ]) ] ->
        let* reason = option_of_json string_of_json ctx reason in
        Ok (RustcAttributeKindShouldPanic reason)
    | `Assoc
        [
          ( "TargetFeature",
            `Assoc
              [
                ("features", features);
                ("attr_span", attr_span);
                ("was_forced", was_forced);
              ] );
        ] ->
        let* features =
          list_of_json (pair_of_json string_of_json span_of_json) ctx features
        in
        let* attr_span = span_of_json ctx attr_span in
        let* was_forced = bool_of_json ctx was_forced in
        Ok (RustcAttributeKindTargetFeature (features, attr_span, was_forced))
    | `Assoc [ ("TrackCaller", _0) ] ->
        let* _0 = span_of_json ctx _0 in
        Ok (RustcAttributeKindTrackCaller _0)
    | _ -> Error "")

and body_of_json (ctx : of_json_ctx) (js : json) : (body, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Unstructured", _0) ] ->
        let* _0 =
          gexpr_body_of_json
            (index_vec_of_json Ullbc.block_id_of_json Ullbc.block_of_json)
            ctx _0
        in
        Ok (UnstructuredBody _0)
    | `Assoc [ ("Structured", _0) ] ->
        let* _0 = gexpr_body_of_json Llbc.block_of_json ctx _0 in
        Ok (StructuredBody _0)
    | `Assoc [ ("TargetDispatch", _0) ] ->
        let* _0 =
          index_map_of_json string_of_json fun_decl_ref_of_json int_of_json ctx
            _0
        in
        Ok (TargetDispatchBody _0)
    | `Assoc [ ("Extern", _0) ] ->
        let* _0 = string_of_json ctx _0 in
        Ok (ExternBody _0)
    | `Assoc
        [ ("Intrinsic", `Assoc [ ("name", name); ("arg_names", arg_names) ]) ]
      ->
        let* name = string_of_json ctx name in
        let* arg_names =
          list_of_json (option_of_json string_of_json) ctx arg_names
        in
        Ok (IntrinsicBody (name, arg_names))
    | `String "Opaque" -> Ok OpaqueBody
    | `String "Missing" -> Ok MissingBody
    | `Assoc [ ("Error", _0) ] ->
        let* _0 = error_of_json ctx _0 in
        Ok (ErrorBody _0)
    | _ -> Error "")

and cli_options_of_json (ctx : of_json_ctx) (js : json) :
    (cli_options, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc
        [
          ("ullbc", ullbc);
          ("precise_drops", precise_drops);
          ("mir", mir);
          ("rustc_args", rustc_args);
          ("targets", targets);
          ("sysroot", sysroot);
          ("monomorphize", monomorphize);
          ("monomorphize_mut", monomorphize_mut);
          ("start_from", start_from);
          ("start_from_if_exists", start_from_if_exists);
          ("start_from_attribute", start_from_attribute);
          ("start_from_pub", start_from_pub);
          ("include", include_);
          ("opaque", opaque);
          ("exclude", exclude);
          ("extract_opaque_bodies", extract_opaque_bodies);
          ("translate_all_methods", translate_all_methods);
          ("duplicate_defaulted_methods", duplicate_defaulted_methods);
          ("lift_associated_types", lift_associated_types);
          ("hide_marker_traits", hide_marker_traits);
          ("hide_allocator", hide_allocator);
          ("remove_unused_clauses", remove_unused_clauses);
          ("remove_unused_self_clauses", remove_unused_self_clauses);
          ("remove_adt_clauses", remove_adt_clauses);
          ("desugar_drops", desugar_drops);
          ("ops_to_function_calls", ops_to_function_calls);
          ("index_to_function_calls", index_to_function_calls);
          ("treat_box_as_builtin", treat_box_as_builtin);
          ("raw_consts", raw_consts);
          ("consts", consts);
          ("unsized_strings", unsized_strings);
          ("reconstruct_fallible_operations", reconstruct_fallible_operations);
          ("reconstruct_asserts", reconstruct_asserts);
          ("deallocate_all_locals", deallocate_all_locals);
          ("unbind_item_vars", unbind_item_vars);
          ("print_original_ullbc", print_original_ullbc);
          ("print_ullbc", print_ullbc);
          ("print_built_llbc", print_built_llbc);
          ("print_llbc", print_llbc);
          ("dest_dir", dest_dir);
          ("dest_file", dest_file);
          ("no_dedup_serialized_ast", no_dedup_serialized_ast);
          ("format", format);
          ("no_serialize", no_serialize);
          ("skip_borrowck", skip_borrowck);
          ("no_typecheck", no_typecheck);
          ("no_normalize", no_normalize);
          ("no_reorder_decls", no_reorder_decls);
          ("abort_on_error", abort_on_error);
          ("error_on_warnings", error_on_warnings);
          ("preset", preset);
        ] ->
        let* ullbc = bool_of_json ctx ullbc in
        let* precise_drops = bool_of_json ctx precise_drops in
        let* mir = option_of_json mir_level_of_json ctx mir in
        let* rustc_args = list_of_json string_of_json ctx rustc_args in
        let* targets = list_of_json string_of_json ctx targets in
        let* sysroot = option_of_json string_of_json ctx sysroot in
        let* monomorphize = bool_of_json ctx monomorphize in
        let* monomorphize_mut =
          option_of_json monomorphize_mut_of_json ctx monomorphize_mut
        in
        let* start_from = list_of_json string_of_json ctx start_from in
        let* start_from_if_exists =
          list_of_json string_of_json ctx start_from_if_exists
        in
        let* start_from_attribute =
          list_of_json string_of_json ctx start_from_attribute
        in
        let* start_from_pub = bool_of_json ctx start_from_pub in
        let* included = list_of_json string_of_json ctx include_ in
        let* opaque = list_of_json string_of_json ctx opaque in
        let* exclude = list_of_json string_of_json ctx exclude in
        let* extract_opaque_bodies = bool_of_json ctx extract_opaque_bodies in
        let* translate_all_methods = bool_of_json ctx translate_all_methods in
        let* duplicate_defaulted_methods =
          bool_of_json ctx duplicate_defaulted_methods
        in
        let* lift_associated_types =
          list_of_json string_of_json ctx lift_associated_types
        in
        let* hide_marker_traits = bool_of_json ctx hide_marker_traits in
        let* hide_allocator = bool_of_json ctx hide_allocator in
        let* remove_unused_clauses = bool_of_json ctx remove_unused_clauses in
        let* remove_unused_self_clauses =
          bool_of_json ctx remove_unused_self_clauses
        in
        let* remove_adt_clauses = bool_of_json ctx remove_adt_clauses in
        let* desugar_drops = bool_of_json ctx desugar_drops in
        let* ops_to_function_calls = bool_of_json ctx ops_to_function_calls in
        let* index_to_function_calls =
          bool_of_json ctx index_to_function_calls
        in
        let* treat_box_as_builtin = bool_of_json ctx treat_box_as_builtin in
        let* raw_consts = bool_of_json ctx raw_consts in
        let* consts = option_of_json const_handling_of_json ctx consts in
        let* unsized_strings = bool_of_json ctx unsized_strings in
        let* reconstruct_fallible_operations =
          bool_of_json ctx reconstruct_fallible_operations
        in
        let* reconstruct_asserts = bool_of_json ctx reconstruct_asserts in
        let* deallocate_all_locals = bool_of_json ctx deallocate_all_locals in
        let* unbind_item_vars = bool_of_json ctx unbind_item_vars in
        let* print_original_ullbc = bool_of_json ctx print_original_ullbc in
        let* print_ullbc = bool_of_json ctx print_ullbc in
        let* print_built_llbc = bool_of_json ctx print_built_llbc in
        let* print_llbc = bool_of_json ctx print_llbc in
        let* dest_dir = option_of_json path_buf_of_json ctx dest_dir in
        let* dest_file = option_of_json path_buf_of_json ctx dest_file in
        let* no_dedup_serialized_ast =
          bool_of_json ctx no_dedup_serialized_ast
        in
        let* format =
          option_of_json serialization_format_arg_of_json ctx format
        in
        let* no_serialize = bool_of_json ctx no_serialize in
        let* skip_borrowck = bool_of_json ctx skip_borrowck in
        let* no_typecheck = bool_of_json ctx no_typecheck in
        let* no_normalize = bool_of_json ctx no_normalize in
        let* no_reorder_decls = bool_of_json ctx no_reorder_decls in
        let* abort_on_error = bool_of_json ctx abort_on_error in
        let* error_on_warnings = bool_of_json ctx error_on_warnings in
        let* preset = option_of_json preset_of_json ctx preset in
        Ok
          ({
             ullbc;
             precise_drops;
             mir;
             rustc_args;
             targets;
             sysroot;
             monomorphize;
             monomorphize_mut;
             start_from;
             start_from_if_exists;
             start_from_attribute;
             start_from_pub;
             included;
             opaque;
             exclude;
             extract_opaque_bodies;
             translate_all_methods;
             duplicate_defaulted_methods;
             lift_associated_types;
             hide_marker_traits;
             hide_allocator;
             remove_unused_clauses;
             remove_unused_self_clauses;
             remove_adt_clauses;
             desugar_drops;
             ops_to_function_calls;
             index_to_function_calls;
             treat_box_as_builtin;
             raw_consts;
             consts;
             unsized_strings;
             reconstruct_fallible_operations;
             reconstruct_asserts;
             deallocate_all_locals;
             unbind_item_vars;
             print_original_ullbc;
             print_ullbc;
             print_built_llbc;
             print_llbc;
             dest_dir;
             dest_file;
             no_dedup_serialized_ast;
             format;
             no_serialize;
             skip_borrowck;
             no_typecheck;
             no_normalize;
             no_reorder_decls;
             abort_on_error;
             error_on_warnings;
             preset;
           }
            : cli_options)
    | _ -> Error "")

and closure_info_of_json (ctx : of_json_ctx) (js : json) :
    (closure_info, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc
        [
          ("kind", kind);
          ("fn_once_impl", fn_once_impl);
          ("fn_mut_impl", fn_mut_impl);
          ("fn_impl", fn_impl);
          ("signature", signature);
        ] ->
        let* kind = closure_kind_of_json ctx kind in
        let* fn_once_impl =
          region_binder_of_json trait_impl_ref_of_json ctx fn_once_impl
        in
        let* fn_mut_impl =
          option_of_json
            (region_binder_of_json trait_impl_ref_of_json)
            ctx fn_mut_impl
        in
        let* fn_impl =
          option_of_json
            (region_binder_of_json trait_impl_ref_of_json)
            ctx fn_impl
        in
        let* signature = region_binder_of_json fun_sig_of_json ctx signature in
        Ok
          ({ kind; fn_once_impl; fn_mut_impl; fn_impl; signature }
            : closure_info)
    | _ -> Error "")

and closure_kind_of_json (ctx : of_json_ctx) (js : json) :
    (closure_kind, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `String "Fn" -> Ok Fn
    | `String "FnMut" -> Ok FnMut
    | `String "FnOnce" -> Ok FnOnce
    | _ -> Error "")

and const_handling_of_json (ctx : of_json_ctx) (js : json) :
    (const_handling, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `String "Initializers" -> Ok Initializers
    | `String "Values" -> Ok Values
    | _ -> Error "")

and declaration_group_of_json (ctx : of_json_ctx) (js : json) :
    (declaration_group, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Type", _0) ] ->
        let* _0 = g_declaration_group_of_json type_decl_id_of_json ctx _0 in
        Ok (TypeGroup _0)
    | `Assoc [ ("Fun", _0) ] ->
        let* _0 = g_declaration_group_of_json fun_decl_id_of_json ctx _0 in
        Ok (FunGroup _0)
    | `Assoc [ ("Global", _0) ] ->
        let* _0 = g_declaration_group_of_json global_decl_id_of_json ctx _0 in
        Ok (GlobalGroup _0)
    | `Assoc [ ("TraitDecl", _0) ] ->
        let* _0 = g_declaration_group_of_json trait_decl_id_of_json ctx _0 in
        Ok (TraitDeclGroup _0)
    | `Assoc [ ("TraitImpl", _0) ] ->
        let* _0 = g_declaration_group_of_json trait_impl_id_of_json ctx _0 in
        Ok (TraitImplGroup _0)
    | `Assoc [ ("Mixed", _0) ] ->
        let* _0 = g_declaration_group_of_json item_id_of_json ctx _0 in
        Ok (MixedGroup _0)
    | _ -> Error "")

and rustc_deprecated_since_of_json (ctx : of_json_ctx) (js : json) :
    (rustc_deprecated_since, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("RustcVersion", _0) ] ->
        let* _0 = rustc_rustc_version_of_json ctx _0 in
        Ok (RustcDeprecatedSinceRustcVersion _0)
    | `String "Future" -> Ok RustcDeprecatedSinceFuture
    | `Assoc [ ("NonStandard", _0) ] ->
        let* _0 = string_of_json ctx _0 in
        Ok (RustcDeprecatedSinceNonStandard _0)
    | `String "Unspecified" -> Ok RustcDeprecatedSinceUnspecified
    | `String "Err" -> Ok RustcDeprecatedSinceErr
    | _ -> Error "")

and rustc_deprecation_of_json (ctx : of_json_ctx) (js : json) :
    (rustc_deprecation, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("since", since); ("note", note); ("suggestion", suggestion) ] ->
        let* since = rustc_deprecated_since_of_json ctx since in
        let* note = option_of_json rustc_ident_of_json ctx note in
        let* suggestion = option_of_json string_of_json ctx suggestion in
        Ok ({ since; note; suggestion } : rustc_deprecation)
    | _ -> Error "")

and discriminator_of_json (ctx : of_json_ctx) (js : json) :
    (discriminator, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Known", _0) ] ->
        let* _0 = variant_id_of_json ctx _0 in
        Ok (Known _0)
    | `String "Invalid" -> Ok Invalid
    | `Assoc
        [
          ( "Branch",
            `Assoc
              [
                ("offset", offset);
                ("int_ty", int_ty);
                ("children", children);
                ("fallback", fallback);
              ] );
        ] ->
        let* offset = int_of_json ctx offset in
        let* int_ty = integer_type_of_json ctx int_ty in
        let* children =
          list_of_json
            (pair_of_json
               (range_inclusive_of_json scalar_value_of_json)
               discriminator_of_json)
            ctx children
        in
        let* fallback = box_of_json discriminator_of_json ctx fallback in
        Ok (Branch (offset, int_ty, children, fallback))
    | _ -> Error "")

and error_of_json (ctx : of_json_ctx) (js : json) : (error, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("span", span); ("msg", msg) ] ->
        let* span = span_of_json ctx span in
        let* msg = string_of_json ctx msg in
        Ok ({ span; msg } : error)
    | _ -> Error "")

and field_of_json (ctx : of_json_ctx) (js : json) : (field, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc
        [
          ("span", span);
          ("attr_info", attr_info);
          ("name", name);
          ("is_positional", is_positional);
          ("ty", ty);
        ] ->
        let* span = span_of_json ctx span in
        let* attr_info = attr_info_of_json ctx attr_info in
        let* field_name = string_of_json ctx name in
        let* is_positional = bool_of_json ctx is_positional in
        let* field_ty = ty_of_json ctx ty in
        Ok ({ span; attr_info; field_name; is_positional; field_ty } : field)
    | _ -> Error "")

and file_of_json (ctx : of_json_ctx) (js : json) : (file, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | json -> (
        match json with
        | `Assoc
            [
              ("id", id);
              ("name", name);
              ("crate_name", crate_name);
              ("contents", contents);
            ] ->
            let* id = FileId.id_of_json ctx id in
            let* name = file_name_of_json ctx name in
            let* crate_name = string_of_json ctx crate_name in
            let* contents = option_of_json string_of_json ctx contents in
            let file : file = { name; crate_name; contents } in
            FileTbl.add ctx.id_to_file_map id file;
            Ok file
        | _ -> Error "")
    | _ -> Error "")

and file_name_of_json (ctx : of_json_ctx) (js : json) :
    (file_name, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Virtual", _0) ] ->
        let* _0 = path_buf_of_json ctx _0 in
        Ok (Virtual _0)
    | `Assoc [ ("Local", _0) ] ->
        let* _0 = path_buf_of_json ctx _0 in
        Ok (Local _0)
    | `Assoc [ ("NotReal", _0) ] ->
        let* _0 = string_of_json ctx _0 in
        Ok (NotReal _0)
    | _ -> Error "")

and fun_decl_of_json (ctx : of_json_ctx) (js : json) : (fun_decl, string) result
    =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc
        [
          ("def_id", def_id);
          ("item_meta", item_meta);
          ("generics", generics);
          ("signature", signature);
          ("src", src);
          ("body", body);
        ] ->
        let* def_id = fun_decl_id_of_json ctx def_id in
        let* item_meta = item_meta_of_json ctx item_meta in
        let* generics = generic_params_of_json ctx generics in
        let* signature = box_of_json fun_sig_of_json ctx signature in
        let* src = fun_source_of_json ctx src in
        let* body = body_of_json ctx body in
        Ok ({ def_id; item_meta; generics; signature; src; body } : fun_decl)
    | _ -> Error "")

and fun_source_of_json (ctx : of_json_ctx) (js : json) :
    (fun_source, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `String "Normal" -> Ok NormalFun
    | `Assoc
        [
          ( "TraitDefault",
            `Assoc [ ("trait_ref", trait_ref); ("item_id", item_id) ] );
        ] ->
        let* trait_ref = trait_decl_ref_of_json ctx trait_ref in
        let* item_id = trait_method_id_of_json ctx item_id in
        Ok (TraitDefaultFun (trait_ref, item_id))
    | `Assoc
        [
          ( "TraitImpl",
            `Assoc
              [
                ("impl_ref", impl_ref);
                ("trait_ref", trait_ref);
                ("item_id", item_id);
                ("reuses_default", reuses_default);
              ] );
        ] ->
        let* impl_ref = trait_impl_ref_of_json ctx impl_ref in
        let* trait_ref = trait_decl_ref_of_json ctx trait_ref in
        let* item_id = trait_method_id_of_json ctx item_id in
        let* reuses_default = bool_of_json ctx reuses_default in
        Ok (TraitImplFun (impl_ref, trait_ref, item_id, reuses_default))
    | `String "VTableShim" -> Ok VTableShimFun
    | `Assoc [ ("GlobalInitializer", _0) ] ->
        let* _0 = global_decl_ref_of_json ctx _0 in
        Ok (GlobalInitializerFun _0)
    | `Assoc [ ("TargetDependent", `Assoc [ ("dispatcher", dispatcher) ]) ] ->
        let* dispatcher = fun_decl_ref_of_json ctx dispatcher in
        Ok (TargetDependentFun dispatcher)
    | _ -> Error "")

and g_declaration_group_of_json :
    'a0.
    (of_json_ctx -> json -> ('a0, string) result) ->
    of_json_ctx ->
    json ->
    ('a0 g_declaration_group, string) result =
 fun arg0_of_json ctx js ->
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("NonRec", _0) ] ->
        let* _0 = arg0_of_json ctx _0 in
        Ok (NonRecGroup _0)
    | `Assoc [ ("Rec", _0) ] ->
        let* _0 = list_of_json arg0_of_json ctx _0 in
        Ok (RecGroup _0)
    | _ -> Error "")

and gexpr_body_of_json :
    'a0.
    (of_json_ctx -> json -> ('a0, string) result) ->
    of_json_ctx ->
    json ->
    ('a0 gexpr_body, string) result =
 fun arg0_of_json ctx js ->
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc
        [
          ("span", span);
          ("bound_body_regions", bound_body_regions);
          ("locals", locals);
          ("body", body);
          ("comments", _);
        ] ->
        let* span = span_of_json ctx span in
        let* bound_body_regions = int_of_json ctx bound_body_regions in
        let* locals = locals_of_json ctx locals in
        let* body = arg0_of_json ctx body in
        Ok ({ span; bound_body_regions; locals; body } : _ gexpr_body)
    | _ -> Error "")

and global_decl_of_json (ctx : of_json_ctx) (js : json) :
    (global_decl, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc
        [
          ("def_id", def_id);
          ("item_meta", item_meta);
          ("generics", generics);
          ("ty", ty);
          ("src", src);
          ("global_kind", global_kind);
          ("value", value);
        ] ->
        let* def_id = global_decl_id_of_json ctx def_id in
        let* item_meta = item_meta_of_json ctx item_meta in
        let* generics = generic_params_of_json ctx generics in
        let* ty = ty_of_json ctx ty in
        let* src = global_source_of_json ctx src in
        let* global_kind = global_kind_of_json ctx global_kind in
        let* value = constant_expr_of_json ctx value in
        Ok
          ({ def_id; item_meta; generics; ty; src; global_kind; value }
            : global_decl)
    | _ -> Error "")

and global_kind_of_json (ctx : of_json_ctx) (js : json) :
    (global_kind, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `String "Static" -> Ok Static
    | `String "ThreadLocal" -> Ok ThreadLocal
    | `String "NamedConst" -> Ok NamedConst
    | `String "AnonConst" -> Ok AnonConst
    | _ -> Error "")

and global_source_of_json (ctx : of_json_ctx) (js : json) :
    (global_source, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `String "Normal" -> Ok NormalGlobal
    | `Assoc
        [
          ( "TraitDefault",
            `Assoc [ ("trait_ref", trait_ref); ("item_id", item_id) ] );
        ] ->
        let* trait_ref = trait_decl_ref_of_json ctx trait_ref in
        let* item_id = assoc_const_id_of_json ctx item_id in
        Ok (TraitDefaultGlobal (trait_ref, item_id))
    | `Assoc
        [
          ( "TraitImpl",
            `Assoc
              [
                ("impl_ref", impl_ref);
                ("trait_ref", trait_ref);
                ("item_id", item_id);
                ("reuses_default", reuses_default);
              ] );
        ] ->
        let* impl_ref = trait_impl_ref_of_json ctx impl_ref in
        let* trait_ref = trait_decl_ref_of_json ctx trait_ref in
        let* item_id = assoc_const_id_of_json ctx item_id in
        let* reuses_default = bool_of_json ctx reuses_default in
        Ok (TraitImplGlobal (impl_ref, trait_ref, item_id, reuses_default))
    | `Assoc [ ("VTableInstance", `Assoc [ ("impl_ref", impl_ref) ]) ] ->
        let* impl_ref = option_of_json trait_impl_ref_of_json ctx impl_ref in
        Ok (VTableInstanceGlobal impl_ref)
    | _ -> Error "")

and rustc_ident_of_json (ctx : of_json_ctx) (js : json) :
    (rustc_ident, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("name", name); ("span", span) ] ->
        let* name = string_of_json ctx name in
        let* span = span_of_json ctx span in
        Ok ({ name; span } : rustc_ident)
    | _ -> Error "")

and index_map_of_json :
    'a0 'a1 'a2.
    (of_json_ctx -> json -> ('a0, string) result) ->
    (of_json_ctx -> json -> ('a1, string) result) ->
    (of_json_ctx -> json -> ('a2, string) result) ->
    of_json_ctx ->
    json ->
    (('a0 * 'a1) list, string) result =
 fun arg0_of_json arg1_of_json arg2_of_json ctx js ->
  combine_error_msgs js __FUNCTION__
    (match js with
    | json ->
        list_of_json (key_value_pair_of_json arg0_of_json arg1_of_json) ctx json
    | _ -> Error "")

and inline_attr_of_json (ctx : of_json_ctx) (js : json) :
    (inline_attr, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `String "Hint" -> Ok Hint
    | `String "Never" -> Ok Never
    | `String "Always" -> Ok Always
    | _ -> Error "")

and rustc_inline_attr_of_json (ctx : of_json_ctx) (js : json) :
    (rustc_inline_attr, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `String "None" -> Ok RustcInlineAttrNone
    | `String "Hint" -> Ok RustcInlineAttrHint
    | `String "Always" -> Ok RustcInlineAttrAlways
    | `String "Never" -> Ok RustcInlineAttrNever
    | `Assoc
        [ ("Force", `Assoc [ ("attr_span", attr_span); ("reason", reason) ]) ]
      ->
        let* attr_span = span_of_json ctx attr_span in
        let* reason = option_of_json string_of_json ctx reason in
        Ok (RustcInlineAttrForce (attr_span, reason))
    | _ -> Error "")

and integer_type_of_json (ctx : of_json_ctx) (js : json) :
    (integer_type, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Signed", _0) ] ->
        let* _0 = int_ty_of_json ctx _0 in
        Ok (Signed _0)
    | `Assoc [ ("Unsigned", _0) ] ->
        let* _0 = u_int_ty_of_json ctx _0 in
        Ok (Unsigned _0)
    | _ -> Error "")

and item_id_of_json (ctx : of_json_ctx) (js : json) : (item_id, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Type", _0) ] ->
        let* _0 = type_decl_id_of_json ctx _0 in
        Ok (IdType _0)
    | `Assoc [ ("TraitDecl", _0) ] ->
        let* _0 = trait_decl_id_of_json ctx _0 in
        Ok (IdTraitDecl _0)
    | `Assoc [ ("TraitImpl", _0) ] ->
        let* _0 = trait_impl_id_of_json ctx _0 in
        Ok (IdTraitImpl _0)
    | `Assoc [ ("Fun", _0) ] ->
        let* _0 = fun_decl_id_of_json ctx _0 in
        Ok (IdFun _0)
    | `Assoc [ ("Global", _0) ] ->
        let* _0 = global_decl_id_of_json ctx _0 in
        Ok (IdGlobal _0)
    | _ -> Error "")

and item_meta_of_json (ctx : of_json_ctx) (js : json) :
    (item_meta, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc
        [
          ("name", name);
          ("span", span);
          ("source_text", source_text);
          ("attr_info", attr_info);
          ("is_local", is_local);
          ("opacity", opacity);
          ("lang_item", lang_item);
          ("diagnostic_item", diagnostic_item);
        ] ->
        let* name = name_of_json ctx name in
        let* span = span_of_json ctx span in
        let* source_text = option_of_json string_of_json ctx source_text in
        let* attr_info = attr_info_of_json ctx attr_info in
        let* is_local = bool_of_json ctx is_local in
        let* opacity = item_opacity_of_json ctx opacity in
        let* lang_item = option_of_json rustc_lang_item_of_json ctx lang_item in
        let* diagnostic_item =
          option_of_json string_of_json ctx diagnostic_item
        in
        Ok
          ({
             name;
             span;
             source_text;
             attr_info;
             is_local;
             opacity;
             lang_item;
             diagnostic_item;
           }
            : item_meta)
    | _ -> Error "")

and item_opacity_of_json (ctx : of_json_ctx) (js : json) :
    (item_opacity, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `String "Transparent" -> Ok Transparent
    | `String "Foreign" -> Ok Foreign
    | `String "Opaque" -> Ok ItemOpaque
    | `String "Invisible" -> Ok Invisible
    | _ -> Error "")

and rustc_lang_item_of_json (ctx : of_json_ctx) (js : json) :
    (rustc_lang_item, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `String "Sized" -> Ok RustcLangItemSized
    | `String "MetaSized" -> Ok RustcLangItemMetaSized
    | `String "PointeeSized" -> Ok RustcLangItemPointeeSized
    | `String "Unsize" -> Ok RustcLangItemUnsize
    | `String "AlignOf" -> Ok RustcLangItemAlignOf
    | `String "SizeOf" -> Ok RustcLangItemSizeOf
    | `String "OffsetOf" -> Ok RustcLangItemOffsetOf
    | `String "StructuralPeq" -> Ok RustcLangItemStructuralPeq
    | `String "Copy" -> Ok RustcLangItemCopy
    | `String "Clone" -> Ok RustcLangItemClone
    | `String "CloneFn" -> Ok RustcLangItemCloneFn
    | `String "UseCloned" -> Ok RustcLangItemUseCloned
    | `String "TrivialClone" -> Ok RustcLangItemTrivialClone
    | `String "Sync" -> Ok RustcLangItemSync
    | `String "DiscriminantKind" -> Ok RustcLangItemDiscriminantKind
    | `String "Discriminant" -> Ok RustcLangItemDiscriminant
    | `String "PointeeTrait" -> Ok RustcLangItemPointeeTrait
    | `String "Metadata" -> Ok RustcLangItemMetadata
    | `String "DynMetadata" -> Ok RustcLangItemDynMetadata
    | `String "Freeze" -> Ok RustcLangItemFreeze
    | `String "UnsafeUnpin" -> Ok RustcLangItemUnsafeUnpin
    | `String "FnPtrTrait" -> Ok RustcLangItemFnPtrTrait
    | `String "FnPtrAddr" -> Ok RustcLangItemFnPtrAddr
    | `String "Drop" -> Ok RustcLangItemDrop
    | `String "Destruct" -> Ok RustcLangItemDestruct
    | `String "AsyncDrop" -> Ok RustcLangItemAsyncDrop
    | `String "AsyncDropInPlace" -> Ok RustcLangItemAsyncDropInPlace
    | `String "CoerceUnsized" -> Ok RustcLangItemCoerceUnsized
    | `String "DispatchFromDyn" -> Ok RustcLangItemDispatchFromDyn
    | `String "TryAsDyn" -> Ok RustcLangItemTryAsDyn
    | `String "TransmuteOpts" -> Ok RustcLangItemTransmuteOpts
    | `String "TransmuteTrait" -> Ok RustcLangItemTransmuteTrait
    | `String "Add" -> Ok RustcLangItemAdd
    | `String "Sub" -> Ok RustcLangItemSub
    | `String "Mul" -> Ok RustcLangItemMul
    | `String "Div" -> Ok RustcLangItemDiv
    | `String "Rem" -> Ok RustcLangItemRem
    | `String "Neg" -> Ok RustcLangItemNeg
    | `String "Not" -> Ok RustcLangItemNot
    | `String "BitXor" -> Ok RustcLangItemBitXor
    | `String "BitAnd" -> Ok RustcLangItemBitAnd
    | `String "BitOr" -> Ok RustcLangItemBitOr
    | `String "Shl" -> Ok RustcLangItemShl
    | `String "Shr" -> Ok RustcLangItemShr
    | `String "AddAssign" -> Ok RustcLangItemAddAssign
    | `String "SubAssign" -> Ok RustcLangItemSubAssign
    | `String "MulAssign" -> Ok RustcLangItemMulAssign
    | `String "DivAssign" -> Ok RustcLangItemDivAssign
    | `String "RemAssign" -> Ok RustcLangItemRemAssign
    | `String "BitXorAssign" -> Ok RustcLangItemBitXorAssign
    | `String "BitAndAssign" -> Ok RustcLangItemBitAndAssign
    | `String "BitOrAssign" -> Ok RustcLangItemBitOrAssign
    | `String "ShlAssign" -> Ok RustcLangItemShlAssign
    | `String "ShrAssign" -> Ok RustcLangItemShrAssign
    | `String "Index" -> Ok RustcLangItemIndex
    | `String "IndexMut" -> Ok RustcLangItemIndexMut
    | `String "UnsafeCell" -> Ok RustcLangItemUnsafeCell
    | `String "CovariantUnsafeCell" -> Ok RustcLangItemCovariantUnsafeCell
    | `String "UnsafePinned" -> Ok RustcLangItemUnsafePinned
    | `String "VaArgSafe" -> Ok RustcLangItemVaArgSafe
    | `String "VaList" -> Ok RustcLangItemVaList
    | `String "Complex" -> Ok RustcLangItemComplex
    | `String "Deref" -> Ok RustcLangItemDeref
    | `String "DerefMut" -> Ok RustcLangItemDerefMut
    | `String "DerefPure" -> Ok RustcLangItemDerefPure
    | `String "DerefTarget" -> Ok RustcLangItemDerefTarget
    | `String "Receiver" -> Ok RustcLangItemReceiver
    | `String "ReceiverTarget" -> Ok RustcLangItemReceiverTarget
    | `String "LegacyReceiver" -> Ok RustcLangItemLegacyReceiver
    | `String "Fn" -> Ok RustcLangItemFn
    | `String "FnMut" -> Ok RustcLangItemFnMut
    | `String "FnOnce" -> Ok RustcLangItemFnOnce
    | `String "AsyncFn" -> Ok RustcLangItemAsyncFn
    | `String "AsyncFnMut" -> Ok RustcLangItemAsyncFnMut
    | `String "AsyncFnOnce" -> Ok RustcLangItemAsyncFnOnce
    | `String "AsyncFnOnceOutput" -> Ok RustcLangItemAsyncFnOnceOutput
    | `String "CallOnceFuture" -> Ok RustcLangItemCallOnceFuture
    | `String "CallRefFuture" -> Ok RustcLangItemCallRefFuture
    | `String "AsyncFnKindHelper" -> Ok RustcLangItemAsyncFnKindHelper
    | `String "AsyncFnKindUpvars" -> Ok RustcLangItemAsyncFnKindUpvars
    | `String "FnOnceOutput" -> Ok RustcLangItemFnOnceOutput
    | `String "Iterator" -> Ok RustcLangItemIterator
    | `String "FusedIterator" -> Ok RustcLangItemFusedIterator
    | `String "Future" -> Ok RustcLangItemFuture
    | `String "FutureOutput" -> Ok RustcLangItemFutureOutput
    | `String "AsyncIterator" -> Ok RustcLangItemAsyncIterator
    | `String "CoroutineState" -> Ok RustcLangItemCoroutineState
    | `String "Coroutine" -> Ok RustcLangItemCoroutine
    | `String "CoroutineReturn" -> Ok RustcLangItemCoroutineReturn
    | `String "CoroutineYield" -> Ok RustcLangItemCoroutineYield
    | `String "CoroutineResume" -> Ok RustcLangItemCoroutineResume
    | `String "Unpin" -> Ok RustcLangItemUnpin
    | `String "Pin" -> Ok RustcLangItemPin
    | `String "OrderingEnum" -> Ok RustcLangItemOrderingEnum
    | `String "PartialEq" -> Ok RustcLangItemPartialEq
    | `String "PartialOrd" -> Ok RustcLangItemPartialOrd
    | `String "CVoid" -> Ok RustcLangItemCVoid
    | `String "Type" -> Ok RustcLangItemType
    | `String "TypeGeneric" -> Ok RustcLangItemTypeGeneric
    | `String "TypeId" -> Ok RustcLangItemTypeId
    | `String "Panic" -> Ok RustcLangItemPanic
    | `String "PanicNounwind" -> Ok RustcLangItemPanicNounwind
    | `String "PanicFmt" -> Ok RustcLangItemPanicFmt
    | `String "PanicDisplay" -> Ok RustcLangItemPanicDisplay
    | `String "ConstPanicFmt" -> Ok RustcLangItemConstPanicFmt
    | `String "PanicBoundsCheck" -> Ok RustcLangItemPanicBoundsCheck
    | `String "PanicMisalignedPointerDereference" ->
        Ok RustcLangItemPanicMisalignedPointerDereference
    | `String "PanicInfo" -> Ok RustcLangItemPanicInfo
    | `String "PanicLocation" -> Ok RustcLangItemPanicLocation
    | `String "PanicImpl" -> Ok RustcLangItemPanicImpl
    | `String "PanicCannotUnwind" -> Ok RustcLangItemPanicCannotUnwind
    | `String "PanicInCleanup" -> Ok RustcLangItemPanicInCleanup
    | `String "PanicAddOverflow" -> Ok RustcLangItemPanicAddOverflow
    | `String "PanicSubOverflow" -> Ok RustcLangItemPanicSubOverflow
    | `String "PanicMulOverflow" -> Ok RustcLangItemPanicMulOverflow
    | `String "PanicDivOverflow" -> Ok RustcLangItemPanicDivOverflow
    | `String "PanicRemOverflow" -> Ok RustcLangItemPanicRemOverflow
    | `String "PanicNegOverflow" -> Ok RustcLangItemPanicNegOverflow
    | `String "PanicShrOverflow" -> Ok RustcLangItemPanicShrOverflow
    | `String "PanicShlOverflow" -> Ok RustcLangItemPanicShlOverflow
    | `String "PanicDivZero" -> Ok RustcLangItemPanicDivZero
    | `String "PanicRemZero" -> Ok RustcLangItemPanicRemZero
    | `String "PanicCoroutineResumed" -> Ok RustcLangItemPanicCoroutineResumed
    | `String "PanicAsyncFnResumed" -> Ok RustcLangItemPanicAsyncFnResumed
    | `String "PanicAsyncGenFnResumed" -> Ok RustcLangItemPanicAsyncGenFnResumed
    | `String "PanicGenFnNone" -> Ok RustcLangItemPanicGenFnNone
    | `String "PanicCoroutineResumedPanic" ->
        Ok RustcLangItemPanicCoroutineResumedPanic
    | `String "PanicAsyncFnResumedPanic" ->
        Ok RustcLangItemPanicAsyncFnResumedPanic
    | `String "PanicAsyncGenFnResumedPanic" ->
        Ok RustcLangItemPanicAsyncGenFnResumedPanic
    | `String "PanicGenFnNonePanic" -> Ok RustcLangItemPanicGenFnNonePanic
    | `String "PanicNullPointerDereference" ->
        Ok RustcLangItemPanicNullPointerDereference
    | `String "PanicNullReferenceConstructed" ->
        Ok RustcLangItemPanicNullReferenceConstructed
    | `String "PanicInvalidEnumConstruction" ->
        Ok RustcLangItemPanicInvalidEnumConstruction
    | `String "PanicCoroutineResumedDrop" ->
        Ok RustcLangItemPanicCoroutineResumedDrop
    | `String "PanicAsyncFnResumedDrop" ->
        Ok RustcLangItemPanicAsyncFnResumedDrop
    | `String "PanicAsyncGenFnResumedDrop" ->
        Ok RustcLangItemPanicAsyncGenFnResumedDrop
    | `String "PanicGenFnNoneDrop" -> Ok RustcLangItemPanicGenFnNoneDrop
    | `String "BeginPanic" -> Ok RustcLangItemBeginPanic
    | `String "FormatArgument" -> Ok RustcLangItemFormatArgument
    | `String "FormatArguments" -> Ok RustcLangItemFormatArguments
    | `String "DropGlue" -> Ok RustcLangItemDropGlue
    | `String "AllocLayout" -> Ok RustcLangItemAllocLayout
    | `String "Start" -> Ok RustcLangItemStart
    | `String "EhPersonality" -> Ok RustcLangItemEhPersonality
    | `String "CompilerMove" -> Ok RustcLangItemCompilerMove
    | `String "CompilerCopy" -> Ok RustcLangItemCompilerCopy
    | `String "OwnedBox" -> Ok RustcLangItemOwnedBox
    | `String "GlobalAlloc" -> Ok RustcLangItemGlobalAlloc
    | `String "PhantomData" -> Ok RustcLangItemPhantomData
    | `String "ManuallyDrop" -> Ok RustcLangItemManuallyDrop
    | `String "MaybeDangling" -> Ok RustcLangItemMaybeDangling
    | `String "BikeshedGuaranteedNoDrop" ->
        Ok RustcLangItemBikeshedGuaranteedNoDrop
    | `String "MaybeUninit" -> Ok RustcLangItemMaybeUninit
    | `String "Termination" -> Ok RustcLangItemTermination
    | `String "Try" -> Ok RustcLangItemTry
    | `String "Tuple" -> Ok RustcLangItemTuple
    | `String "SliceLen" -> Ok RustcLangItemSliceLen
    | `String "TryTraitFromResidual" -> Ok RustcLangItemTryTraitFromResidual
    | `String "TryTraitFromOutput" -> Ok RustcLangItemTryTraitFromOutput
    | `String "TryTraitBranch" -> Ok RustcLangItemTryTraitBranch
    | `String "TryTraitFromYeet" -> Ok RustcLangItemTryTraitFromYeet
    | `String "ResidualIntoTryType" -> Ok RustcLangItemResidualIntoTryType
    | `String "CoercePointeeValidated" -> Ok RustcLangItemCoercePointeeValidated
    | `String "ConstParamTy" -> Ok RustcLangItemConstParamTy
    | `String "Poll" -> Ok RustcLangItemPoll
    | `String "PollReady" -> Ok RustcLangItemPollReady
    | `String "PollPending" -> Ok RustcLangItemPollPending
    | `String "AsyncGenReady" -> Ok RustcLangItemAsyncGenReady
    | `String "AsyncGenPending" -> Ok RustcLangItemAsyncGenPending
    | `String "AsyncGenFinished" -> Ok RustcLangItemAsyncGenFinished
    | `String "ResumeTy" -> Ok RustcLangItemResumeTy
    | `String "GetContext" -> Ok RustcLangItemGetContext
    | `String "Context" -> Ok RustcLangItemContext
    | `String "FuturePoll" -> Ok RustcLangItemFuturePoll
    | `String "AsyncIteratorPollNext" -> Ok RustcLangItemAsyncIteratorPollNext
    | `String "IntoAsyncIterIntoIter" -> Ok RustcLangItemIntoAsyncIterIntoIter
    | `String "Option" -> Ok RustcLangItemOption
    | `String "OptionSome" -> Ok RustcLangItemOptionSome
    | `String "OptionNone" -> Ok RustcLangItemOptionNone
    | `String "ResultOk" -> Ok RustcLangItemResultOk
    | `String "ResultErr" -> Ok RustcLangItemResultErr
    | `String "ControlFlowContinue" -> Ok RustcLangItemControlFlowContinue
    | `String "ControlFlowBreak" -> Ok RustcLangItemControlFlowBreak
    | `String "IntoFutureIntoFuture" -> Ok RustcLangItemIntoFutureIntoFuture
    | `String "IntoIterIntoIter" -> Ok RustcLangItemIntoIterIntoIter
    | `String "IteratorNext" -> Ok RustcLangItemIteratorNext
    | `String "PinNewUnchecked" -> Ok RustcLangItemPinNewUnchecked
    | `String "RangeFrom" -> Ok RustcLangItemRangeFrom
    | `String "RangeFull" -> Ok RustcLangItemRangeFull
    | `String "RangeInclusiveStruct" -> Ok RustcLangItemRangeInclusiveStruct
    | `String "RangeInclusiveNew" -> Ok RustcLangItemRangeInclusiveNew
    | `String "Range" -> Ok RustcLangItemRange
    | `String "RangeToInclusive" -> Ok RustcLangItemRangeToInclusive
    | `String "RangeTo" -> Ok RustcLangItemRangeTo
    | `String "RangeMax" -> Ok RustcLangItemRangeMax
    | `String "RangeMin" -> Ok RustcLangItemRangeMin
    | `String "RangeSub" -> Ok RustcLangItemRangeSub
    | `String "RangeFromCopy" -> Ok RustcLangItemRangeFromCopy
    | `String "RangeCopy" -> Ok RustcLangItemRangeCopy
    | `String "RangeInclusiveCopy" -> Ok RustcLangItemRangeInclusiveCopy
    | `String "RangeToInclusiveCopy" -> Ok RustcLangItemRangeToInclusiveCopy
    | `String "String" -> Ok RustcLangItemString
    | `String "CStr" -> Ok RustcLangItemCStr
    | `String "ContractBuildCheckEnsures" ->
        Ok RustcLangItemContractBuildCheckEnsures
    | `String "ContractCheckRequires" -> Ok RustcLangItemContractCheckRequires
    | `String "DefaultTrait4" -> Ok RustcLangItemDefaultTrait4
    | `String "DefaultTrait3" -> Ok RustcLangItemDefaultTrait3
    | `String "DefaultTrait2" -> Ok RustcLangItemDefaultTrait2
    | `String "DefaultTrait1" -> Ok RustcLangItemDefaultTrait1
    | `String "ContractCheckEnsures" -> Ok RustcLangItemContractCheckEnsures
    | `String "Reborrow" -> Ok RustcLangItemReborrow
    | `String "CoerceShared" -> Ok RustcLangItemCoerceShared
    | `String "FieldRepresentingType" -> Ok RustcLangItemFieldRepresentingType
    | `String "Field" -> Ok RustcLangItemField
    | `String "FieldBase" -> Ok RustcLangItemFieldBase
    | `String "FieldType" -> Ok RustcLangItemFieldType
    | `String "FieldOffset" -> Ok RustcLangItemFieldOffset
    | `String "From" -> Ok RustcLangItemFrom
    | `String "FromFn" -> Ok RustcLangItemFromFn
    | _ -> Error "")

and layout_of_json (ctx : of_json_ctx) (js : json) : (layout, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc
        [
          ("size", size);
          ("align", align);
          ("discriminator", discriminator);
          ("uninhabited", uninhabited);
          ("variant_layouts", variant_layouts);
          ("repr", repr);
        ] ->
        let* size = option_of_json int_of_json ctx size in
        let* align = option_of_json int_of_json ctx align in
        let* discriminator =
          option_of_json discriminator_of_json ctx discriminator
        in
        let* uninhabited = bool_of_json ctx uninhabited in
        let* variant_layouts =
          index_vec_of_json variant_id_of_json
            (option_of_json variant_layout_of_json)
            ctx variant_layouts
        in
        let* repr = repr_options_of_json ctx repr in
        Ok
          ({ size; align; discriminator; uninhabited; variant_layouts; repr }
            : layout)
    | _ -> Error "")

and local_of_json (ctx : of_json_ctx) (js : json) : (local, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("index", index); ("name", name); ("span", span); ("ty", ty) ] ->
        let* index = local_id_of_json ctx index in
        let* name = option_of_json string_of_json ctx name in
        let* span = span_of_json ctx span in
        let* local_ty = ty_of_json ctx ty in
        Ok ({ index; name; span; local_ty } : local)
    | _ -> Error "")

and locals_of_json (ctx : of_json_ctx) (js : json) : (locals, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("arg_count", arg_count); ("locals", locals) ] ->
        let* arg_count = int_of_json ctx arg_count in
        let* locals =
          index_vec_of_json local_id_of_json local_of_json ctx locals
        in
        Ok ({ arg_count; locals } : locals)
    | _ -> Error "")

and maybe_assoc_item_id_of_json (ctx : of_json_ctx) (js : json) :
    (maybe_assoc_item_id, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Free", _0) ] ->
        let* _0 = item_id_of_json ctx _0 in
        Ok (ItemFree _0)
    | `Assoc [ ("Assoc", `List [ _0; _1 ]) ] ->
        let* _0 = trait_decl_id_of_json ctx _0 in
        let* _1 = assoc_item_id_of_json ctx _1 in
        Ok (ItemAssoc (_0, _1))
    | _ -> Error "")

and mir_level_of_json (ctx : of_json_ctx) (js : json) :
    (mir_level, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `String "Built" -> Ok Built
    | `String "Promoted" -> Ok Promoted
    | `String "Elaborated" -> Ok Elaborated
    | `String "Optimized" -> Ok Optimized
    | _ -> Error "")

and monomorphize_mut_of_json (ctx : of_json_ctx) (js : json) :
    (monomorphize_mut, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `String "All" -> Ok All
    | `String "ExceptTypes" -> Ok ExceptTypes
    | _ -> Error "")

and rustc_optimize_attr_of_json (ctx : of_json_ctx) (js : json) :
    (rustc_optimize_attr, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `String "Default" -> Ok RustcOptimizeAttrDefault
    | `String "DoNotOptimize" -> Ok RustcOptimizeAttrDoNotOptimize
    | `String "Speed" -> Ok RustcOptimizeAttrSpeed
    | `String "Size" -> Ok RustcOptimizeAttrSize
    | _ -> Error "")

and preset_of_json (ctx : of_json_ctx) (js : json) : (preset, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `String "OldDefaults" -> Ok OldDefaults
    | `String "RawMir" -> Ok RawMir
    | `String "Fast" -> Ok Fast
    | `String "Aeneas" -> Ok Aeneas
    | `String "Eurydice" -> Ok Eurydice
    | `String "Soteria" -> Ok Soteria
    | `String "Tests" -> Ok Tests
    | _ -> Error "")

and ptr_metadata_of_json (ctx : of_json_ctx) (js : json) :
    (ptr_metadata, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `String "None" -> Ok NoMetadata
    | `String "Length" -> Ok Length
    | `Assoc [ ("VTable", _0) ] ->
        let* _0 = type_decl_ref_of_json ctx _0 in
        Ok (VTable _0)
    | `Assoc [ ("InheritFrom", _0) ] ->
        let* _0 = ty_of_json ctx _0 in
        Ok (InheritFrom _0)
    | _ -> Error "")

and raw_attribute_of_json (ctx : of_json_ctx) (js : json) :
    (raw_attribute, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("path", path); ("args", args) ] ->
        let* path = string_of_json ctx path in
        let* args = option_of_json string_of_json ctx args in
        Ok ({ path; args } : raw_attribute)
    | _ -> Error "")

and repr_algorithm_of_json (ctx : of_json_ctx) (js : json) :
    (repr_algorithm, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `String "Rust" -> Ok Rust
    | `String "C" -> Ok C
    | _ -> Error "")

and repr_options_of_json (ctx : of_json_ctx) (js : json) :
    (repr_options, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc
        [
          ("repr_algo", repr_algo);
          ("align_modif", align_modif);
          ("transparent", transparent);
          ("explicit_discr_type", explicit_discr_type);
        ] ->
        let* repr_algo = repr_algorithm_of_json ctx repr_algo in
        let* align_modif =
          option_of_json alignment_modifier_of_json ctx align_modif
        in
        let* transparent = bool_of_json ctx transparent in
        let* explicit_discr_type = bool_of_json ctx explicit_discr_type in
        Ok
          ({ repr_algo; align_modif; transparent; explicit_discr_type }
            : repr_options)
    | _ -> Error "")

and rustc_rustc_version_of_json (ctx : of_json_ctx) (js : json) :
    (rustc_rustc_version, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("major", major); ("minor", minor); ("patch", patch) ] ->
        let* major = int_of_json ctx major in
        let* minor = int_of_json ctx minor in
        let* patch = int_of_json ctx patch in
        Ok ({ major; minor; patch } : rustc_rustc_version)
    | _ -> Error "")

and serialization_format_arg_of_json (ctx : of_json_ctx) (js : json) :
    (serialization_format_arg, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `String "Json" -> Ok Json
    | `String "Postcard" -> Ok Postcard
    | `String "All" -> Ok AllFormats
    | _ -> Error "")

and target_info_of_json (ctx : of_json_ctx) (js : json) :
    (target_info, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc
        [
          ("target_pointer_size", target_pointer_size);
          ("is_little_endian", is_little_endian);
          ("c_enum_min_size", c_enum_min_size);
          ("primitive_alignments", primitive_alignments);
        ] ->
        let* target_pointer_size = int_of_json ctx target_pointer_size in
        let* is_little_endian = bool_of_json ctx is_little_endian in
        let* c_enum_min_size = int_of_json ctx c_enum_min_size in
        let* primitive_alignments =
          index_map_of_json literal_type_of_json int_of_json int_of_json ctx
            primitive_alignments
        in
        Ok
          ({
             target_pointer_size;
             is_little_endian;
             c_enum_min_size;
             primitive_alignments;
           }
            : target_info)
    | _ -> Error "")

and trait_assoc_const_of_json (ctx : of_json_ctx) (js : json) :
    (trait_assoc_const, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc
        [
          ("name", name);
          ("attr_info", attr_info);
          ("ty", ty);
          ("default", default);
        ] ->
        let* name = trait_item_name_of_json ctx name in
        let* attr_info = attr_info_of_json ctx attr_info in
        let* ty = ty_of_json ctx ty in
        let* default = option_of_json global_decl_ref_of_json ctx default in
        Ok ({ name; attr_info; ty; default } : trait_assoc_const)
    | _ -> Error "")

and trait_assoc_ty_of_json (ctx : of_json_ctx) (js : json) :
    (trait_assoc_ty, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc
        [
          ("name", name);
          ("attr_info", attr_info);
          ("default", default);
          ("implied_clauses", implied_clauses);
        ] ->
        let* name = trait_item_name_of_json ctx name in
        let* attr_info = attr_info_of_json ctx attr_info in
        let* default = option_of_json trait_assoc_ty_impl_of_json ctx default in
        let* implied_clauses =
          index_vec_of_json trait_clause_id_of_json trait_param_of_json ctx
            implied_clauses
        in
        Ok ({ name; attr_info; default; implied_clauses } : trait_assoc_ty)
    | _ -> Error "")

and trait_decl_of_json (ctx : of_json_ctx) (js : json) :
    (trait_decl, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc
        [
          ("def_id", def_id);
          ("item_meta", item_meta);
          ("src", src);
          ("generics", generics);
          ("implied_clauses", implied_clauses);
          ("consts", consts);
          ("types", types);
          ("methods", methods);
          ("vtable", vtable);
        ] ->
        let* def_id = trait_decl_id_of_json ctx def_id in
        let* item_meta = item_meta_of_json ctx item_meta in
        let* src = trait_decl_source_of_json ctx src in
        let* generics = generic_params_of_json ctx generics in
        let* implied_clauses =
          index_vec_of_json trait_clause_id_of_json trait_param_of_json ctx
            implied_clauses
        in
        let* consts =
          (fun ctx json ->
            Result.map AssocConstId.map_of_indexed_list
              (opt_indexed_map_of_json assoc_const_id_of_json
                 trait_assoc_const_of_json ctx json))
            ctx consts
        in
        let* types =
          (fun ctx json ->
            Result.map AssocTypeId.map_of_indexed_list
              (opt_indexed_map_of_json assoc_type_id_of_json
                 (binder_of_json trait_assoc_ty_of_json)
                 ctx json))
            ctx types
        in
        let* methods =
          (fun ctx json ->
            Result.map TraitMethodId.map_of_indexed_list
              (opt_indexed_map_of_json trait_method_id_of_json
                 (binder_of_json trait_method_of_json)
                 ctx json))
            ctx methods
        in
        let* vtable = option_of_json type_decl_ref_of_json ctx vtable in
        Ok
          ({
             def_id;
             item_meta;
             src;
             generics;
             implied_clauses;
             consts;
             types;
             methods;
             vtable;
           }
            : trait_decl)
    | _ -> Error "")

and trait_decl_source_of_json (ctx : of_json_ctx) (js : json) :
    (trait_decl_source, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `String "Normal" -> Ok NormalTraitDecl
    | `String "TraitAlias" -> Ok TraitAliasTraitDecl
    | _ -> Error "")

and trait_impl_of_json (ctx : of_json_ctx) (js : json) :
    (trait_impl, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc
        [
          ("def_id", def_id);
          ("item_meta", item_meta);
          ("src", src);
          ("impl_trait", impl_trait);
          ("generics", generics);
          ("implied_trait_refs", implied_trait_refs);
          ("consts", consts);
          ("types", types);
          ("methods", methods);
          ("vtable", vtable);
        ] ->
        let* def_id = trait_impl_id_of_json ctx def_id in
        let* item_meta = item_meta_of_json ctx item_meta in
        let* src = trait_impl_source_of_json ctx src in
        let* impl_trait = trait_decl_ref_of_json ctx impl_trait in
        let* generics = generic_params_of_json ctx generics in
        let* implied_trait_refs =
          index_vec_of_json trait_clause_id_of_json trait_ref_of_json ctx
            implied_trait_refs
        in
        let* consts =
          (fun ctx json ->
            Result.map AssocConstId.map_of_indexed_list
              (opt_indexed_map_of_json assoc_const_id_of_json
                 global_decl_ref_of_json ctx json))
            ctx consts
        in
        let* types =
          (fun ctx json ->
            Result.map AssocTypeId.map_of_indexed_list
              (opt_indexed_map_of_json assoc_type_id_of_json
                 (binder_of_json trait_assoc_ty_impl_of_json)
                 ctx json))
            ctx types
        in
        let* methods =
          (fun ctx json ->
            Result.map TraitMethodId.map_of_indexed_list
              (opt_indexed_map_of_json trait_method_id_of_json
                 (binder_of_json fun_decl_ref_of_json)
                 ctx json))
            ctx methods
        in
        let* vtable = option_of_json global_decl_ref_of_json ctx vtable in
        Ok
          ({
             def_id;
             item_meta;
             src;
             impl_trait;
             generics;
             implied_trait_refs;
             consts;
             types;
             methods;
             vtable;
           }
            : trait_impl)
    | _ -> Error "")

and trait_impl_source_of_json (ctx : of_json_ctx) (js : json) :
    (trait_impl_source, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `String "Normal" -> Ok NormalTraitImpl
    | `String "TraitAlias" -> Ok TraitAliasTraitImpl
    | `Assoc [ ("Closure", `Assoc [ ("kind", kind) ]) ] ->
        let* kind = closure_kind_of_json ctx kind in
        Ok (ClosureTraitImpl kind)
    | `String "Destruct" -> Ok DestructTraitImpl
    | _ -> Error "")

and trait_item_name_of_json (ctx : of_json_ctx) (js : json) :
    (trait_item_name, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | x -> string_of_json ctx x
    | _ -> Error "")

and trait_method_of_json (ctx : of_json_ctx) (js : json) :
    (trait_method, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc
        [
          ("name", name);
          ("item_meta", item_meta);
          ("signature", signature);
          ("default", default);
        ] ->
        let* name = trait_item_name_of_json ctx name in
        let* item_meta = item_meta_of_json ctx item_meta in
        let* signature = fun_sig_of_json ctx signature in
        let* default = option_of_json fun_decl_ref_of_json ctx default in
        Ok ({ name; item_meta; signature; default } : trait_method)
    | _ -> Error "")

and translated_crate_of_json (ctx : of_json_ctx) (js : json) :
    (translated_crate, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc
        [
          ("crate_name", crate_name);
          ("options", options);
          ("target_information", target_information);
          ("files", files);
          ("item_names", item_names);
          ("assoc_item_names", assoc_item_names);
          ("short_names", short_names);
          ("type_decls", type_decls);
          ("fun_decls", fun_decls);
          ("global_decls", global_decls);
          ("trait_decls", trait_decls);
          ("trait_impls", trait_impls);
          ("ordered_decls", ordered_decls);
        ] ->
        let* crate_name = string_of_json ctx crate_name in
        let* options = cli_options_of_json ctx options in
        let* target_information =
          index_map_of_json string_of_json target_info_of_json int_of_json ctx
            target_information
        in
        let* files = index_vec_of_json file_id_of_json file_of_json ctx files in
        let* item_names =
          index_map_of_json item_id_of_json name_of_json int_of_json ctx
            item_names
        in
        let* assoc_item_names =
          (fun ctx json ->
            Result.map TraitDeclId.map_of_indexed_list
              (opt_indexed_map_of_json trait_decl_id_of_json
                 assoc_item_names_of_json ctx json))
            ctx assoc_item_names
        in
        let* short_names =
          index_map_of_json item_id_of_json name_of_json int_of_json ctx
            short_names
        in
        let* type_decls =
          (fun ctx json ->
            Result.map TypeDeclId.map_of_indexed_list
              (opt_indexed_map_of_json type_decl_id_of_json type_decl_of_json
                 ctx json))
            ctx type_decls
        in
        let* fun_decls =
          (fun ctx json ->
            Result.map FunDeclId.map_of_indexed_list
              (opt_indexed_map_of_json fun_decl_id_of_json fun_decl_of_json ctx
                 json))
            ctx fun_decls
        in
        let* global_decls =
          (fun ctx json ->
            Result.map GlobalDeclId.map_of_indexed_list
              (opt_indexed_map_of_json global_decl_id_of_json
                 global_decl_of_json ctx json))
            ctx global_decls
        in
        let* trait_decls =
          (fun ctx json ->
            Result.map TraitDeclId.map_of_indexed_list
              (opt_indexed_map_of_json trait_decl_id_of_json trait_decl_of_json
                 ctx json))
            ctx trait_decls
        in
        let* trait_impls =
          (fun ctx json ->
            Result.map TraitImplId.map_of_indexed_list
              (opt_indexed_map_of_json trait_impl_id_of_json trait_impl_of_json
                 ctx json))
            ctx trait_impls
        in
        let* ordered_decls =
          option_of_json
            (list_of_json declaration_group_of_json)
            ctx ordered_decls
        in
        Ok
          ({
             crate_name;
             options;
             target_information;
             files;
             item_names;
             assoc_item_names;
             short_names;
             type_decls;
             fun_decls;
             global_decls;
             trait_decls;
             trait_impls;
             ordered_decls;
           }
            : translated_crate)
    | _ -> Error "")

and type_decl_of_json (ctx : of_json_ctx) (js : json) :
    (type_decl, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc
        [
          ("def_id", def_id);
          ("item_meta", item_meta);
          ("generics", generics);
          ("src", src);
          ("kind", kind);
          ("layout", layout);
          ("ptr_metadata", ptr_metadata);
        ] ->
        let* def_id = type_decl_id_of_json ctx def_id in
        let* item_meta = item_meta_of_json ctx item_meta in
        let* generics = generic_params_of_json ctx generics in
        let* src = type_source_of_json ctx src in
        let* kind = type_decl_kind_of_json ctx kind in
        let* layout =
          index_map_of_json string_of_json layout_of_json int_of_json ctx layout
        in
        let* ptr_metadata = ptr_metadata_of_json ctx ptr_metadata in
        Ok
          ({ def_id; item_meta; generics; src; kind; layout; ptr_metadata }
            : type_decl)
    | _ -> Error "")

and type_decl_kind_of_json (ctx : of_json_ctx) (js : json) :
    (type_decl_kind, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Struct", _0) ] ->
        let* _0 = index_vec_of_json field_id_of_json field_of_json ctx _0 in
        Ok (Struct _0)
    | `Assoc [ ("Enum", _0) ] ->
        let* _0 = index_vec_of_json variant_id_of_json variant_of_json ctx _0 in
        Ok (Enum _0)
    | `Assoc [ ("Union", _0) ] ->
        let* _0 = index_vec_of_json field_id_of_json field_of_json ctx _0 in
        Ok (Union _0)
    | `String "Opaque" -> Ok Opaque
    | `Assoc [ ("Alias", _0) ] ->
        let* _0 = ty_of_json ctx _0 in
        Ok (Alias _0)
    | `Assoc [ ("Error", _0) ] ->
        let* _0 = string_of_json ctx _0 in
        Ok (TDeclError _0)
    | _ -> Error "")

and type_source_of_json (ctx : of_json_ctx) (js : json) :
    (type_source, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `String "Normal" -> Ok NormalType
    | `Assoc [ ("Closure", `Assoc [ ("info", info) ]) ] ->
        let* info = closure_info_of_json ctx info in
        Ok (ClosureType info)
    | `Assoc
        [
          ( "VTable",
            `Assoc
              [
                ("dyn_predicate", dyn_predicate);
                ("field_map", field_map);
                ("supertrait_map", supertrait_map);
              ] );
        ] ->
        let* dyn_predicate = dyn_predicate_of_json ctx dyn_predicate in
        let* field_map =
          index_vec_of_json field_id_of_json v_table_field_of_json ctx field_map
        in
        let* supertrait_map =
          index_vec_of_json trait_clause_id_of_json
            (option_of_json field_id_of_json)
            ctx supertrait_map
        in
        Ok (VTableType (dyn_predicate, field_map, supertrait_map))
    | _ -> Error "")

and v_table_field_of_json (ctx : of_json_ctx) (js : json) :
    (v_table_field, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `String "Size" -> Ok VTableSize
    | `String "Align" -> Ok VTableAlign
    | `String "Drop" -> Ok VTableDrop
    | `Assoc [ ("Method", _0) ] ->
        let* _0 = trait_method_id_of_json ctx _0 in
        Ok (VTableMethod _0)
    | `Assoc [ ("SuperTrait", _0) ] ->
        let* _0 = trait_clause_id_of_json ctx _0 in
        Ok (VTableSuperTrait _0)
    | _ -> Error "")

and variant_of_json (ctx : of_json_ctx) (js : json) : (variant, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc
        [
          ("id", id);
          ("span", span);
          ("attr_info", attr_info);
          ("name", name);
          ("fields", fields);
          ("discriminant", discriminant);
        ] ->
        let* id = variant_id_of_json ctx id in
        let* span = span_of_json ctx span in
        let* attr_info = attr_info_of_json ctx attr_info in
        let* variant_name = string_of_json ctx name in
        let* fields =
          index_vec_of_json field_id_of_json field_of_json ctx fields
        in
        let* discriminant = literal_of_json ctx discriminant in
        Ok
          ({ id; span; attr_info; variant_name; fields; discriminant }
            : variant)
    | _ -> Error "")

and variant_layout_of_json (ctx : of_json_ctx) (js : json) :
    (variant_layout, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc
        [
          ("field_offsets", field_offsets);
          ("uninhabited", uninhabited);
          ("tagger", tagger);
        ] ->
        let* field_offsets =
          index_vec_of_json field_id_of_json int_of_json ctx field_offsets
        in
        let* uninhabited = bool_of_json ctx uninhabited in
        let* tagger =
          list_of_json
            (pair_of_json int_of_json scalar_value_of_json)
            ctx tagger
        in
        Ok ({ field_offsets; uninhabited; tagger } : variant_layout)
    | _ -> Error "")
