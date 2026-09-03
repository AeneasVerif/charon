(** WARNING: this file is partially auto-generated. Do not edit `OfPostcard.ml`
    by hand. Edit `generate_ml/templates/OfPostcard.ml` instead, or improve the
    code generation tool so avoid the need for hand-writing things.

    `generate_ml/templates/OfPostcard.ml` contains the manual definitions and
    some `(* __REPLACEn__ *)` comments. These comments are replaced by
    auto-generated definitions by running `make generate-asts` in the crate
    root. The code-generation code is in `charon/src/bin/generate-asts`. *)

open OfPostcardBasic
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

module FileTbl = Hashtbl.Make (struct
  type t = FileId.id

  let equal = FileId.equal_id
  let hash = Hashtbl.hash
end)

type of_postcard_ctx = {
  id_to_file_map : file FileTbl.t;
  ty_hashcons_map : ty HashConsId.Map.t ref;
  tref_hashcons_map : trait_ref HashConsId.Map.t ref;
  constant_expr_hashcons_map : constant_expr HashConsId.Map.t ref;
  exact_size_expr_hashcons_map : exact_size_expr HashConsId.Map.t ref;
}

let empty_of_postcard_ctx : of_postcard_ctx =
  {
    id_to_file_map = FileTbl.create 8;
    ty_hashcons_map = ref HashConsId.Map.empty;
    tref_hashcons_map = ref HashConsId.Map.empty;
    constant_expr_hashcons_map = ref HashConsId.Map.empty;
    exact_size_expr_hashcons_map = ref HashConsId.Map.empty;
  }

let hash_consed_val_of_postcard (map : 'a HashConsId.Map.t ref)
    (of_postcard : of_postcard_ctx -> postcard_state -> ('a, string) result)
    (ctx : of_postcard_ctx) (st : postcard_state) : ('a, string) result =
  combine_error_msgs st __FUNCTION__
    (let* tag = int_of_postcard ctx st in
     match tag with
     | 0 ->
         let* id = HashConsId.id_of_postcard ctx st in
         let* v = of_postcard ctx st in
         map := HashConsId.Map.add id v !map;
         Ok v
     | 1 ->
         let* id = HashConsId.id_of_postcard ctx st in
         begin
           match HashConsId.Map.find_opt id !map with
           | Some v -> Ok v
           | None ->
               Error
                 "Hash-consing key not found; there is a serialization \
                  mismatch between Rust and OCaml"
         end
     | 2 -> of_postcard ctx st
     | _ -> Error "invalid hash-consed representation")

let path_buf_of_postcard = string_of_postcard

let opt_indexed_map_of_postcard :
    'a0 'a1.
    (of_postcard_ctx -> postcard_state -> ('a0, string) result) ->
    (of_postcard_ctx -> postcard_state -> ('a1, string) result) ->
    of_postcard_ctx ->
    postcard_state ->
    ('a1 option list, string) result =
 fun arg0_of_postcard arg1_of_postcard ctx st ->
  list_of_postcard (option_of_postcard arg1_of_postcard) ctx st

let rec ___ = ()

and abi_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (abi, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 -> Ok AbiRust
     | 1 -> Ok AbiC
     | 2 ->
         let* _0 = string_of_postcard ctx st in
         Ok (AbiOther _0)
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and abort_kind_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (abort_kind, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 ->
         let* _0 = option_of_postcard name_of_postcard ctx st in
         Ok (Panic _0)
     | 1 -> Ok UndefinedBehavior
     | 2 -> Ok UnwindTerminate
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and aggregate_kind_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (aggregate_kind, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 ->
         let* _0 = type_decl_ref_of_postcard ctx st in
         let* _1 = option_of_postcard variant_id_of_postcard ctx st in
         let* _2 = option_of_postcard field_id_of_postcard ctx st in
         Ok (AggregatedAdt (_0, _1, _2))
     | 1 ->
         let* _0 = ty_of_postcard ctx st in
         let* _1 = constant_expr_of_postcard ctx st in
         Ok (AggregatedArray (_0, _1))
     | 2 ->
         let* _0 = ty_of_postcard ctx st in
         let* _1 = ref_kind_of_postcard ctx st in
         Ok (AggregatedRawPtr (_0, _1))
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and assertion_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (assertion, string) result =
  combine_error_msgs st __FUNCTION__
    (let* cond = operand_of_postcard ctx st in
     let* expected = bool_of_postcard ctx st in
     let* check_kind =
       option_of_postcard builtin_assert_kind_of_postcard ctx st
     in
     Ok ({ cond; expected; check_kind } : assertion))

and assoc_const_id_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (assoc_const_id, string) result =
  combine_error_msgs st __FUNCTION__ (AssocConstId.id_of_postcard ctx st)

and assoc_type_id_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (assoc_type_id, string) result =
  combine_error_msgs st __FUNCTION__ (AssocTypeId.id_of_postcard ctx st)

and binop_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (binop, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 -> Ok BitXor
     | 1 -> Ok BitAnd
     | 2 -> Ok BitOr
     | 3 -> Ok Eq
     | 4 -> Ok Lt
     | 5 -> Ok Le
     | 6 -> Ok Ne
     | 7 -> Ok Ge
     | 8 -> Ok Gt
     | 9 ->
         let* _0 = overflow_mode_of_postcard ctx st in
         Ok (Add _0)
     | 10 ->
         let* _0 = overflow_mode_of_postcard ctx st in
         Ok (Sub _0)
     | 11 ->
         let* _0 = overflow_mode_of_postcard ctx st in
         Ok (Mul _0)
     | 12 ->
         let* _0 = overflow_mode_of_postcard ctx st in
         Ok (Div _0)
     | 13 ->
         let* _0 = overflow_mode_of_postcard ctx st in
         Ok (Rem _0)
     | 14 -> Ok AddChecked
     | 15 -> Ok SubChecked
     | 16 -> Ok MulChecked
     | 17 ->
         let* _0 = overflow_mode_of_postcard ctx st in
         Ok (Shl _0)
     | 18 ->
         let* _0 = overflow_mode_of_postcard ctx st in
         Ok (Shr _0)
     | 19 -> Ok Offset
     | 20 -> Ok Cmp
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and binder_of_postcard :
    'a0.
    (of_postcard_ctx -> postcard_state -> ('a0, string) result) ->
    of_postcard_ctx ->
    postcard_state ->
    ('a0 binder, string) result =
 fun arg0_of_postcard ctx st ->
  combine_error_msgs st __FUNCTION__
    (let* binder_params = generic_params_of_postcard ctx st in
     let* binder_value = arg0_of_postcard ctx st in
     let* _ = binder_kind_of_postcard ctx st in
     Ok ({ binder_params; binder_value } : _ binder))

and binder_kind_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (binder_kind, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 ->
         let* _0 = trait_decl_id_of_postcard ctx st in
         let* _1 = assoc_type_id_of_postcard ctx st in
         Ok (BKTraitType (_0, _1))
     | 1 ->
         let* _0 = trait_decl_id_of_postcard ctx st in
         let* _1 = trait_method_id_of_postcard ctx st in
         Ok (BKTraitMethod (_0, _1))
     | 2 -> Ok BKInherentImplBlock
     | 3 -> Ok BKDyn
     | 4 -> Ok BKOther
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and borrow_kind_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (borrow_kind, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 -> Ok BShared
     | 1 -> Ok BMut
     | 2 -> Ok BTwoPhaseMut
     | 3 -> Ok BShallow
     | 4 -> Ok BUniqueImmutable
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and borrowck_statement_of_postcard (ctx : of_postcard_ctx) (st : postcard_state)
    : (borrowck_statement, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 ->
         let* _0 = place_of_postcard ctx st in
         Ok (FakeRead _0)
     | 1 ->
         let* place = place_of_postcard ctx st in
         let* ty = ty_of_postcard ctx st in
         let* variance = variance_of_postcard ctx st in
         Ok (SetType (place, ty, variance))
     | 2 ->
         let* _0 = ty_of_postcard ctx st in
         let* _1 = region_of_postcard ctx st in
         Ok (SetOutlives (_0, _1))
     | 3 ->
         let* _0 = trait_ref_of_postcard ctx st in
         Ok (PredicateHolds _0)
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and branch_id_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (branch_id, string) result =
  combine_error_msgs st __FUNCTION__ (BranchId.id_of_postcard ctx st)

and builtin_assert_kind_of_postcard (ctx : of_postcard_ctx)
    (st : postcard_state) : (builtin_assert_kind, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 ->
         let* len = operand_of_postcard ctx st in
         let* index = operand_of_postcard ctx st in
         Ok (BoundsCheck (len, index))
     | 1 ->
         let* _0 = binop_of_postcard ctx st in
         let* _1 = operand_of_postcard ctx st in
         let* _2 = operand_of_postcard ctx st in
         Ok (Overflow (_0, _1, _2))
     | 2 ->
         let* _0 = operand_of_postcard ctx st in
         Ok (OverflowNeg _0)
     | 3 ->
         let* _0 = operand_of_postcard ctx st in
         Ok (DivisionByZero _0)
     | 4 ->
         let* _0 = operand_of_postcard ctx st in
         Ok (RemainderByZero _0)
     | 5 ->
         let* required = operand_of_postcard ctx st in
         let* found = operand_of_postcard ctx st in
         Ok (MisalignedPointerDereference (required, found))
     | 6 -> Ok NullPointerDereference
     | 7 -> Ok NullReferenceCreated
     | 8 ->
         let* _0 = operand_of_postcard ctx st in
         Ok (InvalidEnumConstruction _0)
     | 9 -> Ok ResumedAfterReturn
     | 10 -> Ok ResumedAfterPanic
     | 11 -> Ok ResumedAfterDrop
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and builtin_fun_id_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (builtin_fun_id, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 -> Ok ArrayToSliceShared
     | 1 -> Ok ArrayToSliceMut
     | 2 -> Ok ArrayRepeat
     | 3 ->
         let* _0 = builtin_index_op_of_postcard ctx st in
         Ok (Index _0)
     | 4 ->
         let* _0 = ref_kind_of_postcard ctx st in
         Ok (PtrFromParts _0)
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and builtin_impl_data_of_postcard (ctx : of_postcard_ctx) (st : postcard_state)
    : (builtin_impl_data, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 -> Ok BuiltinAuto
     | 1 -> Ok BuiltinSized
     | 2 -> Ok BuiltinMetaSized
     | 3 -> Ok BuiltinPointeeSized
     | 4 -> Ok BuiltinCopy
     | 5 -> Ok BuiltinClone
     | 6 -> Ok BuiltinTuple
     | 7 -> Ok BuiltinTransmute
     | 8 -> Ok BuiltinUnsize
     | 9 -> Ok BuiltinPointee
     | 10 -> Ok BuiltinDiscriminantKind
     | 11 -> Ok BuiltinFn
     | 12 -> Ok BuiltinFnMut
     | 13 -> Ok BuiltinFnOnce
     | 14 -> Ok BuiltinFnPtr
     | 15 -> Ok BuiltinAsyncFn
     | 16 -> Ok BuiltinAsyncFnMut
     | 17 -> Ok BuiltinAsyncFnOnce
     | 18 -> Ok BuiltinCoroutine
     | 19 -> Ok BuiltinFuture
     | 20 -> Ok BuiltinTryAsDynCompatible
     | 21 -> Ok BuiltinNoopDestruct
     | 22 -> Ok BuiltinUntrackedDestruct
     | 23 -> Ok BuiltinRemovedAdtClause
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and builtin_index_op_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (builtin_index_op, string) result =
  combine_error_msgs st __FUNCTION__
    (let* is_array = bool_of_postcard ctx st in
     let* mutability = ref_kind_of_postcard ctx st in
     let* is_range = bool_of_postcard ctx st in
     Ok ({ is_array; mutability; is_range } : builtin_index_op))

and builtin_path_elem_of_postcard (ctx : of_postcard_ctx) (st : postcard_state)
    : (builtin_path_elem, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 ->
         let* _0 = usize_of_postcard ctx st in
         Ok (PeTuple _0)
     | 1 -> Ok PeStr
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and builtin_ty_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (builtin_ty, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 -> Ok TTuple
     | 1 -> Ok TBox
     | 2 -> Ok TStr
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and byte_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (byte, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 -> Ok Uninit
     | 1 ->
         let* _0 = u8_of_postcard ctx st in
         Ok (Value _0)
     | 2 ->
         let* _0 = provenance_of_postcard ctx st in
         let* _1 = u8_of_postcard ctx st in
         Ok (Provenance (_0, _1))
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and call_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (call, string) result =
  combine_error_msgs st __FUNCTION__
    (let* func = fn_operand_of_postcard ctx st in
     let* args = list_of_postcard operand_of_postcard ctx st in
     let* dest = place_of_postcard ctx st in
     Ok ({ func; args; dest } : call))

and cast_kind_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (cast_kind, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 ->
         let* _0 = literal_type_of_postcard ctx st in
         let* _1 = literal_type_of_postcard ctx st in
         Ok (CastScalar (_0, _1))
     | 1 ->
         let* _0 = ty_of_postcard ctx st in
         let* _1 = ty_of_postcard ctx st in
         Ok (CastRawPtr (_0, _1))
     | 2 ->
         let* _0 = ty_of_postcard ctx st in
         let* _1 = ty_of_postcard ctx st in
         Ok (CastFnPtr (_0, _1))
     | 3 ->
         let* _0 = ty_of_postcard ctx st in
         let* _1 = ty_of_postcard ctx st in
         let* _2 = unsizing_metadata_of_postcard ctx st in
         Ok (CastUnsize (_0, _1, _2))
     | 4 ->
         let* _0 = ty_of_postcard ctx st in
         let* _1 = ty_of_postcard ctx st in
         Ok (CastTransmute (_0, _1))
     | 5 ->
         let* _0 = ty_of_postcard ctx st in
         let* _1 = ty_of_postcard ctx st in
         Ok (CastConcretize (_0, _1))
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and const_generic_param_of_postcard (ctx : of_postcard_ctx)
    (st : postcard_state) : (const_generic_param, string) result =
  combine_error_msgs st __FUNCTION__
    (let* index = const_generic_var_id_of_postcard ctx st in
     let* name = string_of_postcard ctx st in
     let* ty = ty_of_postcard ctx st in
     Ok ({ index; name; ty } : const_generic_param))

and const_generic_var_id_of_postcard (ctx : of_postcard_ctx)
    (st : postcard_state) : (const_generic_var_id, string) result =
  combine_error_msgs st __FUNCTION__ (ConstGenericVarId.id_of_postcard ctx st)

and constant_expr_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (constant_expr, string) result =
  combine_error_msgs st __FUNCTION__
    (hash_consed_val_of_postcard ctx.constant_expr_hashcons_map
       (fun ctx st ->
         let* contents =
           pair_of_postcard constant_expr_kind_of_postcard ty_of_postcard ctx st
         in
         let kind, ty = contents in
         Ok ({ kind; ty } : constant_expr))
       ctx st)

and constant_expr_kind_of_postcard (ctx : of_postcard_ctx) (st : postcard_state)
    : (constant_expr_kind, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 ->
         let* _0 = literal_of_postcard ctx st in
         Ok (CLiteral _0)
     | 1 ->
         let* _0 = option_of_postcard variant_id_of_postcard ctx st in
         let* _1 = list_of_postcard constant_expr_of_postcard ctx st in
         Ok (CAdt (_0, _1))
     | 2 ->
         let* _0 = list_of_postcard constant_expr_of_postcard ctx st in
         Ok (CArray _0)
     | 3 ->
         let* _0 = global_decl_ref_of_postcard ctx st in
         Ok (CGlobal _0)
     | 4 ->
         let* _0 = trait_ref_of_postcard ctx st in
         let* _1 = assoc_const_id_of_postcard ctx st in
         Ok (CTraitConst (_0, _1))
     | 5 ->
         let* _0 = trait_ref_of_postcard ctx st in
         Ok (CVTableRef _0)
     | 6 ->
         let* _0 = type_decl_ref_of_postcard ctx st in
         let* _1 = variant_id_of_postcard ctx st in
         Ok (CDiscriminant (_0, _1))
     | 7 ->
         let* _0 = constant_expr_of_postcard ctx st in
         let* _1 = option_of_postcard unsizing_metadata_of_postcard ctx st in
         Ok (CRef (_0, _1))
     | 8 ->
         let* _0 = ref_kind_of_postcard ctx st in
         let* _1 = constant_expr_of_postcard ctx st in
         let* _2 = option_of_postcard unsizing_metadata_of_postcard ctx st in
         Ok (CPtr (_0, _1, _2))
     | 9 ->
         let* _0 =
           de_bruijn_var_of_postcard const_generic_var_id_of_postcard ctx st
         in
         Ok (CVar _0)
     | 10 ->
         let* _0 = fn_ptr_of_postcard ctx st in
         let* _1 = list_of_postcard constant_expr_of_postcard ctx st in
         Ok (CCall (_0, _1))
     | 11 ->
         let* _0 = fn_ptr_of_postcard ctx st in
         Ok (CFnDef _0)
     | 12 ->
         let* _0 = fn_ptr_of_postcard ctx st in
         Ok (CFnPtr _0)
     | 13 ->
         let* _0 = ty_of_postcard ctx st in
         Ok (CSizeOf _0)
     | 14 ->
         let* _0 = ty_of_postcard ctx st in
         Ok (CAlignOf _0)
     | 15 ->
         let* _0 = ty_of_postcard ctx st in
         Ok (CTypeId _0)
     | 16 ->
         let* _0 = big_uint_of_postcard ctx st in
         Ok (CPtrNoProvenance _0)
     | 17 ->
         let* _0 = list_of_postcard byte_of_postcard ctx st in
         Ok (CRawMemory _0)
     | 18 ->
         let* _0 = string_of_postcard ctx st in
         Ok (COpaque _0)
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and de_bruijn_id_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (de_bruijn_id, string) result =
  combine_error_msgs st __FUNCTION__ (usize_of_postcard ctx st)

and de_bruijn_var_of_postcard :
    'a0.
    (of_postcard_ctx -> postcard_state -> ('a0, string) result) ->
    of_postcard_ctx ->
    postcard_state ->
    ('a0 de_bruijn_var, string) result =
 fun arg0_of_postcard ctx st ->
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 ->
         let* _0 = de_bruijn_id_of_postcard ctx st in
         let* _1 = arg0_of_postcard ctx st in
         Ok (Bound (_0, _1))
     | 1 ->
         let* _0 = arg0_of_postcard ctx st in
         Ok (Free _0)
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and disambiguator_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (disambiguator, string) result =
  combine_error_msgs st __FUNCTION__ (Disambiguator.id_of_postcard ctx st)

and drop_kind_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (drop_kind, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 -> Ok Precise
     | 1 -> Ok Conditional
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and dyn_predicate_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (dyn_predicate, string) result =
  combine_error_msgs st __FUNCTION__
    (let* binder = binder_of_postcard ty_of_postcard ctx st in
     Ok ({ binder } : dyn_predicate))

and field_id_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (field_id, string) result =
  combine_error_msgs st __FUNCTION__ (FieldId.id_of_postcard ctx st)

and file_id_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (file_id, string) result =
  combine_error_msgs st __FUNCTION__
    (let* file_id = FileId.id_of_postcard ctx st in
     try Ok (FileTbl.find ctx.id_to_file_map file_id)
     with Not_found ->
       let valid_keys =
         FileTbl.fold
           (fun key _ acc -> FileId.to_string key :: acc)
           ctx.id_to_file_map []
       in
       Error
         ("unknown file id: " ^ FileId.to_string file_id ^ ". valid ids are: "
         ^ String.concat ", " valid_keys))

and float_type_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (float_type, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 -> Ok F16
     | 1 -> Ok F32
     | 2 -> Ok F64
     | 3 -> Ok F128
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and float_value_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (float_value, string) result =
  combine_error_msgs st __FUNCTION__
    (let* float_value = string_of_postcard ctx st in
     let* float_ty = float_type_of_postcard ctx st in
     Ok ({ float_value; float_ty } : float_value))

and fn_operand_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (fn_operand, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 ->
         let* _0 = fn_ptr_of_postcard ctx st in
         Ok (FnOpRegular _0)
     | 1 ->
         let* _0 = operand_of_postcard ctx st in
         Ok (FnOpDynamic _0)
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and fn_ptr_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (fn_ptr, string) result =
  combine_error_msgs st __FUNCTION__
    (let* kind = box_of_postcard fn_ptr_kind_of_postcard ctx st in
     let* generics = box_of_postcard generic_args_of_postcard ctx st in
     Ok ({ kind; generics } : fn_ptr))

and fn_ptr_kind_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (fn_ptr_kind, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 ->
         let* _0 = fun_id_of_postcard ctx st in
         Ok (FunId _0)
     | 1 ->
         let* _0 = trait_ref_of_postcard ctx st in
         let* _1 = trait_method_id_of_postcard ctx st in
         Ok (TraitMethod (_0, _1))
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and fun_decl_id_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (fun_decl_id, string) result =
  combine_error_msgs st __FUNCTION__ (FunDeclId.id_of_postcard ctx st)

and fun_decl_ref_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (fun_decl_ref, string) result =
  combine_error_msgs st __FUNCTION__
    (let* id = fun_decl_id_of_postcard ctx st in
     let* generics = box_of_postcard generic_args_of_postcard ctx st in
     Ok ({ id; generics } : fun_decl_ref))

and fun_id_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (fun_id, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 ->
         let* _0 = fun_decl_id_of_postcard ctx st in
         Ok (FRegular _0)
     | 1 ->
         let* _0 = builtin_fun_id_of_postcard ctx st in
         Ok (FBuiltin _0)
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and fun_sig_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (fun_sig, string) result =
  combine_error_msgs st __FUNCTION__
    (let* is_unsafe = bool_of_postcard ctx st in
     let* abi = abi_of_postcard ctx st in
     let* is_variadic = bool_of_postcard ctx st in
     let* inputs = list_of_postcard ty_of_postcard ctx st in
     let* output = ty_of_postcard ctx st in
     Ok ({ is_unsafe; abi; is_variadic; inputs; output } : fun_sig))

and generic_args_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (generic_args, string) result =
  combine_error_msgs st __FUNCTION__
    (let* regions =
       index_vec_of_postcard region_id_of_postcard region_of_postcard ctx st
     in
     let* types =
       index_vec_of_postcard type_var_id_of_postcard ty_of_postcard ctx st
     in
     let* const_generics =
       index_vec_of_postcard const_generic_var_id_of_postcard
         constant_expr_of_postcard ctx st
     in
     let* trait_refs =
       index_vec_of_postcard trait_clause_id_of_postcard trait_ref_of_postcard
         ctx st
     in
     Ok ({ regions; types; const_generics; trait_refs } : generic_args))

and generic_params_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (generic_params, string) result =
  combine_error_msgs st __FUNCTION__
    (let* regions =
       index_vec_of_postcard region_id_of_postcard region_param_of_postcard ctx
         st
     in
     let* types =
       index_vec_of_postcard type_var_id_of_postcard type_param_of_postcard ctx
         st
     in
     let* const_generics =
       index_vec_of_postcard const_generic_var_id_of_postcard
         const_generic_param_of_postcard ctx st
     in
     let* trait_clauses =
       index_vec_of_postcard trait_clause_id_of_postcard trait_param_of_postcard
         ctx st
     in
     let* regions_outlive =
       list_of_postcard
         (region_binder_of_postcard
            (outlives_pred_of_postcard region_of_postcard region_of_postcard))
         ctx st
     in
     let* types_outlive =
       list_of_postcard
         (region_binder_of_postcard
            (outlives_pred_of_postcard ty_of_postcard region_of_postcard))
         ctx st
     in
     let* trait_type_constraints =
       index_vec_of_postcard trait_type_constraint_id_of_postcard
         (region_binder_of_postcard trait_type_constraint_of_postcard)
         ctx st
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
         : generic_params))

and global_decl_id_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (global_decl_id, string) result =
  combine_error_msgs st __FUNCTION__ (GlobalDeclId.id_of_postcard ctx st)

and global_decl_ref_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (global_decl_ref, string) result =
  combine_error_msgs st __FUNCTION__
    (let* id = global_decl_id_of_postcard ctx st in
     let* generics = box_of_postcard generic_args_of_postcard ctx st in
     Ok ({ id; generics } : global_decl_ref))

and hash_consed_of_postcard :
    'a0.
    (of_postcard_ctx -> postcard_state -> ('a0, string) result) ->
    of_postcard_ctx ->
    postcard_state ->
    ('a0 hash_consed, string) result =
 fun arg0_of_postcard ctx st ->
  combine_error_msgs st __FUNCTION__
    (Error "use `hash_consed_val_of_postcard` instead")

and impl_elem_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (impl_elem, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 ->
         let* _0 = box_of_postcard (binder_of_postcard ty_of_postcard) ctx st in
         Ok (ImplElemTy _0)
     | 1 ->
         let* _0 = trait_impl_id_of_postcard ctx st in
         Ok (ImplElemTrait _0)
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and index_vec_of_postcard :
    'a0 'a1.
    (of_postcard_ctx -> postcard_state -> ('a0, string) result) ->
    (of_postcard_ctx -> postcard_state -> ('a1, string) result) ->
    of_postcard_ctx ->
    postcard_state ->
    ('a1 list, string) result =
 fun arg0_of_postcard arg1_of_postcard ctx st ->
  combine_error_msgs st __FUNCTION__ (list_of_postcard arg1_of_postcard ctx st)

and int_ty_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (int_ty, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 -> Ok Isize
     | 1 -> Ok I8
     | 2 -> Ok I16
     | 3 -> Ok I32
     | 4 -> Ok I64
     | 5 -> Ok I128
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and lifetime_mutability_of_postcard (ctx : of_postcard_ctx)
    (st : postcard_state) : (lifetime_mutability, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 -> Ok LtMutable
     | 1 -> Ok LtShared
     | 2 -> Ok LtUnknown
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and literal_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (literal, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 ->
         let* _0 = scalar_value_of_postcard ctx st in
         Ok (VScalar _0)
     | 1 ->
         let* _0 = float_value_of_postcard ctx st in
         Ok (VFloat _0)
     | 2 ->
         let* _0 = bool_of_postcard ctx st in
         Ok (VBool _0)
     | 3 ->
         let* _0 = char_of_postcard ctx st in
         Ok (VChar _0)
     | 4 ->
         let* _0 = list_of_postcard u8_of_postcard ctx st in
         Ok (VByteStr _0)
     | 5 ->
         let* _0 = string_of_postcard ctx st in
         Ok (VStr _0)
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and literal_type_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (literal_type, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 ->
         let* _0 = int_ty_of_postcard ctx st in
         Ok (TInt _0)
     | 1 ->
         let* _0 = u_int_ty_of_postcard ctx st in
         Ok (TUInt _0)
     | 2 ->
         let* _0 = float_type_of_postcard ctx st in
         Ok (TFloat _0)
     | 3 -> Ok TBool
     | 4 -> Ok TChar
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and loc_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (loc, string) result =
  combine_error_msgs st __FUNCTION__
    (let* line = u32_of_postcard ctx st in
     let* col = u32_of_postcard ctx st in
     Ok ({ line; col } : loc))

and local_id_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (local_id, string) result =
  combine_error_msgs st __FUNCTION__ (LocalId.id_of_postcard ctx st)

and name_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (name, string) result =
  combine_error_msgs st __FUNCTION__
    (list_of_postcard path_elem_of_postcard ctx st)

and nullop_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (nullop, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 -> Ok SizeOf
     | 1 -> Ok AlignOf
     | 2 ->
         let* _0 = type_decl_ref_of_postcard ctx st in
         let* _1 = option_of_postcard variant_id_of_postcard ctx st in
         let* _2 = field_id_of_postcard ctx st in
         Ok (OffsetOf (_0, _1, _2))
     | 3 -> Ok UbChecks
     | 4 -> Ok OverflowChecks
     | 5 -> Ok ContractChecks
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and operand_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (operand, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 ->
         let* _0 = place_of_postcard ctx st in
         Ok (Copy _0)
     | 1 ->
         let* _0 = place_of_postcard ctx st in
         Ok (Move _0)
     | 2 ->
         let* _0 = constant_expr_of_postcard ctx st in
         Ok (Constant _0)
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and outlives_pred_of_postcard :
    'a0 'a1.
    (of_postcard_ctx -> postcard_state -> ('a0, string) result) ->
    (of_postcard_ctx -> postcard_state -> ('a1, string) result) ->
    of_postcard_ctx ->
    postcard_state ->
    (('a0, 'a1) outlives_pred, string) result =
 fun arg0_of_postcard arg1_of_postcard ctx st ->
  combine_error_msgs st __FUNCTION__
    (let* _0 = arg0_of_postcard ctx st in
     let* _1 = arg1_of_postcard ctx st in
     Ok (_0, _1))

and overflow_mode_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (overflow_mode, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 -> Ok OPanic
     | 1 -> Ok OUB
     | 2 -> Ok OWrap
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and path_elem_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (path_elem, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 ->
         let* _0 = string_of_postcard ctx st in
         let* _1 = disambiguator_of_postcard ctx st in
         Ok (PeIdent (_0, _1))
     | 1 ->
         let* _0 = impl_elem_of_postcard ctx st in
         Ok (PeImpl _0)
     | 2 ->
         let* _0 =
           box_of_postcard (binder_of_postcard generic_args_of_postcard) ctx st
         in
         Ok (PeInstantiated _0)
     | 3 ->
         let* _0 = string_of_postcard ctx st in
         Ok (PeTarget _0)
     | 4 ->
         let* _0 = builtin_path_elem_of_postcard ctx st in
         Ok (PeBuiltin _0)
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and place_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (place, string) result =
  combine_error_msgs st __FUNCTION__
    (let* kind = place_kind_of_postcard ctx st in
     let* ty = ty_of_postcard ctx st in
     Ok ({ kind; ty } : place))

and place_kind_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (place_kind, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 ->
         let* _0 = local_id_of_postcard ctx st in
         Ok (PlaceLocal _0)
     | 1 ->
         let* _0 = box_of_postcard place_of_postcard ctx st in
         let* _1 = projection_elem_of_postcard ctx st in
         Ok (PlaceProjection (_0, _1))
     | 2 ->
         let* _0 = global_decl_ref_of_postcard ctx st in
         Ok (PlaceGlobal _0)
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and predicate_origin_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (predicate_origin, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 -> Ok WhereClauseOnFn
     | 1 -> Ok WhereClauseOnType
     | 2 -> Ok WhereClauseOnImpl
     | 3 -> Ok TraitSelf
     | 4 -> Ok WhereClauseOnTrait
     | 5 ->
         let* _0 = assoc_type_id_of_postcard ctx st in
         Ok (TraitItem _0)
     | 6 -> Ok OriginDyn
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and projection_elem_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (projection_elem, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 -> Ok Deref
     | 1 ->
         let* _0 = option_of_postcard variant_id_of_postcard ctx st in
         let* _1 = field_id_of_postcard ctx st in
         Ok (Field (_0, _1))
     | 2 -> Ok PtrMetadata
     | 3 ->
         let* offset = box_of_postcard operand_of_postcard ctx st in
         let* from_end = bool_of_postcard ctx st in
         Ok (ProjIndex (offset, from_end))
     | 4 ->
         let* from = box_of_postcard operand_of_postcard ctx st in
         let* to_ = box_of_postcard operand_of_postcard ctx st in
         let* from_end = bool_of_postcard ctx st in
         Ok (Subslice (from, to_, from_end))
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and provenance_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (provenance, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 ->
         let* _0 = global_decl_ref_of_postcard ctx st in
         Ok (ProvGlobal _0)
     | 1 ->
         let* _0 = fun_decl_ref_of_postcard ctx st in
         Ok (ProvFunction _0)
     | 2 -> Ok ProvUnknown
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and ref_kind_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (ref_kind, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 -> Ok RMut
     | 1 -> Ok RShared
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and region_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (region, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 ->
         let* _0 = de_bruijn_var_of_postcard region_id_of_postcard ctx st in
         Ok (RVar _0)
     | 1 -> Ok RStatic
     | 2 ->
         let* _0 = region_id_of_postcard ctx st in
         Ok (RBody _0)
     | 3 -> Ok RErased
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and region_binder_of_postcard :
    'a0.
    (of_postcard_ctx -> postcard_state -> ('a0, string) result) ->
    of_postcard_ctx ->
    postcard_state ->
    ('a0 region_binder, string) result =
 fun arg0_of_postcard ctx st ->
  combine_error_msgs st __FUNCTION__
    (let* binder_regions =
       index_vec_of_postcard region_id_of_postcard region_param_of_postcard ctx
         st
     in
     let* binder_value = arg0_of_postcard ctx st in
     Ok ({ binder_regions; binder_value } : _ region_binder))

and region_id_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (region_id, string) result =
  combine_error_msgs st __FUNCTION__ (RegionId.id_of_postcard ctx st)

and region_param_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (region_param, string) result =
  combine_error_msgs st __FUNCTION__
    (let* index = region_id_of_postcard ctx st in
     let* name = option_of_postcard string_of_postcard ctx st in
     let* variance = variance_of_postcard ctx st in
     let* mutability = lifetime_mutability_of_postcard ctx st in
     Ok ({ index; name; variance; mutability } : region_param))

and rvalue_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (rvalue, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 ->
         let* _0 = operand_of_postcard ctx st in
         let* _1 = with_retag_of_postcard ctx st in
         Ok (Use (_0, _1))
     | 1 ->
         let* place = place_of_postcard ctx st in
         let* kind = borrow_kind_of_postcard ctx st in
         let* ptr_metadata = operand_of_postcard ctx st in
         Ok (RvRef (place, kind, ptr_metadata))
     | 2 ->
         let* place = place_of_postcard ctx st in
         let* kind = ref_kind_of_postcard ctx st in
         let* ptr_metadata = operand_of_postcard ctx st in
         Ok (RawPtr (place, kind, ptr_metadata))
     | 3 ->
         let* _0 = binop_of_postcard ctx st in
         let* _1 = operand_of_postcard ctx st in
         let* _2 = operand_of_postcard ctx st in
         Ok (BinaryOp (_0, _1, _2))
     | 4 ->
         let* _0 = unop_of_postcard ctx st in
         let* _1 = operand_of_postcard ctx st in
         Ok (UnaryOp (_0, _1))
     | 5 ->
         let* _0 = nullop_of_postcard ctx st in
         let* _1 = ty_of_postcard ctx st in
         Ok (NullaryOp (_0, _1))
     | 6 ->
         let* _0 = place_of_postcard ctx st in
         Ok (Discriminant _0)
     | 7 ->
         let* _0 = aggregate_kind_of_postcard ctx st in
         let* _1 = list_of_postcard operand_of_postcard ctx st in
         Ok (Aggregate (_0, _1))
     | 8 ->
         let* _0 = place_of_postcard ctx st in
         let* _1 = ty_of_postcard ctx st in
         let* _2 = option_of_postcard constant_expr_of_postcard ctx st in
         Ok (Len (_0, _1, _2))
     | 9 ->
         let* _0 = operand_of_postcard ctx st in
         let* _1 = ty_of_postcard ctx st in
         let* _2 = constant_expr_of_postcard ctx st in
         Ok (Repeat (_0, _1, _2))
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and scalar_value_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (scalar_value, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 ->
         let* _0 = u_int_ty_of_postcard ctx st in
         let* _1 = big_uint_of_postcard ctx st in
         Ok (UnsignedScalar (_0, _1))
     | 1 ->
         let* _0 = int_ty_of_postcard ctx st in
         let* _1 = big_int_of_postcard ctx st in
         Ok (SignedScalar (_0, _1))
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and span_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (span, string) result =
  combine_error_msgs st __FUNCTION__
    (let* data = span_data_of_postcard ctx st in
     let* generated_from_span =
       option_of_postcard span_data_of_postcard ctx st
     in
     Ok ({ data; generated_from_span } : span))

and span_data_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (span_data, string) result =
  combine_error_msgs st __FUNCTION__
    (let* file = file_id_of_postcard ctx st in
     let* beg_loc = loc_of_postcard ctx st in
     let* end_loc = loc_of_postcard ctx st in
     Ok ({ file; beg_loc; end_loc } : span_data))

and switch_data_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (switch_data, string) result =
  combine_error_msgs st __FUNCTION__
    (let* scrutinee = switch_scrutinee_of_postcard ctx st in
     let* branches =
       list_of_postcard
         (pair_of_postcard constant_expr_of_postcard branch_id_of_postcard)
         ctx st
     in
     let* fallback = option_of_postcard branch_id_of_postcard ctx st in
     Ok ({ scrutinee; branches; fallback } : switch_data))

and switch_scrutinee_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (switch_scrutinee, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 ->
         let* _0 = operand_of_postcard ctx st in
         Ok (SwitchValue _0)
     | 1 ->
         let* _0 = place_of_postcard ctx st in
         Ok (SwitchDiscriminant _0)
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and trait_assoc_ty_impl_of_postcard (ctx : of_postcard_ctx)
    (st : postcard_state) : (trait_assoc_ty_impl, string) result =
  combine_error_msgs st __FUNCTION__
    (let* value = ty_of_postcard ctx st in
     let* implied_trait_refs =
       index_vec_of_postcard trait_clause_id_of_postcard trait_ref_of_postcard
         ctx st
     in
     Ok ({ value; implied_trait_refs } : trait_assoc_ty_impl))

and trait_clause_id_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (trait_clause_id, string) result =
  combine_error_msgs st __FUNCTION__ (TraitClauseId.id_of_postcard ctx st)

and trait_decl_id_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (trait_decl_id, string) result =
  combine_error_msgs st __FUNCTION__ (TraitDeclId.id_of_postcard ctx st)

and trait_decl_ref_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (trait_decl_ref, string) result =
  combine_error_msgs st __FUNCTION__
    (let* id = trait_decl_id_of_postcard ctx st in
     let* generics = box_of_postcard generic_args_of_postcard ctx st in
     Ok ({ id; generics } : trait_decl_ref))

and trait_impl_id_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (trait_impl_id, string) result =
  combine_error_msgs st __FUNCTION__ (TraitImplId.id_of_postcard ctx st)

and trait_impl_ref_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (trait_impl_ref, string) result =
  combine_error_msgs st __FUNCTION__
    (let* id = trait_impl_id_of_postcard ctx st in
     let* generics = box_of_postcard generic_args_of_postcard ctx st in
     Ok ({ id; generics } : trait_impl_ref))

and trait_method_id_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (trait_method_id, string) result =
  combine_error_msgs st __FUNCTION__ (TraitMethodId.id_of_postcard ctx st)

and trait_param_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (trait_param, string) result =
  combine_error_msgs st __FUNCTION__
    (let* clause_id = trait_clause_id_of_postcard ctx st in
     let* span = option_of_postcard span_of_postcard ctx st in
     let* origin = predicate_origin_of_postcard ctx st in
     let* trait = region_binder_of_postcard trait_decl_ref_of_postcard ctx st in
     Ok ({ clause_id; span; origin; trait } : trait_param))

and trait_ref_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (trait_ref, string) result =
  combine_error_msgs st __FUNCTION__
    (hash_consed_val_of_postcard ctx.tref_hashcons_map
       trait_ref_contents_of_postcard ctx st)

and trait_ref_contents_of_postcard (ctx : of_postcard_ctx) (st : postcard_state)
    : (trait_ref_contents, string) result =
  combine_error_msgs st __FUNCTION__
    (let* kind = trait_ref_kind_of_postcard ctx st in
     let* trait_decl_ref =
       region_binder_of_postcard trait_decl_ref_of_postcard ctx st
     in
     Ok ({ kind; trait_decl_ref } : trait_ref_contents))

and trait_ref_kind_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (trait_ref_kind, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 ->
         let* _0 = trait_impl_ref_of_postcard ctx st in
         Ok (TraitImpl _0)
     | 1 ->
         let* _0 =
           de_bruijn_var_of_postcard trait_clause_id_of_postcard ctx st
         in
         Ok (Clause _0)
     | 2 ->
         let* _0 = box_of_postcard trait_ref_of_postcard ctx st in
         let* _1 = trait_clause_id_of_postcard ctx st in
         Ok (ParentClause (_0, _1))
     | 3 ->
         let* _0 = box_of_postcard trait_ref_of_postcard ctx st in
         let* _1 = assoc_type_id_of_postcard ctx st in
         let* _2 = trait_clause_id_of_postcard ctx st in
         Ok (ItemClause (_0, _1, _2))
     | 4 -> Ok Self
     | 5 ->
         let* builtin_data = builtin_impl_data_of_postcard ctx st in
         let* parent_trait_refs =
           index_vec_of_postcard trait_clause_id_of_postcard
             trait_ref_of_postcard ctx st
         in
         let* types =
           (fun ctx st ->
             Result.map AssocTypeId.map_of_indexed_list
               (opt_indexed_map_of_postcard assoc_type_id_of_postcard
                  trait_assoc_ty_impl_of_postcard ctx st))
             ctx st
         in
         let* vtable = option_of_postcard global_decl_ref_of_postcard ctx st in
         Ok (BuiltinOrAuto (builtin_data, parent_trait_refs, types, vtable))
     | 6 -> Ok Dyn
     | 7 ->
         let* _0 = string_of_postcard ctx st in
         Ok (UnknownTrait _0)
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and trait_type_constraint_of_postcard (ctx : of_postcard_ctx)
    (st : postcard_state) : (trait_type_constraint, string) result =
  combine_error_msgs st __FUNCTION__
    (let* trait_ref = trait_ref_of_postcard ctx st in
     let* type_id = assoc_type_id_of_postcard ctx st in
     let* ty = ty_of_postcard ctx st in
     Ok ({ trait_ref; type_id; ty } : trait_type_constraint))

and trait_type_constraint_id_of_postcard (ctx : of_postcard_ctx)
    (st : postcard_state) : (trait_type_constraint_id, string) result =
  combine_error_msgs st __FUNCTION__
    (TraitTypeConstraintId.id_of_postcard ctx st)

and ty_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (ty, string) result =
  combine_error_msgs st __FUNCTION__
    (hash_consed_val_of_postcard ctx.ty_hashcons_map ty_kind_of_postcard ctx st)

and ty_kind_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (ty_kind, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 ->
         let* _0 = type_decl_ref_of_postcard ctx st in
         Ok (TAdt _0)
     | 1 ->
         let* _0 = de_bruijn_var_of_postcard type_var_id_of_postcard ctx st in
         Ok (TVar _0)
     | 2 ->
         let* _0 = literal_type_of_postcard ctx st in
         Ok (TLiteral _0)
     | 3 -> Ok TNever
     | 4 ->
         let* _0 = region_of_postcard ctx st in
         let* _1 = ty_of_postcard ctx st in
         let* _2 = ref_kind_of_postcard ctx st in
         Ok (TRef (_0, _1, _2))
     | 5 ->
         let* _0 = ty_of_postcard ctx st in
         let* _1 = ref_kind_of_postcard ctx st in
         Ok (TRawPtr (_0, _1))
     | 6 ->
         let* _0 = trait_ref_of_postcard ctx st in
         let* _1 = assoc_type_id_of_postcard ctx st in
         let* _2 = generic_args_of_postcard ctx st in
         Ok (TTraitType (_0, _1, _2))
     | 7 ->
         let* _0 = dyn_predicate_of_postcard ctx st in
         Ok (TDynTrait _0)
     | 8 ->
         let* _0 = region_binder_of_postcard fun_sig_of_postcard ctx st in
         Ok (TFnPtr _0)
     | 9 ->
         let* _0 = region_binder_of_postcard fn_ptr_of_postcard ctx st in
         Ok (TFnDef _0)
     | 10 ->
         let* _0 = ty_of_postcard ctx st in
         Ok (TPtrMetadata _0)
     | 11 ->
         let* _0 = ty_of_postcard ctx st in
         let* _1 = constant_expr_of_postcard ctx st in
         Ok (TArray (_0, _1))
     | 12 ->
         let* _0 = ty_of_postcard ctx st in
         Ok (TSlice _0)
     | 13 ->
         let* _0 = ty_of_postcard ctx st in
         let* _1 = type_pattern_of_postcard ctx st in
         Ok (TPattern (_0, _1))
     | 14 ->
         let* _0 = string_of_postcard ctx st in
         Ok (TError _0)
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and type_decl_id_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (type_decl_id, string) result =
  combine_error_msgs st __FUNCTION__ (TypeDeclId.id_of_postcard ctx st)

and type_decl_ref_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (type_decl_ref, string) result =
  combine_error_msgs st __FUNCTION__
    (let* id = type_decl_id_of_postcard ctx st in
     let* generics = box_of_postcard generic_args_of_postcard ctx st in
     let* builtin = option_of_postcard builtin_ty_of_postcard ctx st in
     Ok ({ id; generics; builtin } : type_decl_ref))

and type_param_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (type_param, string) result =
  combine_error_msgs st __FUNCTION__
    (let* index = type_var_id_of_postcard ctx st in
     let* name = string_of_postcard ctx st in
     let* variance = variance_of_postcard ctx st in
     Ok ({ index; name; variance } : type_param))

and type_pattern_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (type_pattern, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 ->
         let* _0 = constant_expr_of_postcard ctx st in
         let* _1 = constant_expr_of_postcard ctx st in
         Ok (Range (_0, _1))
     | 1 ->
         let* _0 = list_of_postcard type_pattern_of_postcard ctx st in
         Ok (OrPattern _0)
     | 2 -> Ok NotNull
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and type_var_id_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (type_var_id, string) result =
  combine_error_msgs st __FUNCTION__ (TypeVarId.id_of_postcard ctx st)

and u_int_ty_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (u_int_ty, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 -> Ok Usize
     | 1 -> Ok U8
     | 2 -> Ok U16
     | 3 -> Ok U32
     | 4 -> Ok U64
     | 5 -> Ok U128
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and unop_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (unop, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 -> Ok Not
     | 1 ->
         let* _0 = overflow_mode_of_postcard ctx st in
         Ok (Neg _0)
     | 2 ->
         let* _0 = cast_kind_of_postcard ctx st in
         Ok (Cast _0)
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and unsizing_metadata_of_postcard (ctx : of_postcard_ctx) (st : postcard_state)
    : (unsizing_metadata, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 ->
         let* _0 = constant_expr_of_postcard ctx st in
         Ok (MetaLength _0)
     | 1 ->
         let* _0 = trait_ref_of_postcard ctx st in
         let* _1 = constant_expr_of_postcard ctx st in
         Ok (MetaVTable (_0, _1))
     | 2 ->
         let* _0 = list_of_postcard field_id_of_postcard ctx st in
         Ok (MetaVTableUpcast _0)
     | 3 -> Ok MetaUnknown
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and variance_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (variance, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 -> Ok Covariant
     | 1 -> Ok Invariant
     | 2 -> Ok Contravariant
     | 3 -> Ok Bivariant
     | 4 -> Ok VaUnknown
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and variant_id_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (variant_id, string) result =
  combine_error_msgs st __FUNCTION__ (VariantId.id_of_postcard ctx st)

and with_retag_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (with_retag, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 -> Ok NoRetag
     | 1 -> Ok YesRetag
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

module Ullbc = struct
  open UllbcAst

  let rec ___ = ()

  and block_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
      (Generated_UllbcAst.block, string) result =
    combine_error_msgs st __FUNCTION__
      (let* statements = list_of_postcard statement_of_postcard ctx st in
       let* terminator = terminator_of_postcard ctx st in
       Ok ({ statements; terminator } : Generated_UllbcAst.block))

  and block_id_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
      (Generated_UllbcAst.block_id, string) result =
    combine_error_msgs st __FUNCTION__ (BlockId.id_of_postcard ctx st)

  and statement_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
      (Generated_UllbcAst.statement, string) result =
    combine_error_msgs st __FUNCTION__
      (let* span = span_of_postcard ctx st in
       let* kind = statement_kind_of_postcard ctx st in
       let* comments_before = list_of_postcard string_of_postcard ctx st in
       Ok ({ span; kind; comments_before } : Generated_UllbcAst.statement))

  and statement_kind_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
      (Generated_UllbcAst.statement_kind, string) result =
    combine_error_msgs st __FUNCTION__
      (let* __tag = int_of_postcard ctx st in
       match __tag with
       | 0 ->
           let* _0 = place_of_postcard ctx st in
           let* _1 = rvalue_of_postcard ctx st in
           Ok (Assign (_0, _1))
       | 1 ->
           let* _0 = place_of_postcard ctx st in
           let* _1 = variant_id_of_postcard ctx st in
           Ok (SetDiscriminant (_0, _1))
       | 2 ->
           let* _0 = local_id_of_postcard ctx st in
           Ok (StorageLive _0)
       | 3 ->
           let* _0 = local_id_of_postcard ctx st in
           Ok (StorageDead _0)
       | 4 ->
           let* _0 = place_of_postcard ctx st in
           Ok (PlaceMention _0)
       | 5 ->
           let* _0 = borrowck_statement_of_postcard ctx st in
           Ok (Borrowck _0)
       | 6 ->
           let* assert_ = assertion_of_postcard ctx st in
           let* on_failure = abort_kind_of_postcard ctx st in
           Ok (Assert (assert_, on_failure))
       | 7 -> Ok Nop
       | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

  and terminator_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
      (terminator, string) result =
    combine_error_msgs st __FUNCTION__
      (let* span = span_of_postcard ctx st in
       let* kind = terminator_kind_of_postcard ctx st in
       let* comments_before = list_of_postcard string_of_postcard ctx st in
       Ok ({ span; kind; comments_before } : terminator))

  and terminator_kind_of_postcard (ctx : of_postcard_ctx) (st : postcard_state)
      : (terminator_kind, string) result =
    combine_error_msgs st __FUNCTION__
      (let* __tag = int_of_postcard ctx st in
       match __tag with
       | 0 ->
           let* target = block_id_of_postcard ctx st in
           Ok (Goto target)
       | 1 ->
           let* data = switch_data_of_postcard ctx st in
           let* branches =
             index_vec_of_postcard branch_id_of_postcard block_id_of_postcard
               ctx st
           in
           Ok (Switch (data, branches))
       | 2 ->
           let* call = call_of_postcard ctx st in
           let* target = block_id_of_postcard ctx st in
           let* on_unwind = block_id_of_postcard ctx st in
           Ok (Call (call, target, on_unwind))
       | 3 ->
           let* kind = drop_kind_of_postcard ctx st in
           let* place = place_of_postcard ctx st in
           let* fn_ptr = fn_ptr_of_postcard ctx st in
           let* target = block_id_of_postcard ctx st in
           let* on_unwind = block_id_of_postcard ctx st in
           Ok (Drop (kind, place, fn_ptr, target, on_unwind))
       | 4 ->
           let* assert_ = assertion_of_postcard ctx st in
           let* target = block_id_of_postcard ctx st in
           let* on_unwind = block_id_of_postcard ctx st in
           Ok (TAssert (assert_, target, on_unwind))
       | 5 ->
           let* asm = string_of_postcard ctx st in
           let* targets = list_of_postcard block_id_of_postcard ctx st in
           let* on_unwind = block_id_of_postcard ctx st in
           Ok (InlineAsm (asm, targets, on_unwind))
       | 6 ->
           let* _0 = abort_kind_of_postcard ctx st in
           Ok (Abort _0)
       | 7 -> Ok Return
       | 8 -> Ok UnwindResume
       | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))
end

module Llbc = struct
  open LlbcAst

  let rec ___ = ()

  and block_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
      (Generated_LlbcAst.block, string) result =
    combine_error_msgs st __FUNCTION__
      (let* span = span_of_postcard ctx st in
       let* block_id = block_id_of_postcard ctx st in
       let* statements = list_of_postcard statement_of_postcard ctx st in
       Ok ({ span; block_id; statements } : Generated_LlbcAst.block))

  and block_id_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
      (Generated_LlbcAst.block_id, string) result =
    combine_error_msgs st __FUNCTION__ (BlockId.id_of_postcard ctx st)

  and statement_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
      (Generated_LlbcAst.statement, string) result =
    combine_error_msgs st __FUNCTION__
      (let* span = span_of_postcard ctx st in
       let* statement_id = statement_id_of_postcard ctx st in
       let* kind = statement_kind_of_postcard ctx st in
       let* comments_before = list_of_postcard string_of_postcard ctx st in
       Ok
         ({ span; statement_id; kind; comments_before }
           : Generated_LlbcAst.statement))

  and statement_id_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
      (statement_id, string) result =
    combine_error_msgs st __FUNCTION__ (StatementId.id_of_postcard ctx st)

  and statement_kind_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
      (Generated_LlbcAst.statement_kind, string) result =
    combine_error_msgs st __FUNCTION__
      (let* __tag = int_of_postcard ctx st in
       match __tag with
       | 0 ->
           let* _0 = place_of_postcard ctx st in
           let* _1 = rvalue_of_postcard ctx st in
           Ok (Assign (_0, _1))
       | 1 ->
           let* _0 = place_of_postcard ctx st in
           let* _1 = variant_id_of_postcard ctx st in
           Ok (SetDiscriminant (_0, _1))
       | 2 ->
           let* _0 = local_id_of_postcard ctx st in
           Ok (StorageLive _0)
       | 3 ->
           let* _0 = local_id_of_postcard ctx st in
           Ok (StorageDead _0)
       | 4 ->
           let* _0 = place_of_postcard ctx st in
           Ok (PlaceMention _0)
       | 5 ->
           let* _0 = borrowck_statement_of_postcard ctx st in
           Ok (Borrowck _0)
       | 6 ->
           let* place = place_of_postcard ctx st in
           let* fn_ptr = fn_ptr_of_postcard ctx st in
           let* kind = drop_kind_of_postcard ctx st in
           let* on_unwind = block_of_postcard ctx st in
           Ok (Drop (place, fn_ptr, kind, on_unwind))
       | 7 ->
           let* assert_ = assertion_of_postcard ctx st in
           let* on_failure = abort_kind_of_postcard ctx st in
           let* on_unwind = block_of_postcard ctx st in
           Ok (Assert (assert_, on_failure, on_unwind))
       | 8 ->
           let* asm = string_of_postcard ctx st in
           let* targets = list_of_postcard block_of_postcard ctx st in
           let* on_unwind = block_of_postcard ctx st in
           Ok (InlineAsm (asm, targets, on_unwind))
       | 9 ->
           let* call = call_of_postcard ctx st in
           let* on_unwind = block_of_postcard ctx st in
           Ok (Call (call, on_unwind))
       | 10 ->
           let* _0 = abort_kind_of_postcard ctx st in
           Ok (Abort _0)
       | 11 -> Ok Return
       | 12 -> Ok UnwindResume
       | 13 ->
           let* _0 = usize_of_postcard ctx st in
           Ok (Break _0)
       | 14 ->
           let* _0 = usize_of_postcard ctx st in
           Ok (Continue _0)
       | 15 -> Ok Nop
       | 16 ->
           let* data = switch_data_of_postcard ctx st in
           let* branches =
             index_vec_of_postcard branch_id_of_postcard block_of_postcard ctx
               st
           in
           Ok (Switch (data, branches))
       | 17 ->
           let* _0 = block_of_postcard ctx st in
           Ok (Loop _0)
       | 18 ->
           let* _0 = string_of_postcard ctx st in
           Ok (Error _0)
       | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))
end

let rec ___ = ()

and alignment_modifier_of_postcard (ctx : of_postcard_ctx) (st : postcard_state)
    : (alignment_modifier, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 ->
         let* _0 = u64_of_postcard ctx st in
         Ok (Align _0)
     | 1 ->
         let* _0 = u64_of_postcard ctx st in
         Ok (Pack _0)
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and assoc_item_id_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (assoc_item_id, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 ->
         let* _0 = assoc_type_id_of_postcard ctx st in
         Ok (AssocIdType _0)
     | 1 ->
         let* _0 = trait_method_id_of_postcard ctx st in
         Ok (AssocIdMethod _0)
     | 2 ->
         let* _0 = assoc_const_id_of_postcard ctx st in
         Ok (AssocIdConst _0)
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and assoc_item_names_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (assoc_item_names, string) result =
  combine_error_msgs st __FUNCTION__
    (let* types =
       index_vec_of_postcard assoc_type_id_of_postcard
         trait_item_name_of_postcard ctx st
     in
     let* methods =
       index_vec_of_postcard trait_method_id_of_postcard
         trait_item_name_of_postcard ctx st
     in
     let* consts =
       index_vec_of_postcard assoc_const_id_of_postcard
         trait_item_name_of_postcard ctx st
     in
     Ok ({ types; methods; consts } : assoc_item_names))

and attr_info_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (attr_info, string) result =
  combine_error_msgs st __FUNCTION__
    (let* attributes = list_of_postcard attribute_of_postcard ctx st in
     let* inline = option_of_postcard inline_attr_of_postcard ctx st in
     let* rename = option_of_postcard string_of_postcard ctx st in
     let* public = bool_of_postcard ctx st in
     Ok ({ attributes; inline; rename; public } : attr_info))

and attribute_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (attribute, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 -> Ok AttrOpaque
     | 1 -> Ok AttrExclude
     | 2 ->
         let* _0 = string_of_postcard ctx st in
         Ok (AttrRename _0)
     | 3 ->
         let* _0 = string_of_postcard ctx st in
         Ok (AttrVariantsPrefix _0)
     | 4 ->
         let* _0 = string_of_postcard ctx st in
         Ok (AttrVariantsSuffix _0)
     | 5 -> Ok AttrTransparent
     | 6 ->
         let* kind = string_of_postcard ctx st in
         let* target = maybe_assoc_item_id_of_postcard ctx st in
         Ok (AttrIsContract (kind, target))
     | 7 ->
         let* kind = string_of_postcard ctx st in
         let* contract = fun_decl_id_of_postcard ctx st in
         Ok (AttrHasContract (kind, contract))
     | 8 ->
         let* _0 = string_of_postcard ctx st in
         Ok (AttrDocComment _0)
     | 9 ->
         let* _0 = rustc_attribute_kind_of_postcard ctx st in
         Ok (AttrBuiltin _0)
     | 10 ->
         let* _0 = raw_attribute_of_postcard ctx st in
         Ok (AttrUnknown _0)
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and rustc_attribute_kind_of_postcard (ctx : of_postcard_ctx)
    (st : postcard_state) : (rustc_attribute_kind, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 -> Ok RustcAttributeKindAutomaticallyDerived
     | 1 -> Ok RustcAttributeKindCold
     | 2 ->
         let* deprecation = rustc_deprecation_of_postcard ctx st in
         let* span = span_of_postcard ctx st in
         Ok (RustcAttributeKindDeprecated (deprecation, span))
     | 3 -> Ok RustcAttributeKindFundamental
     | 4 ->
         let* span = span_of_postcard ctx st in
         let* reason = option_of_postcard string_of_postcard ctx st in
         Ok (RustcAttributeKindIgnore (span, reason))
     | 5 ->
         let* _0 = rustc_inline_attr_of_postcard ctx st in
         let* _1 = span_of_postcard ctx st in
         Ok (RustcAttributeKindInline (_0, _1))
     | 6 ->
         let* _0 = span_of_postcard ctx st in
         Ok (RustcAttributeKindMayDangle _0)
     | 7 ->
         let* _0 = span_of_postcard ctx st in
         Ok (RustcAttributeKindNaked _0)
     | 8 -> Ok RustcAttributeKindNoLink
     | 9 ->
         let* _0 = span_of_postcard ctx st in
         Ok (RustcAttributeKindNoMangle _0)
     | 10 ->
         let* _0 = span_of_postcard ctx st in
         Ok (RustcAttributeKindNonExhaustive _0)
     | 11 ->
         let* _0 = rustc_optimize_attr_of_postcard ctx st in
         let* _1 = span_of_postcard ctx st in
         Ok (RustcAttributeKindOptimize (_0, _1))
     | 12 ->
         let* align = u64_of_postcard ctx st in
         let* span = span_of_postcard ctx st in
         Ok (RustcAttributeKindRustcAlign (align, span))
     | 13 -> Ok RustcAttributeKindRustcIntrinsic
     | 14 -> Ok RustcAttributeKindRustcTestEntrypointMarker
     | 15 ->
         let* reason = option_of_postcard string_of_postcard ctx st in
         Ok (RustcAttributeKindShouldPanic reason)
     | 16 ->
         let* features =
           list_of_postcard
             (pair_of_postcard string_of_postcard span_of_postcard)
             ctx st
         in
         let* attr_span = span_of_postcard ctx st in
         let* was_forced = bool_of_postcard ctx st in
         Ok (RustcAttributeKindTargetFeature (features, attr_span, was_forced))
     | 17 ->
         let* _0 = span_of_postcard ctx st in
         Ok (RustcAttributeKindTrackCaller _0)
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and body_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (body, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 ->
         let* _0 =
           gexpr_body_of_postcard
             (index_vec_of_postcard Ullbc.block_id_of_postcard
                Ullbc.block_of_postcard)
             ctx st
         in
         Ok (UnstructuredBody _0)
     | 1 ->
         let* _0 = gexpr_body_of_postcard Llbc.block_of_postcard ctx st in
         Ok (StructuredBody _0)
     | 2 ->
         let* _0 =
           index_map_of_postcard string_of_postcard fun_decl_ref_of_postcard
             int_of_postcard ctx st
         in
         Ok (TargetDispatchBody _0)
     | 3 ->
         let* _0 = string_of_postcard ctx st in
         Ok (ExternBody _0)
     | 4 ->
         let* name = string_of_postcard ctx st in
         let* arg_names =
           list_of_postcard (option_of_postcard string_of_postcard) ctx st
         in
         Ok (IntrinsicBody (name, arg_names))
     | 5 -> Ok OpaqueBody
     | 6 -> Ok MissingBody
     | 7 ->
         let* _0 = error_of_postcard ctx st in
         Ok (ErrorBody _0)
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and cli_options_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (cli_options, string) result =
  combine_error_msgs st __FUNCTION__
    (let* ullbc = bool_of_postcard ctx st in
     let* precise_drops = bool_of_postcard ctx st in
     let* mir = option_of_postcard mir_level_of_postcard ctx st in
     let* rustc_args = list_of_postcard string_of_postcard ctx st in
     let* targets = list_of_postcard string_of_postcard ctx st in
     let* sysroot = option_of_postcard string_of_postcard ctx st in
     let* monomorphize = bool_of_postcard ctx st in
     let* monomorphize_mut =
       option_of_postcard monomorphize_mut_of_postcard ctx st
     in
     let* start_from = list_of_postcard string_of_postcard ctx st in
     let* start_from_if_exists = list_of_postcard string_of_postcard ctx st in
     let* start_from_attribute = list_of_postcard string_of_postcard ctx st in
     let* start_from_pub = bool_of_postcard ctx st in
     let* included = list_of_postcard string_of_postcard ctx st in
     let* opaque = list_of_postcard string_of_postcard ctx st in
     let* exclude = list_of_postcard string_of_postcard ctx st in
     let* extract_opaque_bodies = bool_of_postcard ctx st in
     let* translate_all_methods = bool_of_postcard ctx st in
     let* duplicate_defaulted_methods = bool_of_postcard ctx st in
     let* lift_associated_types = list_of_postcard string_of_postcard ctx st in
     let* hide_marker_traits = bool_of_postcard ctx st in
     let* hide_allocator = bool_of_postcard ctx st in
     let* remove_unused_clauses = bool_of_postcard ctx st in
     let* remove_unused_self_clauses = bool_of_postcard ctx st in
     let* remove_adt_clauses = bool_of_postcard ctx st in
     let* desugar_drops = bool_of_postcard ctx st in
     let* ops_to_function_calls = bool_of_postcard ctx st in
     let* index_to_function_calls = bool_of_postcard ctx st in
     let* treat_box_as_builtin = bool_of_postcard ctx st in
     let* no_gen_tuple_structs = bool_of_postcard ctx st in
     let* raw_consts = bool_of_postcard ctx st in
     let* consts = option_of_postcard const_handling_of_postcard ctx st in
     let* unsized_strings = bool_of_postcard ctx st in
     let* reconstruct_fallible_operations = bool_of_postcard ctx st in
     let* reconstruct_asserts = bool_of_postcard ctx st in
     let* reconstruct_matches = bool_of_postcard ctx st in
     let* deallocate_all_locals = bool_of_postcard ctx st in
     let* unbind_item_vars = bool_of_postcard ctx st in
     let* print_original_ullbc = bool_of_postcard ctx st in
     let* print_ullbc = bool_of_postcard ctx st in
     let* print_built_llbc = bool_of_postcard ctx st in
     let* print_llbc = bool_of_postcard ctx st in
     let* dest_dir = option_of_postcard path_buf_of_postcard ctx st in
     let* dest_file = option_of_postcard path_buf_of_postcard ctx st in
     let* no_dedup_serialized_ast = bool_of_postcard ctx st in
     let* format =
       option_of_postcard serialization_format_arg_of_postcard ctx st
     in
     let* no_serialize = bool_of_postcard ctx st in
     let* skip_borrowck = bool_of_postcard ctx st in
     let* no_typecheck = bool_of_postcard ctx st in
     let* no_normalize = bool_of_postcard ctx st in
     let* no_reorder_decls = bool_of_postcard ctx st in
     let* abort_on_error = bool_of_postcard ctx st in
     let* error_on_warnings = bool_of_postcard ctx st in
     let* preset = option_of_postcard preset_of_postcard ctx st in
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
          no_gen_tuple_structs;
          raw_consts;
          consts;
          unsized_strings;
          reconstruct_fallible_operations;
          reconstruct_asserts;
          reconstruct_matches;
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
         : cli_options))

and closure_info_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (closure_info, string) result =
  combine_error_msgs st __FUNCTION__
    (let* kind = closure_kind_of_postcard ctx st in
     let* fn_once_impl =
       region_binder_of_postcard trait_impl_ref_of_postcard ctx st
     in
     let* fn_mut_impl =
       option_of_postcard
         (region_binder_of_postcard trait_impl_ref_of_postcard)
         ctx st
     in
     let* fn_impl =
       option_of_postcard
         (region_binder_of_postcard trait_impl_ref_of_postcard)
         ctx st
     in
     let* signature = region_binder_of_postcard fun_sig_of_postcard ctx st in
     Ok ({ kind; fn_once_impl; fn_mut_impl; fn_impl; signature } : closure_info))

and closure_kind_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (closure_kind, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 -> Ok Fn
     | 1 -> Ok FnMut
     | 2 -> Ok FnOnce
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and const_handling_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (const_handling, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 -> Ok Initializers
     | 1 -> Ok Values
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and declaration_group_of_postcard (ctx : of_postcard_ctx) (st : postcard_state)
    : (declaration_group, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 ->
         let* _0 =
           g_declaration_group_of_postcard type_decl_id_of_postcard ctx st
         in
         Ok (TypeGroup _0)
     | 1 ->
         let* _0 =
           g_declaration_group_of_postcard fun_decl_id_of_postcard ctx st
         in
         Ok (FunGroup _0)
     | 2 ->
         let* _0 =
           g_declaration_group_of_postcard global_decl_id_of_postcard ctx st
         in
         Ok (GlobalGroup _0)
     | 3 ->
         let* _0 =
           g_declaration_group_of_postcard trait_decl_id_of_postcard ctx st
         in
         Ok (TraitDeclGroup _0)
     | 4 ->
         let* _0 =
           g_declaration_group_of_postcard trait_impl_id_of_postcard ctx st
         in
         Ok (TraitImplGroup _0)
     | 5 ->
         let* _0 = g_declaration_group_of_postcard item_id_of_postcard ctx st in
         Ok (MixedGroup _0)
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and rustc_deprecated_since_of_postcard (ctx : of_postcard_ctx)
    (st : postcard_state) : (rustc_deprecated_since, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 ->
         let* _0 = rustc_rustc_version_of_postcard ctx st in
         Ok (RustcDeprecatedSinceRustcVersion _0)
     | 1 -> Ok RustcDeprecatedSinceFuture
     | 2 ->
         let* _0 = string_of_postcard ctx st in
         Ok (RustcDeprecatedSinceNonStandard _0)
     | 3 -> Ok RustcDeprecatedSinceUnspecified
     | 4 -> Ok RustcDeprecatedSinceErr
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and rustc_deprecation_of_postcard (ctx : of_postcard_ctx) (st : postcard_state)
    : (rustc_deprecation, string) result =
  combine_error_msgs st __FUNCTION__
    (let* since = rustc_deprecated_since_of_postcard ctx st in
     let* note = option_of_postcard rustc_ident_of_postcard ctx st in
     let* suggestion = option_of_postcard string_of_postcard ctx st in
     Ok ({ since; note; suggestion } : rustc_deprecation))

and discriminator_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (discriminator, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 ->
         let* _0 = variant_id_of_postcard ctx st in
         Ok (Known _0)
     | 1 -> Ok Invalid
     | 2 ->
         let* offset = offset_expr_of_postcard ctx st in
         let* int_ty = integer_type_of_postcard ctx st in
         let* children =
           list_of_postcard
             (pair_of_postcard
                (range_inclusive_of_postcard scalar_value_of_postcard)
                discriminator_of_postcard)
             ctx st
         in
         let* fallback = box_of_postcard discriminator_of_postcard ctx st in
         Ok (Branch (offset, int_ty, children, fallback))
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and error_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (error, string) result =
  combine_error_msgs st __FUNCTION__
    (let* span = span_of_postcard ctx st in
     let* msg = string_of_postcard ctx st in
     Ok ({ span; msg } : error))

and exact_size_expr_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (exact_size_expr, string) result =
  combine_error_msgs st __FUNCTION__
    (hash_consed_val_of_postcard ctx.exact_size_expr_hashcons_map
       exact_size_expr_kind_of_postcard ctx st)

and exact_size_expr_kind_of_postcard (ctx : of_postcard_ctx)
    (st : postcard_state) : (exact_size_expr_kind, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 ->
         let* _0 = constant_expr_of_postcard ctx st in
         Ok (ExactSizeExprConstant _0)
     | 1 ->
         let* _0 = metadata_value_of_postcard ctx st in
         Ok (ExactSizeExprFromMetadata _0)
     | 2 ->
         let* _0 = list_of_postcard exact_size_expr_of_postcard ctx st in
         Ok (ExactSizeExprMax _0)
     | 3 ->
         let* _0 = list_of_postcard exact_size_expr_of_postcard ctx st in
         Ok (ExactSizeExprMin _0)
     | 4 ->
         let* _0 = exact_size_expr_of_postcard ctx st in
         let* _1 = exact_size_expr_of_postcard ctx st in
         Ok (ExactSizeExprPlus (_0, _1))
     | 5 ->
         let* _0 = exact_size_expr_of_postcard ctx st in
         let* _1 = constant_expr_of_postcard ctx st in
         Ok (ExactSizeExprScale (_0, _1))
     | 6 ->
         let* base = exact_size_expr_of_postcard ctx st in
         let* target_align = exact_size_expr_of_postcard ctx st in
         Ok (ExactSizeExprAlignTo (base, target_align))
     | 7 ->
         let* ty = ty_of_postcard ctx st in
         let* then_size = exact_size_expr_of_postcard ctx st in
         let* else_size = exact_size_expr_of_postcard ctx st in
         Ok (ExactSizeExprIfInhabited (ty, then_size, else_size))
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and field_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (field, string) result =
  combine_error_msgs st __FUNCTION__
    (let* span = span_of_postcard ctx st in
     let* attr_info = attr_info_of_postcard ctx st in
     let* field_name = string_of_postcard ctx st in
     let* is_positional = bool_of_postcard ctx st in
     let* field_ty = ty_of_postcard ctx st in
     Ok ({ span; attr_info; field_name; is_positional; field_ty } : field))

and file_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (file, string) result =
  combine_error_msgs st __FUNCTION__
    (let* id = FileId.id_of_postcard ctx st in
     let* name = file_name_of_postcard ctx st in
     let* crate_name = string_of_postcard ctx st in
     let* contents = option_of_postcard string_of_postcard ctx st in
     let file : file = { name; crate_name; contents } in
     FileTbl.add ctx.id_to_file_map id file;
     Ok file)

and file_name_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (file_name, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 ->
         let* _0 = path_buf_of_postcard ctx st in
         Ok (Virtual _0)
     | 1 ->
         let* _0 = path_buf_of_postcard ctx st in
         Ok (Local _0)
     | 2 ->
         let* _0 = string_of_postcard ctx st in
         Ok (NotReal _0)
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and fun_decl_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (fun_decl, string) result =
  combine_error_msgs st __FUNCTION__
    (let* def_id = fun_decl_id_of_postcard ctx st in
     let* item_meta = item_meta_of_postcard ctx st in
     let* generics = generic_params_of_postcard ctx st in
     let* signature = box_of_postcard fun_sig_of_postcard ctx st in
     let* src = fun_source_of_postcard ctx st in
     let* body = body_of_postcard ctx st in
     Ok ({ def_id; item_meta; generics; signature; src; body } : fun_decl))

and fun_source_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (fun_source, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 -> Ok NormalFun
     | 1 -> Ok AdtConstructorFun
     | 2 ->
         let* trait_ref = trait_decl_ref_of_postcard ctx st in
         let* item_id = trait_method_id_of_postcard ctx st in
         Ok (TraitDefaultFun (trait_ref, item_id))
     | 3 ->
         let* impl_ref = trait_impl_ref_of_postcard ctx st in
         let* trait_ref = trait_decl_ref_of_postcard ctx st in
         let* item_id = trait_method_id_of_postcard ctx st in
         let* reuses_default = bool_of_postcard ctx st in
         Ok (TraitImplFun (impl_ref, trait_ref, item_id, reuses_default))
     | 4 -> Ok VTableShimFun
     | 5 ->
         let* _0 = global_decl_ref_of_postcard ctx st in
         Ok (GlobalInitializerFun _0)
     | 6 ->
         let* dispatcher = fun_decl_ref_of_postcard ctx st in
         Ok (TargetDependentFun dispatcher)
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and g_declaration_group_of_postcard :
    'a0.
    (of_postcard_ctx -> postcard_state -> ('a0, string) result) ->
    of_postcard_ctx ->
    postcard_state ->
    ('a0 g_declaration_group, string) result =
 fun arg0_of_postcard ctx st ->
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 ->
         let* _0 = arg0_of_postcard ctx st in
         Ok (NonRecGroup _0)
     | 1 ->
         let* _0 = list_of_postcard arg0_of_postcard ctx st in
         Ok (RecGroup _0)
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and gexpr_body_of_postcard :
    'a0.
    (of_postcard_ctx -> postcard_state -> ('a0, string) result) ->
    of_postcard_ctx ->
    postcard_state ->
    ('a0 gexpr_body, string) result =
 fun arg0_of_postcard ctx st ->
  combine_error_msgs st __FUNCTION__
    (let* span = span_of_postcard ctx st in
     let* bound_body_regions = usize_of_postcard ctx st in
     let* locals = locals_of_postcard ctx st in
     let* body = arg0_of_postcard ctx st in
     let* _ =
       list_of_postcard
         (pair_of_postcard u32_of_postcard
            (list_of_postcard string_of_postcard))
         ctx st
     in
     Ok ({ span; bound_body_regions; locals; body } : _ gexpr_body))

and global_decl_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (global_decl, string) result =
  combine_error_msgs st __FUNCTION__
    (let* def_id = global_decl_id_of_postcard ctx st in
     let* item_meta = item_meta_of_postcard ctx st in
     let* generics = generic_params_of_postcard ctx st in
     let* ty = ty_of_postcard ctx st in
     let* src = global_source_of_postcard ctx st in
     let* global_kind = global_kind_of_postcard ctx st in
     let* value = constant_expr_of_postcard ctx st in
     Ok
       ({ def_id; item_meta; generics; ty; src; global_kind; value }
         : global_decl))

and global_kind_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (global_kind, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 -> Ok Static
     | 1 -> Ok ThreadLocal
     | 2 -> Ok NamedConst
     | 3 -> Ok AnonConst
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and global_source_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (global_source, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 -> Ok NormalGlobal
     | 1 ->
         let* trait_ref = trait_decl_ref_of_postcard ctx st in
         let* item_id = assoc_const_id_of_postcard ctx st in
         Ok (TraitDefaultGlobal (trait_ref, item_id))
     | 2 ->
         let* impl_ref = trait_impl_ref_of_postcard ctx st in
         let* trait_ref = trait_decl_ref_of_postcard ctx st in
         let* item_id = assoc_const_id_of_postcard ctx st in
         let* reuses_default = bool_of_postcard ctx st in
         Ok (TraitImplGlobal (impl_ref, trait_ref, item_id, reuses_default))
     | 3 ->
         let* impl_ref = option_of_postcard trait_impl_ref_of_postcard ctx st in
         Ok (VTableInstanceGlobal impl_ref)
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and rustc_ident_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (rustc_ident, string) result =
  combine_error_msgs st __FUNCTION__
    (let* name = string_of_postcard ctx st in
     let* span = span_of_postcard ctx st in
     Ok ({ name; span } : rustc_ident))

and index_map_of_postcard :
    'a0 'a1 'a2.
    (of_postcard_ctx -> postcard_state -> ('a0, string) result) ->
    (of_postcard_ctx -> postcard_state -> ('a1, string) result) ->
    (of_postcard_ctx -> postcard_state -> ('a2, string) result) ->
    of_postcard_ctx ->
    postcard_state ->
    (('a0 * 'a1) list, string) result =
 fun arg0_of_postcard arg1_of_postcard arg2_of_postcard ctx st ->
  combine_error_msgs st __FUNCTION__
    (list_of_postcard
       (key_value_pair_of_postcard arg0_of_postcard arg1_of_postcard)
       ctx st)

and inline_attr_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (inline_attr, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 -> Ok Hint
     | 1 -> Ok Never
     | 2 -> Ok Always
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and rustc_inline_attr_of_postcard (ctx : of_postcard_ctx) (st : postcard_state)
    : (rustc_inline_attr, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 -> Ok RustcInlineAttrNone
     | 1 -> Ok RustcInlineAttrHint
     | 2 -> Ok RustcInlineAttrAlways
     | 3 -> Ok RustcInlineAttrNever
     | 4 ->
         let* attr_span = span_of_postcard ctx st in
         let* reason = option_of_postcard string_of_postcard ctx st in
         Ok (RustcInlineAttrForce (attr_span, reason))
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and integer_type_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (integer_type, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 ->
         let* _0 = int_ty_of_postcard ctx st in
         Ok (Signed _0)
     | 1 ->
         let* _0 = u_int_ty_of_postcard ctx st in
         Ok (Unsigned _0)
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and item_id_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (item_id, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 ->
         let* _0 = type_decl_id_of_postcard ctx st in
         Ok (IdType _0)
     | 1 ->
         let* _0 = trait_decl_id_of_postcard ctx st in
         Ok (IdTraitDecl _0)
     | 2 ->
         let* _0 = trait_impl_id_of_postcard ctx st in
         Ok (IdTraitImpl _0)
     | 3 ->
         let* _0 = fun_decl_id_of_postcard ctx st in
         Ok (IdFun _0)
     | 4 ->
         let* _0 = global_decl_id_of_postcard ctx st in
         Ok (IdGlobal _0)
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and item_meta_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (item_meta, string) result =
  combine_error_msgs st __FUNCTION__
    (let* name = name_of_postcard ctx st in
     let* span = span_of_postcard ctx st in
     let* source_text = option_of_postcard string_of_postcard ctx st in
     let* attr_info = attr_info_of_postcard ctx st in
     let* is_local = bool_of_postcard ctx st in
     let* opacity = item_opacity_of_postcard ctx st in
     let* lang_item = option_of_postcard rustc_lang_item_of_postcard ctx st in
     let* diagnostic_item = option_of_postcard string_of_postcard ctx st in
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
         : item_meta))

and item_opacity_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (item_opacity, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 -> Ok Transparent
     | 1 -> Ok Foreign
     | 2 -> Ok ItemOpaque
     | 3 -> Ok Invisible
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and rustc_lang_item_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (rustc_lang_item, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 -> Ok RustcLangItemSized
     | 1 -> Ok RustcLangItemMetaSized
     | 2 -> Ok RustcLangItemPointeeSized
     | 3 -> Ok RustcLangItemUnsize
     | 4 -> Ok RustcLangItemAlignOf
     | 5 -> Ok RustcLangItemSizeOf
     | 6 -> Ok RustcLangItemOffsetOf
     | 7 -> Ok RustcLangItemStructuralPeq
     | 8 -> Ok RustcLangItemCopy
     | 9 -> Ok RustcLangItemClone
     | 10 -> Ok RustcLangItemCloneFn
     | 11 -> Ok RustcLangItemUseCloned
     | 12 -> Ok RustcLangItemTrivialClone
     | 13 -> Ok RustcLangItemSync
     | 14 -> Ok RustcLangItemDiscriminantKind
     | 15 -> Ok RustcLangItemDiscriminant
     | 16 -> Ok RustcLangItemPointeeTrait
     | 17 -> Ok RustcLangItemMetadata
     | 18 -> Ok RustcLangItemDynMetadata
     | 19 -> Ok RustcLangItemFreeze
     | 20 -> Ok RustcLangItemUnsafeUnpin
     | 21 -> Ok RustcLangItemFnPtrTrait
     | 22 -> Ok RustcLangItemFnPtrAddr
     | 23 -> Ok RustcLangItemDrop
     | 24 -> Ok RustcLangItemDestruct
     | 25 -> Ok RustcLangItemAsyncDrop
     | 26 -> Ok RustcLangItemAsyncDropInPlace
     | 27 -> Ok RustcLangItemCoerceUnsized
     | 28 -> Ok RustcLangItemDispatchFromDyn
     | 29 -> Ok RustcLangItemTryAsDyn
     | 30 -> Ok RustcLangItemTransmuteOpts
     | 31 -> Ok RustcLangItemTransmuteTrait
     | 32 -> Ok RustcLangItemAdd
     | 33 -> Ok RustcLangItemSub
     | 34 -> Ok RustcLangItemMul
     | 35 -> Ok RustcLangItemDiv
     | 36 -> Ok RustcLangItemRem
     | 37 -> Ok RustcLangItemNeg
     | 38 -> Ok RustcLangItemNot
     | 39 -> Ok RustcLangItemBitXor
     | 40 -> Ok RustcLangItemBitAnd
     | 41 -> Ok RustcLangItemBitOr
     | 42 -> Ok RustcLangItemShl
     | 43 -> Ok RustcLangItemShr
     | 44 -> Ok RustcLangItemAddAssign
     | 45 -> Ok RustcLangItemSubAssign
     | 46 -> Ok RustcLangItemMulAssign
     | 47 -> Ok RustcLangItemDivAssign
     | 48 -> Ok RustcLangItemRemAssign
     | 49 -> Ok RustcLangItemBitXorAssign
     | 50 -> Ok RustcLangItemBitAndAssign
     | 51 -> Ok RustcLangItemBitOrAssign
     | 52 -> Ok RustcLangItemShlAssign
     | 53 -> Ok RustcLangItemShrAssign
     | 54 -> Ok RustcLangItemIndex
     | 55 -> Ok RustcLangItemIndexMut
     | 56 -> Ok RustcLangItemUnsafeCell
     | 57 -> Ok RustcLangItemCovariantUnsafeCell
     | 58 -> Ok RustcLangItemUnsafePinned
     | 59 -> Ok RustcLangItemVaArgSafe
     | 60 -> Ok RustcLangItemVaList
     | 61 -> Ok RustcLangItemComplex
     | 62 -> Ok RustcLangItemDeref
     | 63 -> Ok RustcLangItemDerefMut
     | 64 -> Ok RustcLangItemDerefPure
     | 65 -> Ok RustcLangItemDerefTarget
     | 66 -> Ok RustcLangItemReceiver
     | 67 -> Ok RustcLangItemReceiverTarget
     | 68 -> Ok RustcLangItemLegacyReceiver
     | 69 -> Ok RustcLangItemFn
     | 70 -> Ok RustcLangItemFnMut
     | 71 -> Ok RustcLangItemFnOnce
     | 72 -> Ok RustcLangItemAsyncFn
     | 73 -> Ok RustcLangItemAsyncFnMut
     | 74 -> Ok RustcLangItemAsyncFnOnce
     | 75 -> Ok RustcLangItemAsyncFnOnceOutput
     | 76 -> Ok RustcLangItemCallOnceFuture
     | 77 -> Ok RustcLangItemCallRefFuture
     | 78 -> Ok RustcLangItemAsyncFnKindHelper
     | 79 -> Ok RustcLangItemAsyncFnKindUpvars
     | 80 -> Ok RustcLangItemFnOnceOutput
     | 81 -> Ok RustcLangItemIterator
     | 82 -> Ok RustcLangItemFusedIterator
     | 83 -> Ok RustcLangItemFuture
     | 84 -> Ok RustcLangItemFutureOutput
     | 85 -> Ok RustcLangItemAsyncIterator
     | 86 -> Ok RustcLangItemCoroutineState
     | 87 -> Ok RustcLangItemCoroutine
     | 88 -> Ok RustcLangItemCoroutineReturn
     | 89 -> Ok RustcLangItemCoroutineYield
     | 90 -> Ok RustcLangItemCoroutineResume
     | 91 -> Ok RustcLangItemUnpin
     | 92 -> Ok RustcLangItemPin
     | 93 -> Ok RustcLangItemOrderingEnum
     | 94 -> Ok RustcLangItemPartialEq
     | 95 -> Ok RustcLangItemPartialOrd
     | 96 -> Ok RustcLangItemCVoid
     | 97 -> Ok RustcLangItemType
     | 98 -> Ok RustcLangItemTypeGeneric
     | 99 -> Ok RustcLangItemTypeId
     | 100 -> Ok RustcLangItemPanic
     | 101 -> Ok RustcLangItemPanicNounwind
     | 102 -> Ok RustcLangItemPanicFmt
     | 103 -> Ok RustcLangItemPanicDisplay
     | 104 -> Ok RustcLangItemConstPanicFmt
     | 105 -> Ok RustcLangItemPanicBoundsCheck
     | 106 -> Ok RustcLangItemPanicMisalignedPointerDereference
     | 107 -> Ok RustcLangItemPanicInfo
     | 108 -> Ok RustcLangItemPanicLocation
     | 109 -> Ok RustcLangItemPanicImpl
     | 110 -> Ok RustcLangItemPanicCannotUnwind
     | 111 -> Ok RustcLangItemPanicInCleanup
     | 112 -> Ok RustcLangItemPanicAddOverflow
     | 113 -> Ok RustcLangItemPanicSubOverflow
     | 114 -> Ok RustcLangItemPanicMulOverflow
     | 115 -> Ok RustcLangItemPanicDivOverflow
     | 116 -> Ok RustcLangItemPanicRemOverflow
     | 117 -> Ok RustcLangItemPanicNegOverflow
     | 118 -> Ok RustcLangItemPanicShrOverflow
     | 119 -> Ok RustcLangItemPanicShlOverflow
     | 120 -> Ok RustcLangItemPanicDivZero
     | 121 -> Ok RustcLangItemPanicRemZero
     | 122 -> Ok RustcLangItemPanicCoroutineResumed
     | 123 -> Ok RustcLangItemPanicAsyncFnResumed
     | 124 -> Ok RustcLangItemPanicAsyncGenFnResumed
     | 125 -> Ok RustcLangItemPanicGenFnNone
     | 126 -> Ok RustcLangItemPanicCoroutineResumedPanic
     | 127 -> Ok RustcLangItemPanicAsyncFnResumedPanic
     | 128 -> Ok RustcLangItemPanicAsyncGenFnResumedPanic
     | 129 -> Ok RustcLangItemPanicGenFnNonePanic
     | 130 -> Ok RustcLangItemPanicNullPointerDereference
     | 131 -> Ok RustcLangItemPanicNullReferenceConstructed
     | 132 -> Ok RustcLangItemPanicInvalidEnumConstruction
     | 133 -> Ok RustcLangItemPanicCoroutineResumedDrop
     | 134 -> Ok RustcLangItemPanicAsyncFnResumedDrop
     | 135 -> Ok RustcLangItemPanicAsyncGenFnResumedDrop
     | 136 -> Ok RustcLangItemPanicGenFnNoneDrop
     | 137 -> Ok RustcLangItemBeginPanic
     | 138 -> Ok RustcLangItemFormatArgument
     | 139 -> Ok RustcLangItemFormatArguments
     | 140 -> Ok RustcLangItemDropGlue
     | 141 -> Ok RustcLangItemAllocLayout
     | 142 -> Ok RustcLangItemStart
     | 143 -> Ok RustcLangItemEhPersonality
     | 144 -> Ok RustcLangItemCompilerMove
     | 145 -> Ok RustcLangItemCompilerCopy
     | 146 -> Ok RustcLangItemOwnedBox
     | 147 -> Ok RustcLangItemGlobalAlloc
     | 148 -> Ok RustcLangItemPhantomData
     | 149 -> Ok RustcLangItemManuallyDrop
     | 150 -> Ok RustcLangItemMaybeDangling
     | 151 -> Ok RustcLangItemBikeshedGuaranteedNoDrop
     | 152 -> Ok RustcLangItemMaybeUninit
     | 153 -> Ok RustcLangItemTermination
     | 154 -> Ok RustcLangItemTry
     | 155 -> Ok RustcLangItemTuple
     | 156 -> Ok RustcLangItemSliceLen
     | 157 -> Ok RustcLangItemTryTraitFromResidual
     | 158 -> Ok RustcLangItemTryTraitFromOutput
     | 159 -> Ok RustcLangItemTryTraitBranch
     | 160 -> Ok RustcLangItemTryTraitFromYeet
     | 161 -> Ok RustcLangItemResidualIntoTryType
     | 162 -> Ok RustcLangItemCoercePointeeValidated
     | 163 -> Ok RustcLangItemConstParamTy
     | 164 -> Ok RustcLangItemPoll
     | 165 -> Ok RustcLangItemPollReady
     | 166 -> Ok RustcLangItemPollPending
     | 167 -> Ok RustcLangItemAsyncGenReady
     | 168 -> Ok RustcLangItemAsyncGenPending
     | 169 -> Ok RustcLangItemAsyncGenFinished
     | 170 -> Ok RustcLangItemResumeTy
     | 171 -> Ok RustcLangItemGetContext
     | 172 -> Ok RustcLangItemContext
     | 173 -> Ok RustcLangItemFuturePoll
     | 174 -> Ok RustcLangItemAsyncIteratorPollNext
     | 175 -> Ok RustcLangItemIntoAsyncIterIntoIter
     | 176 -> Ok RustcLangItemOption
     | 177 -> Ok RustcLangItemOptionSome
     | 178 -> Ok RustcLangItemOptionNone
     | 179 -> Ok RustcLangItemResultOk
     | 180 -> Ok RustcLangItemResultErr
     | 181 -> Ok RustcLangItemControlFlowContinue
     | 182 -> Ok RustcLangItemControlFlowBreak
     | 183 -> Ok RustcLangItemIntoFutureIntoFuture
     | 184 -> Ok RustcLangItemIntoIterIntoIter
     | 185 -> Ok RustcLangItemIteratorNext
     | 186 -> Ok RustcLangItemPinNewUnchecked
     | 187 -> Ok RustcLangItemRangeFrom
     | 188 -> Ok RustcLangItemRangeFull
     | 189 -> Ok RustcLangItemRangeInclusiveStruct
     | 190 -> Ok RustcLangItemRangeInclusiveNew
     | 191 -> Ok RustcLangItemRange
     | 192 -> Ok RustcLangItemRangeToInclusive
     | 193 -> Ok RustcLangItemRangeTo
     | 194 -> Ok RustcLangItemRangeMax
     | 195 -> Ok RustcLangItemRangeMin
     | 196 -> Ok RustcLangItemRangeSub
     | 197 -> Ok RustcLangItemRangeFromCopy
     | 198 -> Ok RustcLangItemRangeCopy
     | 199 -> Ok RustcLangItemRangeInclusiveCopy
     | 200 -> Ok RustcLangItemRangeToInclusiveCopy
     | 201 -> Ok RustcLangItemString
     | 202 -> Ok RustcLangItemCStr
     | 203 -> Ok RustcLangItemContractBuildCheckEnsures
     | 204 -> Ok RustcLangItemContractCheckRequires
     | 205 -> Ok RustcLangItemDefaultTrait4
     | 206 -> Ok RustcLangItemDefaultTrait3
     | 207 -> Ok RustcLangItemDefaultTrait2
     | 208 -> Ok RustcLangItemDefaultTrait1
     | 209 -> Ok RustcLangItemContractCheckEnsures
     | 210 -> Ok RustcLangItemReborrow
     | 211 -> Ok RustcLangItemCoerceShared
     | 212 -> Ok RustcLangItemFieldRepresentingType
     | 213 -> Ok RustcLangItemField
     | 214 -> Ok RustcLangItemFieldBase
     | 215 -> Ok RustcLangItemFieldType
     | 216 -> Ok RustcLangItemFieldOffset
     | 217 -> Ok RustcLangItemFrom
     | 218 -> Ok RustcLangItemFromFn
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and layout_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (layout, string) result =
  combine_error_msgs st __FUNCTION__
    (let* size = size_expr_of_postcard ctx st in
     let* align = size_expr_of_postcard ctx st in
     let* discriminator = option_of_postcard discriminator_of_postcard ctx st in
     let* uninhabited = bool_of_postcard ctx st in
     let* variant_layouts =
       index_vec_of_postcard variant_id_of_postcard
         (option_of_postcard variant_layout_of_postcard)
         ctx st
     in
     let* repr = repr_options_of_postcard ctx st in
     Ok
       ({ size; align; discriminator; uninhabited; variant_layouts; repr }
         : layout))

and local_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (local, string) result =
  combine_error_msgs st __FUNCTION__
    (let* index = local_id_of_postcard ctx st in
     let* name = option_of_postcard string_of_postcard ctx st in
     let* span = span_of_postcard ctx st in
     let* local_ty = ty_of_postcard ctx st in
     Ok ({ index; name; span; local_ty } : local))

and locals_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (locals, string) result =
  combine_error_msgs st __FUNCTION__
    (let* arg_count = usize_of_postcard ctx st in
     let* locals =
       index_vec_of_postcard local_id_of_postcard local_of_postcard ctx st
     in
     Ok ({ arg_count; locals } : locals))

and maybe_assoc_item_id_of_postcard (ctx : of_postcard_ctx)
    (st : postcard_state) : (maybe_assoc_item_id, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 ->
         let* _0 = item_id_of_postcard ctx st in
         Ok (ItemFree _0)
     | 1 ->
         let* _0 = trait_decl_id_of_postcard ctx st in
         let* _1 = assoc_item_id_of_postcard ctx st in
         Ok (ItemAssoc (_0, _1))
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and metadata_value_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (metadata_value, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 -> Ok DynSize
     | 1 -> Ok DynAlign
     | 2 -> Ok SliceLength
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and mir_level_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (mir_level, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 -> Ok Built
     | 1 -> Ok Promoted
     | 2 -> Ok Elaborated
     | 3 -> Ok Optimized
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and monomorphize_mut_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (monomorphize_mut, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 -> Ok All
     | 1 -> Ok ExceptTypes
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and offset_expr_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (offset_expr, string) result =
  combine_error_msgs st __FUNCTION__
    (let* guarantee = option_of_postcard offset_guarantee_of_postcard ctx st in
     let* chosen = option_of_postcard u64_of_postcard ctx st in
     Ok ({ guarantee; chosen } : offset_expr))

and offset_guarantee_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (offset_guarantee, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 -> Ok AtOffsetZero
     | 1 ->
         let* _0 = exact_size_expr_of_postcard ctx st in
         Ok (GuaranteedAlignment _0)
     | 2 ->
         let* predecessor = option_of_postcard field_id_of_postcard ctx st in
         Ok (ReprCField predecessor)
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and rustc_optimize_attr_of_postcard (ctx : of_postcard_ctx)
    (st : postcard_state) : (rustc_optimize_attr, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 -> Ok RustcOptimizeAttrDefault
     | 1 -> Ok RustcOptimizeAttrDoNotOptimize
     | 2 -> Ok RustcOptimizeAttrSpeed
     | 3 -> Ok RustcOptimizeAttrSize
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and preset_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (preset, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 -> Ok OldDefaults
     | 1 -> Ok RawMir
     | 2 -> Ok Fast
     | 3 -> Ok Aeneas
     | 4 -> Ok Eurydice
     | 5 -> Ok Soteria
     | 6 -> Ok Tests
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and ptr_metadata_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (ptr_metadata, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 -> Ok NoMetadata
     | 1 -> Ok Length
     | 2 ->
         let* _0 = type_decl_ref_of_postcard ctx st in
         Ok (VTable _0)
     | 3 ->
         let* _0 = ty_of_postcard ctx st in
         Ok (InheritFrom _0)
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and raw_attribute_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (raw_attribute, string) result =
  combine_error_msgs st __FUNCTION__
    (let* path = string_of_postcard ctx st in
     let* args = option_of_postcard string_of_postcard ctx st in
     Ok ({ path; args } : raw_attribute))

and repr_algorithm_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (repr_algorithm, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 -> Ok Rust
     | 1 -> Ok C
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and repr_options_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (repr_options, string) result =
  combine_error_msgs st __FUNCTION__
    (let* repr_algo = repr_algorithm_of_postcard ctx st in
     let* align_modif =
       option_of_postcard alignment_modifier_of_postcard ctx st
     in
     let* transparent = bool_of_postcard ctx st in
     let* explicit_discr_type =
       option_of_postcard literal_type_of_postcard ctx st
     in
     Ok
       ({ repr_algo; align_modif; transparent; explicit_discr_type }
         : repr_options))

and rustc_rustc_version_of_postcard (ctx : of_postcard_ctx)
    (st : postcard_state) : (rustc_rustc_version, string) result =
  combine_error_msgs st __FUNCTION__
    (let* major = u16_of_postcard ctx st in
     let* minor = u16_of_postcard ctx st in
     let* patch = u16_of_postcard ctx st in
     Ok ({ major; minor; patch } : rustc_rustc_version))

and serialization_format_arg_of_postcard (ctx : of_postcard_ctx)
    (st : postcard_state) : (serialization_format_arg, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 -> Ok Json
     | 1 -> Ok Postcard
     | 2 -> Ok AllFormats
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and size_expr_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (size_expr, string) result =
  combine_error_msgs st __FUNCTION__
    (let* guarantee = option_of_postcard size_guarantee_of_postcard ctx st in
     let* chosen = option_of_postcard u64_of_postcard ctx st in
     Ok ({ guarantee; chosen } : size_expr))

and size_guarantee_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (size_guarantee, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 ->
         let* _0 = exact_size_expr_of_postcard ctx st in
         Ok (Equals _0)
     | 1 ->
         let* _0 = exact_size_expr_of_postcard ctx st in
         Ok (AtLeast _0)
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and target_info_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (target_info, string) result =
  combine_error_msgs st __FUNCTION__
    (let* target_pointer_size = u64_of_postcard ctx st in
     let* is_little_endian = bool_of_postcard ctx st in
     let* c_enum_smallest_repr_ty = int_ty_of_postcard ctx st in
     let* primitive_alignments =
       index_map_of_postcard literal_type_of_postcard u64_of_postcard
         int_of_postcard ctx st
     in
     Ok
       ({
          target_pointer_size;
          is_little_endian;
          c_enum_smallest_repr_ty;
          primitive_alignments;
        }
         : target_info))

and trait_assoc_const_of_postcard (ctx : of_postcard_ctx) (st : postcard_state)
    : (trait_assoc_const, string) result =
  combine_error_msgs st __FUNCTION__
    (let* name = trait_item_name_of_postcard ctx st in
     let* attr_info = attr_info_of_postcard ctx st in
     let* ty = ty_of_postcard ctx st in
     let* default = option_of_postcard global_decl_ref_of_postcard ctx st in
     Ok ({ name; attr_info; ty; default } : trait_assoc_const))

and trait_assoc_ty_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (trait_assoc_ty, string) result =
  combine_error_msgs st __FUNCTION__
    (let* name = trait_item_name_of_postcard ctx st in
     let* attr_info = attr_info_of_postcard ctx st in
     let* default = option_of_postcard trait_assoc_ty_impl_of_postcard ctx st in
     let* implied_clauses =
       index_vec_of_postcard trait_clause_id_of_postcard trait_param_of_postcard
         ctx st
     in
     Ok ({ name; attr_info; default; implied_clauses } : trait_assoc_ty))

and trait_decl_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (trait_decl, string) result =
  combine_error_msgs st __FUNCTION__
    (let* def_id = trait_decl_id_of_postcard ctx st in
     let* item_meta = item_meta_of_postcard ctx st in
     let* src = trait_decl_source_of_postcard ctx st in
     let* generics = generic_params_of_postcard ctx st in
     let* implied_clauses =
       index_vec_of_postcard trait_clause_id_of_postcard trait_param_of_postcard
         ctx st
     in
     let* consts =
       (fun ctx st ->
         Result.map AssocConstId.map_of_indexed_list
           (opt_indexed_map_of_postcard assoc_const_id_of_postcard
              trait_assoc_const_of_postcard ctx st))
         ctx st
     in
     let* types =
       (fun ctx st ->
         Result.map AssocTypeId.map_of_indexed_list
           (opt_indexed_map_of_postcard assoc_type_id_of_postcard
              (binder_of_postcard trait_assoc_ty_of_postcard)
              ctx st))
         ctx st
     in
     let* methods =
       (fun ctx st ->
         Result.map TraitMethodId.map_of_indexed_list
           (opt_indexed_map_of_postcard trait_method_id_of_postcard
              (binder_of_postcard trait_method_of_postcard)
              ctx st))
         ctx st
     in
     let* vtable = option_of_postcard type_decl_ref_of_postcard ctx st in
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
         : trait_decl))

and trait_decl_source_of_postcard (ctx : of_postcard_ctx) (st : postcard_state)
    : (trait_decl_source, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 -> Ok NormalTraitDecl
     | 1 -> Ok TraitAliasTraitDecl
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and trait_impl_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (trait_impl, string) result =
  combine_error_msgs st __FUNCTION__
    (let* def_id = trait_impl_id_of_postcard ctx st in
     let* item_meta = item_meta_of_postcard ctx st in
     let* src = trait_impl_source_of_postcard ctx st in
     let* impl_trait = trait_decl_ref_of_postcard ctx st in
     let* generics = generic_params_of_postcard ctx st in
     let* implied_trait_refs =
       index_vec_of_postcard trait_clause_id_of_postcard trait_ref_of_postcard
         ctx st
     in
     let* consts =
       (fun ctx st ->
         Result.map AssocConstId.map_of_indexed_list
           (opt_indexed_map_of_postcard assoc_const_id_of_postcard
              global_decl_ref_of_postcard ctx st))
         ctx st
     in
     let* types =
       (fun ctx st ->
         Result.map AssocTypeId.map_of_indexed_list
           (opt_indexed_map_of_postcard assoc_type_id_of_postcard
              (binder_of_postcard trait_assoc_ty_impl_of_postcard)
              ctx st))
         ctx st
     in
     let* methods =
       (fun ctx st ->
         Result.map TraitMethodId.map_of_indexed_list
           (opt_indexed_map_of_postcard trait_method_id_of_postcard
              (binder_of_postcard fun_decl_ref_of_postcard)
              ctx st))
         ctx st
     in
     let* vtable = option_of_postcard global_decl_ref_of_postcard ctx st in
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
         : trait_impl))

and trait_impl_source_of_postcard (ctx : of_postcard_ctx) (st : postcard_state)
    : (trait_impl_source, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 -> Ok NormalTraitImpl
     | 1 -> Ok TraitAliasTraitImpl
     | 2 ->
         let* kind = closure_kind_of_postcard ctx st in
         Ok (ClosureTraitImpl kind)
     | 3 -> Ok DestructTraitImpl
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and trait_item_name_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (trait_item_name, string) result =
  combine_error_msgs st __FUNCTION__ (string_of_postcard ctx st)

and trait_method_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (trait_method, string) result =
  combine_error_msgs st __FUNCTION__
    (let* name = trait_item_name_of_postcard ctx st in
     let* item_meta = item_meta_of_postcard ctx st in
     let* signature = fun_sig_of_postcard ctx st in
     let* default = option_of_postcard fun_decl_ref_of_postcard ctx st in
     Ok ({ name; item_meta; signature; default } : trait_method))

and translated_crate_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (translated_crate, string) result =
  combine_error_msgs st __FUNCTION__
    (let* crate_name = string_of_postcard ctx st in
     let* options = cli_options_of_postcard ctx st in
     let* target_information =
       index_map_of_postcard string_of_postcard target_info_of_postcard
         int_of_postcard ctx st
     in
     let* files =
       index_vec_of_postcard file_id_of_postcard file_of_postcard ctx st
     in
     let* item_names =
       index_map_of_postcard item_id_of_postcard name_of_postcard
         int_of_postcard ctx st
     in
     let* assoc_item_names =
       (fun ctx st ->
         Result.map TraitDeclId.map_of_indexed_list
           (opt_indexed_map_of_postcard trait_decl_id_of_postcard
              assoc_item_names_of_postcard ctx st))
         ctx st
     in
     let* short_names =
       index_map_of_postcard item_id_of_postcard name_of_postcard
         int_of_postcard ctx st
     in
     let* type_decls =
       (fun ctx st ->
         Result.map TypeDeclId.map_of_indexed_list
           (opt_indexed_map_of_postcard type_decl_id_of_postcard
              type_decl_of_postcard ctx st))
         ctx st
     in
     let* fun_decls =
       (fun ctx st ->
         Result.map FunDeclId.map_of_indexed_list
           (opt_indexed_map_of_postcard fun_decl_id_of_postcard
              fun_decl_of_postcard ctx st))
         ctx st
     in
     let* global_decls =
       (fun ctx st ->
         Result.map GlobalDeclId.map_of_indexed_list
           (opt_indexed_map_of_postcard global_decl_id_of_postcard
              global_decl_of_postcard ctx st))
         ctx st
     in
     let* trait_decls =
       (fun ctx st ->
         Result.map TraitDeclId.map_of_indexed_list
           (opt_indexed_map_of_postcard trait_decl_id_of_postcard
              trait_decl_of_postcard ctx st))
         ctx st
     in
     let* trait_impls =
       (fun ctx st ->
         Result.map TraitImplId.map_of_indexed_list
           (opt_indexed_map_of_postcard trait_impl_id_of_postcard
              trait_impl_of_postcard ctx st))
         ctx st
     in
     let* ordered_decls =
       option_of_postcard
         (list_of_postcard declaration_group_of_postcard)
         ctx st
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
         : translated_crate))

and type_decl_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (type_decl, string) result =
  combine_error_msgs st __FUNCTION__
    (let* def_id = type_decl_id_of_postcard ctx st in
     let* item_meta = item_meta_of_postcard ctx st in
     let* generics = generic_params_of_postcard ctx st in
     let* src = type_source_of_postcard ctx st in
     let* kind = type_decl_kind_of_postcard ctx st in
     let* layout =
       index_map_of_postcard string_of_postcard layout_of_postcard
         int_of_postcard ctx st
     in
     let* ptr_metadata = ptr_metadata_of_postcard ctx st in
     Ok
       ({ def_id; item_meta; generics; src; kind; layout; ptr_metadata }
         : type_decl))

and type_decl_kind_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (type_decl_kind, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 ->
         let* _0 =
           index_vec_of_postcard field_id_of_postcard field_of_postcard ctx st
         in
         Ok (Struct _0)
     | 1 ->
         let* _0 =
           index_vec_of_postcard variant_id_of_postcard variant_of_postcard ctx
             st
         in
         Ok (Enum _0)
     | 2 ->
         let* _0 =
           index_vec_of_postcard field_id_of_postcard field_of_postcard ctx st
         in
         Ok (Union _0)
     | 3 -> Ok Opaque
     | 4 ->
         let* _0 = ty_of_postcard ctx st in
         Ok (Alias _0)
     | 5 ->
         let* _0 = string_of_postcard ctx st in
         Ok (TDeclError _0)
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and type_source_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (type_source, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 -> Ok NormalType
     | 1 ->
         let* info = closure_info_of_postcard ctx st in
         Ok (ClosureType info)
     | 2 ->
         let* dyn_predicate = dyn_predicate_of_postcard ctx st in
         let* field_map =
           index_vec_of_postcard field_id_of_postcard v_table_field_of_postcard
             ctx st
         in
         let* supertrait_map =
           index_vec_of_postcard trait_clause_id_of_postcard
             (option_of_postcard field_id_of_postcard)
             ctx st
         in
         Ok (VTableType (dyn_predicate, field_map, supertrait_map))
     | 3 ->
         let* _0 = builtin_ty_of_postcard ctx st in
         Ok (BuiltinType _0)
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and v_table_field_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (v_table_field, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 -> Ok VTableSize
     | 1 -> Ok VTableAlign
     | 2 -> Ok VTableDrop
     | 3 ->
         let* _0 = trait_method_id_of_postcard ctx st in
         Ok (VTableMethod _0)
     | 4 ->
         let* _0 = trait_clause_id_of_postcard ctx st in
         Ok (VTableSuperTrait _0)
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and variant_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (variant, string) result =
  combine_error_msgs st __FUNCTION__
    (let* id = variant_id_of_postcard ctx st in
     let* span = span_of_postcard ctx st in
     let* attr_info = attr_info_of_postcard ctx st in
     let* variant_name = string_of_postcard ctx st in
     let* fields =
       index_vec_of_postcard field_id_of_postcard field_of_postcard ctx st
     in
     let* discriminant = literal_of_postcard ctx st in
     Ok ({ id; span; attr_info; variant_name; fields; discriminant } : variant))

and variant_layout_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (variant_layout, string) result =
  combine_error_msgs st __FUNCTION__
    (let* field_offsets =
       index_vec_of_postcard field_id_of_postcard offset_expr_of_postcard ctx st
     in
     let* uninhabited = bool_of_postcard ctx st in
     let* tagger =
       list_of_postcard
         (pair_of_postcard u64_of_postcard scalar_value_of_postcard)
         ctx st
     in
     Ok ({ field_offsets; uninhabited; tagger } : variant_layout))
