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
open DeserializationCtx

type of_postcard_ctx = DeserializationCtx.t

let empty_of_postcard_ctx = DeserializationCtx.empty ()

(** Values that come up often are deduplicated in the serialized output: the
    first occurrence of a value is serialized in full along with an id, and
    later occurrences only mention that id. *)
let dedup_val_of_postcard (tbl : 'a DedupTbl.t)
    (of_postcard : of_postcard_ctx -> postcard_state -> ('a, string) result)
    (ctx : of_postcard_ctx) (st : postcard_state) : ('a, string) result =
  combine_error_msgs st __FUNCTION__
    (let* tag = int_of_postcard ctx st in
     match tag with
     | 0 ->
         let* id = DedupId.id_of_postcard ctx st in
         let* v = of_postcard ctx st in
         DedupTbl.replace tbl id v;
         Ok v
     | 1 ->
         let* id = DedupId.id_of_postcard ctx st in
         begin
           match DedupTbl.find_opt tbl id with
           | Some v -> Ok v
           | None ->
               Error
                 "Deduplication key not found; there is a serialization \
                  mismatch between Rust and OCaml"
         end
     | 2 -> of_postcard ctx st
     | _ -> Error "invalid deduplicated value representation")

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
     | 0 -> Ok AbortPanic
     | 1 -> Ok AbortUndefinedBehavior
     | 2 ->
         let* _0 = unwind_terminate_reason_of_postcard ctx st in
         Ok (AbortUnwindTerminate _0)
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
         let* _2 = option_of_postcard trait_ref_of_postcard ctx st in
         Ok (AggregatedArray (_0, _1, _2))
     | 2 ->
         let* _0 = ty_of_postcard ctx st in
         let* _1 = ref_kind_of_postcard ctx st in
         Ok (AggregatedRawPtr (_0, _1))
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and asm_kind_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (asm_kind, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 -> Ok Asm
     | 1 -> Ok NakedAsm
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and asm_operand_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (asm_operand, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 ->
         let* reg = asm_register_of_postcard ctx st in
         let* value = operand_of_postcard ctx st in
         Ok (In (reg, value))
     | 1 ->
         let* reg = asm_register_of_postcard ctx st in
         let* late = bool_of_postcard ctx st in
         let* place = option_of_postcard place_of_postcard ctx st in
         Ok (Out (reg, late, place))
     | 2 ->
         let* reg = asm_register_of_postcard ctx st in
         let* late = bool_of_postcard ctx st in
         let* in_value = operand_of_postcard ctx st in
         let* out_place = option_of_postcard place_of_postcard ctx st in
         Ok (InOut (reg, late, in_value, out_place))
     | 3 ->
         let* _0 = constant_expr_of_postcard ctx st in
         Ok (Const _0)
     | 4 ->
         let* _0 = fn_ptr_of_postcard ctx st in
         Ok (SymFn _0)
     | 5 ->
         let* _0 = global_decl_ref_of_postcard ctx st in
         Ok (SymStatic _0)
     | 6 ->
         let* _0 = branch_id_of_postcard ctx st in
         Ok (Label _0)
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and asm_operand_id_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (asm_operand_id, string) result =
  combine_error_msgs st __FUNCTION__ (AsmOperandId.id_of_postcard ctx st)

and asm_options_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (asm_options, string) result =
  combine_error_msgs st __FUNCTION__
    (let* pure = bool_of_postcard ctx st in
     let* nomem = bool_of_postcard ctx st in
     let* readonly = bool_of_postcard ctx st in
     let* preserves_flags = bool_of_postcard ctx st in
     let* noreturn = bool_of_postcard ctx st in
     let* nostack = bool_of_postcard ctx st in
     let* att_syntax = bool_of_postcard ctx st in
     let* may_unwind = bool_of_postcard ctx st in
     Ok
       ({
          pure;
          nomem;
          readonly;
          preserves_flags;
          noreturn;
          nostack;
          att_syntax;
          may_unwind;
        }
         : asm_options))

and asm_register_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (asm_register, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 ->
         let* _0 = string_of_postcard ctx st in
         Ok (Explicit _0)
     | 1 ->
         let* _0 = string_of_postcard ctx st in
         Ok (Class _0)
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and asm_template_piece_of_postcard (ctx : of_postcard_ctx) (st : postcard_state)
    : (asm_template_piece, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 ->
         let* _0 = string_of_postcard ctx st in
         Ok (AsmTemplateText _0)
     | 1 ->
         let* operand_id = asm_operand_id_of_postcard ctx st in
         let* modifier = option_of_postcard char_of_postcard ctx st in
         let* span = span_of_postcard ctx st in
         Ok (AsmTemplatePlaceholder (operand_id, modifier, span))
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and assertion_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (assertion, string) result =
  combine_error_msgs st __FUNCTION__
    (let* cond = operand_of_postcard ctx st in
     let* expected = bool_of_postcard ctx st in
     let* check_kind =
       option_of_postcard builtin_assert_kind_of_postcard ctx st
     in
     let* call = box_of_postcard call_of_postcard ctx st in
     Ok ({ cond; expected; check_kind; call } : assertion))

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
     | 14 ->
         let* _0 = overflow_mode_of_postcard ctx st in
         Ok (Shl _0)
     | 15 ->
         let* _0 = overflow_mode_of_postcard ctx st in
         Ok (Shr _0)
     | 16 -> Ok Cmp
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
         let* _0 = place_type_constraint_of_postcard ctx st in
         Ok (SetType _0)
     | 2 ->
         let* _0 = outlives_pred_of_postcard ctx st in
         Ok (SetOutlives _0)
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and branch_id_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (branch_id, string) result =
  combine_error_msgs st __FUNCTION__ (BranchId.id_of_postcard ctx st)

and builtin_adt_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (builtin_adt, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 -> Ok TTuple
     | 1 -> Ok TBox
     | 2 -> Ok TStr
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

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
     | 14 -> Ok BuiltinFnAddr
     | 15 -> Ok BuiltinFnPtr
     | 16 -> Ok BuiltinAsyncFn
     | 17 -> Ok BuiltinAsyncFnMut
     | 18 -> Ok BuiltinAsyncFnOnce
     | 19 -> Ok BuiltinCoroutine
     | 20 -> Ok BuiltinFuture
     | 21 -> Ok BuiltinTryAsDynCompatible
     | 22 -> Ok BuiltinNoopDestruct
     | 23 -> Ok BuiltinUntrackedDestruct
     | 24 -> Ok BuiltinRemovedAdtClause
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
         let* _0 = box_of_postcard pointer_fragment_of_postcard ctx st in
         Ok (Provenance _0)
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and call_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (call, string) result =
  combine_error_msgs st __FUNCTION__
    (let* func = fn_operand_of_postcard ctx st in
     let* args = list_of_postcard operand_of_postcard ctx st in
     let* safety = call_safety_of_postcard ctx st in
     Ok ({ func; args; safety } : call))

and call_safety_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (call_safety, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 -> Ok Inherit
     | 1 -> Ok Safe
     | 2 -> Ok Unsafe
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and cast_kind_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (cast_kind, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 ->
         let* _0 = scalar_type_of_postcard ctx st in
         Ok (CastScalar _0)
     | 1 ->
         let* _0 = ty_of_postcard ctx st in
         Ok (CastRawPtr _0)
     | 2 ->
         let* _0 = integer_type_of_postcard ctx st in
         Ok (CastPtrExposeProvenance _0)
     | 3 ->
         let* _0 = ty_of_postcard ctx st in
         Ok (CastPtrWithExposedProvenance _0)
     | 4 -> Ok CastFnDefToFnPtr
     | 5 -> Ok CastFnPtrToUnsafe
     | 6 ->
         let* _0 = ty_of_postcard ctx st in
         Ok (CastSubtype _0)
     | 7 ->
         let* _0 = ty_of_postcard ctx st in
         let* _1 = unsizing_metadata_of_postcard ctx st in
         let* _2 = list_of_postcard field_id_of_postcard ctx st in
         Ok (CastUnsize (_0, _1, _2))
     | 8 ->
         let* _0 = ty_of_postcard ctx st in
         Ok (CastTransmute _0)
     | 9 ->
         let* _0 = ty_of_postcard ctx st in
         Ok (CastBoxDerefTransmute _0)
     | 10 ->
         let* _0 = ty_of_postcard ctx st in
         let* _1 = list_of_postcard field_id_of_postcard ctx st in
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

and const_projection_elem_of_postcard (ctx : of_postcard_ctx)
    (st : postcard_state) : (const_projection_elem, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 ->
         let* _0 = option_of_postcard variant_id_of_postcard ctx st in
         let* _1 = field_id_of_postcard ctx st in
         Ok (CProjField (_0, _1))
     | 1 ->
         let* _0 = integer_value_of_postcard ctx st in
         Ok (CProjIndex _0)
     | 2 ->
         let* from = integer_value_of_postcard ctx st in
         let* to_ = integer_value_of_postcard ctx st in
         Ok (CProjSubslice (from, to_))
     | 3 ->
         let* count = integer_value_of_postcard ctx st in
         let* ty = option_of_postcard ty_of_postcard ctx st in
         let* in_bounds = bool_of_postcard ctx st in
         let* pointee_is_sized =
           option_of_postcard trait_ref_of_postcard ctx st
         in
         Ok (CProjOffset (count, ty, in_bounds, pointee_is_sized))
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and constant_expr_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (constant_expr, string) result =
  combine_error_msgs st __FUNCTION__
    (dedup_val_of_postcard ctx.constant_expr_dedup_tbl
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
         let* _0 = bool_of_postcard ctx st in
         Ok (CBool _0)
     | 1 ->
         let* _0 = integer_value_of_postcard ctx st in
         Ok (CInteger _0)
     | 2 ->
         let* _0 = char_of_postcard ctx st in
         Ok (CChar _0)
     | 3 ->
         let* _0 = float_value_of_postcard ctx st in
         Ok (CFloat _0)
     | 4 ->
         let* _0 = option_of_postcard variant_id_of_postcard ctx st in
         let* _1 =
           index_vec_of_postcard field_id_of_postcard constant_expr_of_postcard
             ctx st
         in
         Ok (CAdt (_0, _1))
     | 5 ->
         let* _0 = list_of_postcard constant_expr_of_postcard ctx st in
         Ok (CArray _0)
     | 6 ->
         let* _0 = global_place_of_postcard ctx st in
         let* _1 = option_of_postcard unsizing_metadata_of_postcard ctx st in
         Ok (CRef (_0, _1))
     | 7 ->
         let* _0 = ref_kind_of_postcard ctx st in
         let* _1 = global_place_of_postcard ctx st in
         let* _2 = option_of_postcard unsizing_metadata_of_postcard ctx st in
         Ok (CPtr (_0, _1, _2))
     | 8 ->
         let* _0 = string_of_postcard ctx st in
         Ok (CStr _0)
     | 9 ->
         let* _0 = list_of_postcard u8_of_postcard ctx st in
         Ok (CByteStr _0)
     | 10 ->
         let* _0 = fn_ptr_of_postcard ctx st in
         Ok (CFnDef _0)
     | 11 ->
         let* _0 = fn_ptr_of_postcard ctx st in
         Ok (CFnPtr _0)
     | 12 ->
         let* _0 = constant_expr_of_postcard ctx st in
         let* _1 = cast_kind_of_postcard ctx st in
         Ok (CCast (_0, _1))
     | 13 ->
         let* _0 = big_uint_of_postcard ctx st in
         Ok (CPtrNoProvenance _0)
     | 14 ->
         let* _0 = string_of_postcard ctx st in
         Ok (CExternSymbol _0)
     | 15 ->
         let* _0 = ty_of_postcard ctx st in
         Ok (CTypeId _0)
     | 16 ->
         let* _0 = list_of_postcard byte_of_postcard ctx st in
         Ok (CRawMemory _0)
     | 17 ->
         let* _0 =
           de_bruijn_var_of_postcard const_generic_var_id_of_postcard ctx st
         in
         Ok (CVar _0)
     | 18 ->
         let* _0 = global_decl_ref_of_postcard ctx st in
         Ok (CGlobal _0)
     | 19 ->
         let* _0 = fn_ptr_of_postcard ctx st in
         let* _1 = list_of_postcard constant_expr_of_postcard ctx st in
         Ok (CCall (_0, _1))
     | 20 ->
         let* _0 = trait_ref_of_postcard ctx st in
         let* _1 = assoc_const_id_of_postcard ctx st in
         Ok (CTraitConst (_0, _1))
     | 21 ->
         let* _0 = poly_trait_ref_of_postcard ctx st in
         Ok (CVTableRef _0)
     | 22 ->
         let* _0 = type_decl_ref_of_postcard ctx st in
         let* _1 = variant_id_of_postcard ctx st in
         Ok (CDiscriminant (_0, _1))
     | 23 ->
         let* value = constant_expr_of_postcard ctx st in
         let* count = constant_expr_of_postcard ctx st in
         let* value_is_sized =
           option_of_postcard trait_ref_of_postcard ctx st
         in
         Ok (CRepeat (value, count, value_is_sized))
     | 24 ->
         let* _0 = ty_of_postcard ctx st in
         Ok (CSizeOf _0)
     | 25 ->
         let* _0 = ty_of_postcard ctx st in
         Ok (CAlignOf _0)
     | 26 ->
         let* _0 = type_decl_ref_of_postcard ctx st in
         let* _1 = option_of_postcard variant_id_of_postcard ctx st in
         let* _2 = field_id_of_postcard ctx st in
         Ok (COffsetOf (_0, _1, _2))
     | 27 ->
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
     let* float_bits = big_uint_of_postcard ctx st in
     let* float_ty = float_type_of_postcard ctx st in
     Ok ({ float_value; float_bits; float_ty } : float_value))

and fn_operand_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (fn_operand, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 ->
         let* _0 = fn_ptr_of_postcard ctx st in
         Ok (FnOpRegular _0)
     | 1 ->
         let* _0 = box_of_postcard operand_of_postcard ctx st in
         let* _1 = region_args_of_postcard ctx st in
         Ok (FnOpDynamic (_0, _1))
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
         let* _0 = fun_decl_id_of_postcard ctx st in
         Ok (Fun _0)
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
       index_vec_of_postcard trait_clause_id_of_postcard
         poly_trait_ref_of_postcard ctx st
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
     let* outlives =
       list_of_postcard
         (region_binder_of_postcard outlives_pred_of_postcard)
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
          outlives;
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

and global_place_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (global_place, string) result =
  combine_error_msgs st __FUNCTION__
    (let* global_place_kind = global_place_kind_of_postcard ctx st in
     let* global_place_ty = ty_of_postcard ctx st in
     Ok ({ global_place_kind; global_place_ty } : global_place))

and global_place_kind_of_postcard (ctx : of_postcard_ctx) (st : postcard_state)
    : (global_place_kind, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 ->
         let* _0 = global_provenance_of_postcard ctx st in
         Ok (GlobalPlaceGlobal _0)
     | 1 ->
         let* _0 = constant_expr_of_postcard ctx st in
         Ok (GlobalPlaceValue _0)
     | 2 ->
         let* _0 = box_of_postcard global_place_of_postcard ctx st in
         let* _1 = const_projection_elem_of_postcard ctx st in
         Ok (GlobalPlaceProjection (_0, _1))
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and global_provenance_of_postcard (ctx : of_postcard_ctx) (st : postcard_state)
    : (global_provenance, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 ->
         let* _0 = global_decl_ref_of_postcard ctx st in
         Ok (ProvGlobal _0)
     | 1 ->
         let* _0 = fn_ptr_of_postcard ctx st in
         let* _1 = ty_of_postcard ctx st in
         Ok (ProvFunction (_0, _1))
     | 2 ->
         let* _0 = ty_of_postcard ctx st in
         Ok (ProvTypeId _0)
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and hash_consed_of_postcard :
    'a0.
    (of_postcard_ctx -> postcard_state -> ('a0, string) result) ->
    of_postcard_ctx ->
    postcard_state ->
    ('a0 hash_consed, string) result =
 fun arg0_of_postcard ctx st ->
  combine_error_msgs st __FUNCTION__
    (Error "use `dedup_val_of_postcard` instead")

and index_vec_of_postcard :
    'a0 'a1.
    (of_postcard_ctx -> postcard_state -> ('a0, string) result) ->
    (of_postcard_ctx -> postcard_state -> ('a1, string) result) ->
    of_postcard_ctx ->
    postcard_state ->
    ('a1 list, string) result =
 fun arg0_of_postcard arg1_of_postcard ctx st ->
  combine_error_msgs st __FUNCTION__ (list_of_postcard arg1_of_postcard ctx st)

and inline_asm_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (inline_asm, string) result =
  combine_error_msgs st __FUNCTION__
    (let* kind = asm_kind_of_postcard ctx st in
     let* template = list_of_postcard asm_template_piece_of_postcard ctx st in
     let* operands =
       index_vec_of_postcard asm_operand_id_of_postcard asm_operand_of_postcard
         ctx st
     in
     let* options = asm_options_of_postcard ctx st in
     Ok ({ kind; template; operands; options } : inline_asm))

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

and integer_value_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (integer_value, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 ->
         let* _0 = u_int_ty_of_postcard ctx st in
         let* _1 = big_uint_of_postcard ctx st in
         Ok (UnsignedInteger (_0, _1))
     | 1 ->
         let* _0 = int_ty_of_postcard ctx st in
         let* _1 = big_int_of_postcard ctx st in
         Ok (SignedInteger (_0, _1))
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

and loc_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (loc, string) result =
  combine_error_msgs st __FUNCTION__
    (let* line = u32_of_postcard ctx st in
     let* col = u32_of_postcard ctx st in
     Ok ({ line; col } : loc))

and local_id_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (local_id, string) result =
  combine_error_msgs st __FUNCTION__ (LocalId.id_of_postcard ctx st)

and nullop_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (nullop, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 -> Ok UbChecks
     | 1 -> Ok OverflowChecks
     | 2 -> Ok ContractChecks
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and operand_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (operand, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 ->
         let* _0 = place_of_postcard ctx st in
         let* _1 = trait_ref_of_postcard ctx st in
         Ok (Copy (_0, _1))
     | 1 ->
         let* _0 = place_of_postcard ctx st in
         Ok (Read _0)
     | 2 ->
         let* _0 = place_of_postcard ctx st in
         Ok (Move _0)
     | 3 ->
         let* _0 = constant_expr_of_postcard ctx st in
         Ok (Constant _0)
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and outlives_pred_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (outlives_pred, string) result =
  combine_error_msgs st __FUNCTION__
    (let* _0 = region_of_postcard ctx st in
     let* _1 = region_of_postcard ctx st in
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
         let* _0 = place_of_postcard ctx st in
         let* _1 = projection_elem_of_postcard ctx st in
         Ok (PlaceProjection (_0, _1))
     | 2 ->
         let* _0 = box_of_postcard global_decl_ref_of_postcard ctx st in
         Ok (PlaceGlobal _0)
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and place_type_constraint_of_postcard (ctx : of_postcard_ctx)
    (st : postcard_state) : (place_type_constraint, string) result =
  combine_error_msgs st __FUNCTION__
    (let* place = place_of_postcard ctx st in
     let* ty = ty_of_postcard ctx st in
     let* variance = variance_of_postcard ctx st in
     Ok ({ place; ty; variance } : place_type_constraint))

and pointer_fragment_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (pointer_fragment, string) result =
  combine_error_msgs st __FUNCTION__
    (let* provenance = global_provenance_of_postcard ctx st in
     let* offset = integer_value_of_postcard ctx st in
     let* index = u8_of_postcard ctx st in
     Ok ({ provenance; offset; index } : pointer_fragment))

and poly_trait_ref_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (poly_trait_ref, string) result =
  combine_error_msgs st __FUNCTION__
    (region_binder_of_postcard trait_ref_of_postcard ctx st)

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
     | 5 ->
         let* bytes = box_of_postcard operand_of_postcard ctx st in
         let* in_bounds = bool_of_postcard ctx st in
         let* ty = ty_of_postcard ctx st in
         let* ty_is_sized = option_of_postcard trait_ref_of_postcard ctx st in
         Ok (Offset (bytes, in_bounds, ty, ty_is_sized))
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
     | 1 ->
         let* _0 = ty_of_postcard ctx st in
         Ok (RLub _0)
     | 2 -> Ok RStatic
     | 3 ->
         let* _0 = region_id_of_postcard ctx st in
         Ok (RBody _0)
     | 4 -> Ok RErased
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and region_args_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (region_args, string) result =
  combine_error_msgs st __FUNCTION__
    (let* regions =
       index_vec_of_postcard region_id_of_postcard region_of_postcard ctx st
     in
     Ok ({ regions } : region_args))

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
     let* outlives =
       list_of_postcard
         (region_binder_of_postcard outlives_pred_of_postcard)
         ctx st
     in
     let* binder_value = arg0_of_postcard ctx st in
     Ok ({ binder_regions; outlives; binder_value } : _ region_binder))

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
     let* late_bound = bool_of_postcard ctx st in
     Ok ({ index; name; variance; mutability; late_bound } : region_param))

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
         Ok (NullaryOp _0)
     | 6 ->
         let* _0 = place_of_postcard ctx st in
         Ok (Discriminant _0)
     | 7 ->
         let* _0 = aggregate_kind_of_postcard ctx st in
         let* _1 = list_of_postcard operand_of_postcard ctx st in
         Ok (Aggregate (_0, _1))
     | 8 ->
         let* operand = operand_of_postcard ctx st in
         let* count = constant_expr_of_postcard ctx st in
         let* elem_is_copy = trait_ref_of_postcard ctx st in
         let* elem_is_sized = option_of_postcard trait_ref_of_postcard ctx st in
         Ok (Repeat (operand, count, elem_is_copy, elem_is_sized))
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and scalar_type_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (scalar_type, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 ->
         let* _0 = integer_type_of_postcard ctx st in
         Ok (TInteger _0)
     | 1 ->
         let* _0 = float_type_of_postcard ctx st in
         Ok (TFloat _0)
     | 2 -> Ok TBool
     | 3 -> Ok TChar
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and span_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (span, string) result =
  combine_error_msgs st __FUNCTION__
    (dedup_val_of_postcard ctx.span_dedup_tbl
       (fun ctx st ->
         let* data = span_data_of_postcard ctx st in
         let* generated_from_span =
           option_of_postcard span_data_of_postcard ctx st
         in
         Ok ({ data; generated_from_span } : span))
       ctx st)

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
       index_vec_of_postcard trait_clause_id_of_postcard
         poly_trait_ref_of_postcard ctx st
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
    (dedup_val_of_postcard ctx.tref_dedup_tbl trait_ref_contents_of_postcard ctx
       st)

and trait_ref_contents_of_postcard (ctx : of_postcard_ctx) (st : postcard_state)
    : (trait_ref_contents, string) result =
  combine_error_msgs st __FUNCTION__
    (let* kind = trait_ref_kind_of_postcard ctx st in
     let* trait_decl_ref = trait_decl_ref_of_postcard ctx st in
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
         let* _1 = region_args_of_postcard ctx st in
         Ok (Clause (_0, _1))
     | 2 ->
         let* _0 = trait_ref_of_postcard ctx st in
         let* _1 = trait_clause_id_of_postcard ctx st in
         let* _2 = region_args_of_postcard ctx st in
         Ok (ParentClause (_0, _1, _2))
     | 3 ->
         let* trait_ref = trait_ref_of_postcard ctx st in
         let* type_id = assoc_type_id_of_postcard ctx st in
         let* generics = generic_args_of_postcard ctx st in
         let* clause_id = trait_clause_id_of_postcard ctx st in
         let* clause_args = region_args_of_postcard ctx st in
         Ok (ItemClause (trait_ref, type_id, generics, clause_id, clause_args))
     | 4 -> Ok Self
     | 5 ->
         let* builtin_data = builtin_impl_data_of_postcard ctx st in
         let* parent_trait_refs =
           index_vec_of_postcard trait_clause_id_of_postcard
             poly_trait_ref_of_postcard ctx st
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
    (dedup_val_of_postcard ctx.ty_dedup_tbl ty_kind_of_postcard ctx st)

and ty_kind_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (ty_kind, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 ->
         let* _0 = scalar_type_of_postcard ctx st in
         Ok (TScalar _0)
     | 1 ->
         let* _0 = ty_of_postcard ctx st in
         let* _1 = constant_expr_of_postcard ctx st in
         let* _2 = option_of_postcard trait_ref_of_postcard ctx st in
         Ok (TArray (_0, _1, _2))
     | 2 ->
         let* _0 = ty_of_postcard ctx st in
         let* _1 = option_of_postcard trait_ref_of_postcard ctx st in
         Ok (TSlice (_0, _1))
     | 3 ->
         let* _0 = type_decl_ref_of_postcard ctx st in
         Ok (TAdt _0)
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
         let* _0 = region_binder_of_postcard fn_ptr_of_postcard ctx st in
         Ok (TFnDef _0)
     | 7 ->
         let* _0 = region_binder_of_postcard fun_sig_of_postcard ctx st in
         Ok (TFnPtr _0)
     | 8 ->
         let* _0 = dyn_predicate_of_postcard ctx st in
         Ok (TDynTrait _0)
     | 9 ->
         let* _0 = ty_of_postcard ctx st in
         let* _1 = type_pattern_of_postcard ctx st in
         Ok (TPattern (_0, _1))
     | 10 -> Ok TNever
     | 11 ->
         let* _0 = de_bruijn_var_of_postcard type_var_id_of_postcard ctx st in
         Ok (TVar _0)
     | 12 ->
         let* _0 = trait_ref_of_postcard ctx st in
         let* _1 = assoc_type_id_of_postcard ctx st in
         let* _2 = generic_args_of_postcard ctx st in
         Ok (TTraitType (_0, _1, _2))
     | 13 ->
         let* _0 = ty_of_postcard ctx st in
         Ok (TPtrMetadata _0)
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
     let* builtin = option_of_postcard builtin_adt_of_postcard ctx st in
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
         let* _0 = box_of_postcard poly_trait_ref_of_postcard ctx st in
         let* _1 = constant_expr_of_postcard ctx st in
         Ok (MetaVTable (_0, _1))
     | 2 ->
         let* _0 = list_of_postcard field_id_of_postcard ctx st in
         Ok (MetaVTableUpcast _0)
     | 3 ->
         let* _0 = trait_ref_of_postcard ctx st in
         Ok (MetaUnsizeClause _0)
     | 4 ->
         let* _0 = trait_ref_of_postcard ctx st in
         Ok (MetaCoerceUnsizedClause _0)
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and unwind_terminate_reason_of_postcard (ctx : of_postcard_ctx)
    (st : postcard_state) : (unwind_terminate_reason, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 -> Ok Abi
     | 1 -> Ok InCleanup
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
       let* kind = unwind_kind_of_postcard ctx st in
       Ok ({ statements; terminator; kind } : Generated_UllbcAst.block))

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
           let* dest = place_of_postcard ctx st in
           let* target = block_id_of_postcard ctx st in
           let* on_unwind = block_id_of_postcard ctx st in
           Ok (Call (call, dest, target, on_unwind))
       | 3 ->
           let* kind = drop_kind_of_postcard ctx st in
           let* place = place_of_postcard ctx st in
           let* fn_ptr = fn_ptr_of_postcard ctx st in
           let* target = block_id_of_postcard ctx st in
           let* on_unwind = block_id_of_postcard ctx st in
           Ok (Drop (kind, place, fn_ptr, target, on_unwind))
       | 4 ->
           let* place = place_of_postcard ctx st in
           let* target = block_id_of_postcard ctx st in
           let* on_unwind = block_id_of_postcard ctx st in
           Ok (DropEmptyBox (place, target, on_unwind))
       | 5 ->
           let* asm = box_of_postcard inline_asm_of_postcard ctx st in
           let* fallthrough = option_of_postcard block_id_of_postcard ctx st in
           let* labels =
             index_vec_of_postcard branch_id_of_postcard block_id_of_postcard
               ctx st
           in
           let* on_unwind = block_id_of_postcard ctx st in
           Ok (InlineAsm (asm, fallthrough, labels, on_unwind))
       | 6 ->
           let* assert_ = assertion_of_postcard ctx st in
           let* target = block_id_of_postcard ctx st in
           let* on_unwind = block_id_of_postcard ctx st in
           Ok (TAssert (assert_, target, on_unwind))
       | 7 ->
           let* call = call_of_postcard ctx st in
           let* on_unwind = block_id_of_postcard ctx st in
           Ok (Panic (call, on_unwind))
       | 8 ->
           let* _0 = unwind_terminate_reason_of_postcard ctx st in
           let* _1 = fun_decl_ref_of_postcard ctx st in
           Ok (UnwindTerminate (_0, _1))
       | 9 -> Ok UnwindResume
       | 10 -> Ok Return
       | 11 -> Ok UndefinedBehavior
       | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

  and unwind_kind_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
      (unwind_kind, string) result =
    combine_error_msgs st __FUNCTION__
      (let* __tag = int_of_postcard ctx st in
       match __tag with
       | 0 -> Ok Regular
       | 1 -> Ok Cleanup
       | 2 -> Ok Terminate
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
           let* _1 = box_of_postcard rvalue_of_postcard ctx st in
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
           let* _0 = box_of_postcard borrowck_statement_of_postcard ctx st in
           Ok (Borrowck _0)
       | 6 ->
           let* place = box_of_postcard place_of_postcard ctx st in
           let* fn_ptr = fn_ptr_of_postcard ctx st in
           let* kind = drop_kind_of_postcard ctx st in
           let* on_unwind = box_of_postcard block_of_postcard ctx st in
           Ok (Drop (place, fn_ptr, kind, on_unwind))
       | 7 ->
           let* place = place_of_postcard ctx st in
           let* on_unwind = box_of_postcard block_of_postcard ctx st in
           Ok (DropEmptyBox (place, on_unwind))
       | 8 ->
           let* assert_ = box_of_postcard assertion_of_postcard ctx st in
           let* on_failure = abort_kind_of_postcard ctx st in
           let* on_unwind = box_of_postcard block_of_postcard ctx st in
           Ok (Assert (assert_, on_failure, on_unwind))
       | 9 ->
           let* asm = box_of_postcard inline_asm_of_postcard ctx st in
           let* fallthrough =
             option_of_postcard (box_of_postcard block_of_postcard) ctx st
           in
           let* labels =
             box_of_postcard
               (index_vec_of_postcard branch_id_of_postcard block_of_postcard)
               ctx st
           in
           let* on_unwind = box_of_postcard block_of_postcard ctx st in
           Ok (InlineAsm (asm, fallthrough, labels, on_unwind))
       | 10 ->
           let* call = box_of_postcard call_of_postcard ctx st in
           let* dest = box_of_postcard place_of_postcard ctx st in
           let* on_unwind = box_of_postcard block_of_postcard ctx st in
           Ok (Call (call, dest, on_unwind))
       | 11 ->
           let* data = box_of_postcard switch_data_of_postcard ctx st in
           let* branches =
             index_vec_of_postcard branch_id_of_postcard block_of_postcard ctx
               st
           in
           Ok (Switch (data, branches))
       | 12 ->
           let* _0 = box_of_postcard block_of_postcard ctx st in
           Ok (Loop _0)
       | 13 ->
           let* _0 = usize_of_postcard ctx st in
           Ok (Break _0)
       | 14 ->
           let* _0 = usize_of_postcard ctx st in
           Ok (Continue _0)
       | 15 ->
           let* call = box_of_postcard call_of_postcard ctx st in
           let* on_unwind = box_of_postcard block_of_postcard ctx st in
           Ok (Panic (call, on_unwind))
       | 16 ->
           let* _0 = unwind_terminate_reason_of_postcard ctx st in
           let* _1 = fun_decl_ref_of_postcard ctx st in
           Ok (UnwindTerminate (_0, _1))
       | 17 -> Ok UnwindResume
       | 18 -> Ok Return
       | 19 -> Ok UndefinedBehavior
       | 20 -> Ok Nop
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

and rustc_arch_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (rustc_arch, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 -> Ok RustcArchAArch64
     | 1 -> Ok RustcArchAmdGpu
     | 2 -> Ok RustcArchArm
     | 3 -> Ok RustcArchArm64EC
     | 4 -> Ok RustcArchAvr
     | 5 -> Ok RustcArchBpf
     | 6 -> Ok RustcArchCSky
     | 7 -> Ok RustcArchHexagon
     | 8 -> Ok RustcArchLoongArch32
     | 9 -> Ok RustcArchLoongArch64
     | 10 -> Ok RustcArchM68k
     | 11 -> Ok RustcArchMips
     | 12 -> Ok RustcArchMips32r6
     | 13 -> Ok RustcArchMips64
     | 14 -> Ok RustcArchMips64r6
     | 15 -> Ok RustcArchMsp430
     | 16 -> Ok RustcArchNvptx64
     | 17 -> Ok RustcArchPowerPC
     | 18 -> Ok RustcArchPowerPC64
     | 19 -> Ok RustcArchRiscV32
     | 20 -> Ok RustcArchRiscV64
     | 21 -> Ok RustcArchS390x
     | 22 -> Ok RustcArchSparc
     | 23 -> Ok RustcArchSparc64
     | 24 -> Ok RustcArchSpirV
     | 25 -> Ok RustcArchWasm32
     | 26 -> Ok RustcArchWasm64
     | 27 -> Ok RustcArchX86
     | 28 -> Ok RustcArchX86_64
     | 29 -> Ok RustcArchXtensa
     | 30 ->
         let* _0 = string_of_postcard ctx st in
         Ok (RustcArchOther _0)
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
     let* exported = bool_of_postcard ctx st in
     Ok ({ attributes; inline; rename; public; exported } : attr_info))

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
         let* is_inner = bool_of_postcard ctx st in
         Ok (RustcAttributeKindDeprecated (deprecation, span, is_inner))
     | 3 ->
         let* name = string_of_postcard ctx st in
         let* span = span_of_postcard ctx st in
         Ok (RustcAttributeKindExportName (name, span))
     | 4 -> Ok RustcAttributeKindFundamental
     | 5 ->
         let* span = span_of_postcard ctx st in
         let* reason = option_of_postcard string_of_postcard ctx st in
         Ok (RustcAttributeKindIgnore (span, reason))
     | 6 ->
         let* _0 = rustc_inline_attr_of_postcard ctx st in
         let* _1 = span_of_postcard ctx st in
         Ok (RustcAttributeKindInline (_0, _1))
     | 7 ->
         let* name = string_of_postcard ctx st in
         Ok (RustcAttributeKindLinkSection name)
     | 8 ->
         let* _0 = rustc_linkage_of_postcard ctx st in
         let* _1 = span_of_postcard ctx st in
         Ok (RustcAttributeKindLinkage (_0, _1))
     | 9 ->
         let* _0 = span_of_postcard ctx st in
         Ok (RustcAttributeKindMayDangle _0)
     | 10 ->
         let* _0 = span_of_postcard ctx st in
         Ok (RustcAttributeKindNaked _0)
     | 11 -> Ok RustcAttributeKindNoLink
     | 12 ->
         let* _0 = span_of_postcard ctx st in
         Ok (RustcAttributeKindNoMangle _0)
     | 13 ->
         let* _0 = span_of_postcard ctx st in
         Ok (RustcAttributeKindNonExhaustive _0)
     | 14 ->
         let* _0 = rustc_optimize_attr_of_postcard ctx st in
         let* _1 = span_of_postcard ctx st in
         Ok (RustcAttributeKindOptimize (_0, _1))
     | 15 ->
         let* align = u64_of_postcard ctx st in
         let* span = span_of_postcard ctx st in
         Ok (RustcAttributeKindRustcAlign (align, span))
     | 16 -> Ok RustcAttributeKindRustcAllocator
     | 17 -> Ok RustcAttributeKindRustcAllocatorZeroed
     | 18 ->
         let* name = string_of_postcard ctx st in
         Ok (RustcAttributeKindRustcAllocatorZeroedVariant name)
     | 19 -> Ok RustcAttributeKindRustcDeallocator
     | 20 ->
         let* llvm = option_of_postcard string_of_postcard ctx st in
         Ok (RustcAttributeKindRustcIntrinsic llvm)
     | 21 -> Ok RustcAttributeKindRustcNoWritable
     | 22 -> Ok RustcAttributeKindRustcReallocator
     | 23 ->
         let* reason = option_of_postcard string_of_postcard ctx st in
         Ok (RustcAttributeKindShouldPanic reason)
     | 24 ->
         let* features =
           list_of_postcard
             (pair_of_postcard string_of_postcard span_of_postcard)
             ctx st
         in
         let* attr_span = span_of_postcard ctx st in
         let* was_forced = bool_of_postcard ctx st in
         Ok (RustcAttributeKindTargetFeature (features, attr_span, was_forced))
     | 25 ->
         let* _0 = span_of_postcard ctx st in
         Ok (RustcAttributeKindTrackCaller _0)
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and rustc_binary_format_of_postcard (ctx : of_postcard_ctx)
    (st : postcard_state) : (rustc_binary_format, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 -> Ok RustcBinaryFormatCoff
     | 1 -> Ok RustcBinaryFormatElf
     | 2 -> Ok RustcBinaryFormatMachO
     | 3 -> Ok RustcBinaryFormatWasm
     | 4 -> Ok RustcBinaryFormatXcoff
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
         let* symbol = string_of_postcard ctx st in
         let* definition = linked_extern_of_postcard ctx st in
         Ok (ExternBody (symbol, definition))
     | 4 ->
         let* name = string_of_postcard ctx st in
         let* arg_names =
           list_of_postcard (option_of_postcard string_of_postcard) ctx st
         in
         let* fallback = option_of_postcard fun_decl_ref_of_postcard ctx st in
         let* fallback_is_spec = bool_of_postcard ctx st in
         Ok (IntrinsicBody (name, arg_names, fallback, fallback_is_spec))
     | 5 -> Ok OpaqueBody
     | 6 -> Ok MissingBody
     | 7 ->
         let* _0 = error_of_postcard ctx st in
         Ok (ErrorBody _0)
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and builtin_path_elem_of_postcard (ctx : of_postcard_ctx) (st : postcard_state)
    : (builtin_path_elem, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 ->
         let* _0 = usize_of_postcard ctx st in
         Ok (PeTuple _0)
     | 1 -> Ok PeStr
     | 2 -> Ok PeClosure
     | 3 ->
         let* _0 = coroutine_kind_of_postcard ctx st in
         Ok (PeCoroutine _0)
     | 4 -> Ok PeUse
     | 5 -> Ok PeAnonConst
     | 6 -> Ok PePromotedConst
     | 7 -> Ok PeClosureAsFn
     | 8 -> Ok PeDropGlue
     | 9 -> Ok PeVTable
     | 10 -> Ok PeVTableMethod
     | 11 -> Ok PeVTableDropShim
     | 12 -> Ok PeIntrinsicFallback
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and rustc_cfg_abi_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (rustc_cfg_abi, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 -> Ok RustcCfgAbiAbi64
     | 1 -> Ok RustcCfgAbiAbiV2
     | 2 -> Ok RustcCfgAbiAbiV2Hf
     | 3 -> Ok RustcCfgAbiEabi
     | 4 -> Ok RustcCfgAbiEabiHf
     | 5 -> Ok RustcCfgAbiElfV1
     | 6 -> Ok RustcCfgAbiElfV2
     | 7 -> Ok RustcCfgAbiFortanix
     | 8 -> Ok RustcCfgAbiIlp32
     | 9 -> Ok RustcCfgAbiIlp32e
     | 10 -> Ok RustcCfgAbiLlvm
     | 11 -> Ok RustcCfgAbiMacAbi
     | 12 -> Ok RustcCfgAbiPauthtest
     | 13 -> Ok RustcCfgAbiSim
     | 14 -> Ok RustcCfgAbiSoftFloat
     | 15 -> Ok RustcCfgAbiSpe
     | 16 -> Ok RustcCfgAbiUwp
     | 17 -> Ok RustcCfgAbiVecDefault
     | 18 -> Ok RustcCfgAbiX32
     | 19 -> Ok RustcCfgAbiV8Plus
     | 20 -> Ok RustcCfgAbiUnspecified
     | 21 ->
         let* _0 = string_of_postcard ctx st in
         Ok (RustcCfgAbiOther _0)
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and closure_info_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (closure_info, string) result =
  combine_error_msgs st __FUNCTION__
    (let* kind = closure_kind_of_postcard ctx st in
     let* closure_body = fun_decl_ref_of_postcard ctx st in
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
     Ok
       ({ kind; closure_body; fn_once_impl; fn_mut_impl; fn_impl; signature }
         : closure_info))

and closure_kind_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (closure_kind, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 -> Ok Fn
     | 1 -> Ok FnMut
     | 2 -> Ok FnOnce
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and coroutine_info_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (coroutine_info, string) result =
  combine_error_msgs st __FUNCTION__
    (let* kind = coroutine_kind_of_postcard ctx st in
     let* resume = fun_decl_ref_of_postcard ctx st in
     let* trait_impl = trait_impl_ref_of_postcard ctx st in
     Ok ({ kind; resume; trait_impl } : coroutine_info))

and coroutine_kind_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (coroutine_kind, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 -> Ok Coroutine
     | 1 -> Ok Async
     | 2 -> Ok Gen
     | 3 -> Ok AsyncGen
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

and disambiguator_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (disambiguator, string) result =
  combine_error_msgs st __FUNCTION__ (Disambiguator.id_of_postcard ctx st)

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
                (range_inclusive_of_postcard integer_value_of_postcard)
                discriminator_of_postcard)
             ctx st
         in
         let* fallback = box_of_postcard discriminator_of_postcard ctx st in
         Ok (Branch (offset, int_ty, children, fallback))
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and rustc_env_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (rustc_env, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 -> Ok RustcEnvGnu
     | 1 -> Ok RustcEnvMacAbi
     | 2 -> Ok RustcEnvMlibc
     | 3 -> Ok RustcEnvMsvc
     | 4 -> Ok RustcEnvMusl
     | 5 -> Ok RustcEnvNewlib
     | 6 -> Ok RustcEnvNto70
     | 7 -> Ok RustcEnvNto71
     | 8 -> Ok RustcEnvNto71IoSock
     | 9 -> Ok RustcEnvOhos
     | 10 -> Ok RustcEnvRelibc
     | 11 -> Ok RustcEnvSgx
     | 12 -> Ok RustcEnvSim
     | 13 -> Ok RustcEnvP1
     | 14 -> Ok RustcEnvP2
     | 15 -> Ok RustcEnvP3
     | 16 -> Ok RustcEnvUclibc
     | 17 -> Ok RustcEnvV5
     | 18 -> Ok RustcEnvUnspecified
     | 19 ->
         let* _0 = string_of_postcard ctx st in
         Ok (RustcEnvOther _0)
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and error_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (error, string) result =
  combine_error_msgs st __FUNCTION__
    (let* span = span_of_postcard ctx st in
     let* msg = string_of_postcard ctx st in
     Ok ({ span; msg } : error))

and field_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (field, string) result =
  combine_error_msgs st __FUNCTION__
    (let* span = span_of_postcard ctx st in
     let* attr_info = attr_info_of_postcard ctx st in
     let* field_name = string_of_postcard ctx st in
     let* is_positional = bool_of_postcard ctx st in
     let* field_ty = ty_of_postcard ctx st in
     Ok ({ span; attr_info; field_name; is_positional; field_ty } : field))

and field_predecessor_of_postcard (ctx : of_postcard_ctx) (st : postcard_state)
    : (field_predecessor, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 ->
         let* _0 = field_id_of_postcard ctx st in
         Ok (PredecessorField _0)
     | 1 -> Ok PredecessorTag
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

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
         let* self_ty = ty_of_postcard ctx st in
         Ok (InherentImplFun self_ty)
     | 3 ->
         let* trait_ref = trait_decl_ref_of_postcard ctx st in
         let* item_id = trait_method_id_of_postcard ctx st in
         Ok (TraitDefaultFun (trait_ref, item_id))
     | 4 ->
         let* impl_ref = trait_impl_ref_of_postcard ctx st in
         let* trait_ref = trait_decl_ref_of_postcard ctx st in
         let* item_id = trait_method_id_of_postcard ctx st in
         let* reuses_default = bool_of_postcard ctx st in
         Ok (TraitImplFun (impl_ref, trait_ref, item_id, reuses_default))
     | 5 -> Ok VTableShimFun
     | 6 ->
         let* _0 = global_decl_ref_of_postcard ctx st in
         Ok (GlobalInitializerFun _0)
     | 7 ->
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
     let* size = size_of_postcard ctx st in
     let* align = size_of_postcard ctx st in
     let* ptr_metadata = constant_expr_of_postcard ctx st in
     let* src = global_source_of_postcard ctx st in
     let* global_kind = global_kind_of_postcard ctx st in
     let* value = constant_expr_of_postcard ctx st in
     Ok
       ({
          def_id;
          item_meta;
          generics;
          ty;
          size;
          align;
          ptr_metadata;
          src;
          global_kind;
          value;
        }
         : global_decl))

and global_kind_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (global_kind, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 ->
         let* is_mut = bool_of_postcard ctx st in
         let* is_safe = bool_of_postcard ctx st in
         let* is_thread_local = bool_of_postcard ctx st in
         Ok (Static (is_mut, is_safe, is_thread_local))
     | 1 -> Ok NamedConst
     | 2 -> Ok AnonConst
     | 3 -> Ok VTableGlobal
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
         let* self_ty = ty_of_postcard ctx st in
         let* trait_ref = trait_decl_ref_of_postcard ctx st in
         let* impl_ref = option_of_postcard trait_impl_ref_of_postcard ctx st in
         Ok (VTableInstanceGlobal (self_ty, trait_ref, impl_ref))
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and rustc_ident_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (rustc_ident, string) result =
  combine_error_msgs st __FUNCTION__
    (let* name = string_of_postcard ctx st in
     let* span = span_of_postcard ctx st in
     Ok ({ name; span } : rustc_ident))

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

and impl_restriction_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (impl_restriction, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 -> Ok Unrestricted
     | 1 ->
         let* _0 = name_of_postcard ctx st in
         Ok (Restricted _0)
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and implements_marker_traits_of_postcard (ctx : of_postcard_ctx)
    (st : postcard_state) : (implements_marker_traits, string) result =
  combine_error_msgs st __FUNCTION__
    (let* is_sized = bool_of_postcard ctx st in
     let* is_send = bool_of_postcard ctx st in
     let* is_sync = bool_of_postcard ctx st in
     let* is_freeze = bool_of_postcard ctx st in
     let* is_unpin = bool_of_postcard ctx st in
     Ok
       ({ is_sized; is_send; is_sync; is_freeze; is_unpin }
         : implements_marker_traits))

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

and inhabited_predicate_of_postcard (ctx : of_postcard_ctx)
    (st : postcard_state) : (inhabited_predicate, string) result =
  combine_error_msgs st __FUNCTION__
    (dedup_val_of_postcard ctx.inhabited_predicate_dedup_tbl
       inhabited_predicate_kind_of_postcard ctx st)

and inhabited_predicate_kind_of_postcard (ctx : of_postcard_ctx)
    (st : postcard_state) : (inhabited_predicate_kind, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 -> Ok InhabitedPredicateTrue
     | 1 -> Ok InhabitedPredicateFalse
     | 2 ->
         let* _0 = constant_expr_of_postcard ctx st in
         Ok (InhabitedPredicateConstIsZero _0)
     | 3 ->
         let* _0 = ty_of_postcard ctx st in
         Ok (InhabitedPredicateGenericType _0)
     | 4 ->
         let* _0 = list_of_postcard inhabited_predicate_of_postcard ctx st in
         Ok (InhabitedPredicateAnd _0)
     | 5 ->
         let* _0 = list_of_postcard inhabited_predicate_of_postcard ctx st in
         Ok (InhabitedPredicateOr _0)
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

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
     let* started_from = bool_of_postcard ctx st in
     let* is_extern = bool_of_postcard ctx st in
     let* opacity = item_opacity_of_postcard ctx st in
     let* lang_item = option_of_postcard rustc_lang_item_of_postcard ctx st in
     let* diagnostic_item = option_of_postcard string_of_postcard ctx st in
     let* has_errors = bool_of_postcard ctx st in
     Ok
       ({
          name;
          span;
          source_text;
          attr_info;
          is_local;
          started_from;
          is_extern;
          opacity;
          lang_item;
          diagnostic_item;
          has_errors;
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
     | 7 -> Ok RustcLangItemRawEq
     | 8 -> Ok RustcLangItemCompareBytes
     | 9 -> Ok RustcLangItemStructuralPeq
     | 10 -> Ok RustcLangItemDebug
     | 11 -> Ok RustcLangItemCopy
     | 12 -> Ok RustcLangItemClone
     | 13 -> Ok RustcLangItemCloneFn
     | 14 -> Ok RustcLangItemCloneFromFn
     | 15 -> Ok RustcLangItemUseCloned
     | 16 -> Ok RustcLangItemTrivialClone
     | 17 -> Ok RustcLangItemSync
     | 18 -> Ok RustcLangItemSend
     | 19 -> Ok RustcLangItemDiscriminantKind
     | 20 -> Ok RustcLangItemDiscriminant
     | 21 -> Ok RustcLangItemPointeeTrait
     | 22 -> Ok RustcLangItemMetadata
     | 23 -> Ok RustcLangItemDynMetadata
     | 24 -> Ok RustcLangItemNonNull
     | 25 -> Ok RustcLangItemFreeze
     | 26 -> Ok RustcLangItemUnsafeUnpin
     | 27 -> Ok RustcLangItemFnPtrTrait
     | 28 -> Ok RustcLangItemFnAddrTrait
     | 29 -> Ok RustcLangItemFnAddrAsPtr
     | 30 -> Ok RustcLangItemFnAddrAddrFn
     | 31 -> Ok RustcLangItemFnPtrFromPtr
     | 32 -> Ok RustcLangItemCode
     | 33 -> Ok RustcLangItemDrop
     | 34 -> Ok RustcLangItemForget
     | 35 -> Ok RustcLangItemDestruct
     | 36 -> Ok RustcLangItemAsyncDrop
     | 37 -> Ok RustcLangItemAsyncDropInPlace
     | 38 -> Ok RustcLangItemCoerceUnsized
     | 39 -> Ok RustcLangItemDispatchFromDyn
     | 40 -> Ok RustcLangItemTryAsDyn
     | 41 -> Ok RustcLangItemTransmuteOpts
     | 42 -> Ok RustcLangItemTransmuteTrait
     | 43 -> Ok RustcLangItemAdd
     | 44 -> Ok RustcLangItemSub
     | 45 -> Ok RustcLangItemMul
     | 46 -> Ok RustcLangItemDiv
     | 47 -> Ok RustcLangItemRem
     | 48 -> Ok RustcLangItemNeg
     | 49 -> Ok RustcLangItemNot
     | 50 -> Ok RustcLangItemBitXor
     | 51 -> Ok RustcLangItemBitAnd
     | 52 -> Ok RustcLangItemBitOr
     | 53 -> Ok RustcLangItemShl
     | 54 -> Ok RustcLangItemShr
     | 55 -> Ok RustcLangItemAddAssign
     | 56 -> Ok RustcLangItemSubAssign
     | 57 -> Ok RustcLangItemMulAssign
     | 58 -> Ok RustcLangItemDivAssign
     | 59 -> Ok RustcLangItemRemAssign
     | 60 -> Ok RustcLangItemBitXorAssign
     | 61 -> Ok RustcLangItemBitAndAssign
     | 62 -> Ok RustcLangItemBitOrAssign
     | 63 -> Ok RustcLangItemShlAssign
     | 64 -> Ok RustcLangItemShrAssign
     | 65 -> Ok RustcLangItemIndex
     | 66 -> Ok RustcLangItemIndexMut
     | 67 -> Ok RustcLangItemUnsafeCell
     | 68 -> Ok RustcLangItemCovariantUnsafeCell
     | 69 -> Ok RustcLangItemUnsafePinned
     | 70 -> Ok RustcLangItemVaArgSafe
     | 71 -> Ok RustcLangItemVaList
     | 72 -> Ok RustcLangItemComplex
     | 73 -> Ok RustcLangItemPpcF128
     | 74 -> Ok RustcLangItemX87F80
     | 75 -> Ok RustcLangItemX87F80Raw
     | 76 -> Ok RustcLangItemDeref
     | 77 -> Ok RustcLangItemDerefMut
     | 78 -> Ok RustcLangItemDerefPure
     | 79 -> Ok RustcLangItemDerefTarget
     | 80 -> Ok RustcLangItemReceiver
     | 81 -> Ok RustcLangItemReceiverTarget
     | 82 -> Ok RustcLangItemLegacyReceiver
     | 83 -> Ok RustcLangItemFn
     | 84 -> Ok RustcLangItemFnMut
     | 85 -> Ok RustcLangItemFnOnce
     | 86 -> Ok RustcLangItemFnStatic
     | 87 -> Ok RustcLangItemAsyncFn
     | 88 -> Ok RustcLangItemAsyncFnMut
     | 89 -> Ok RustcLangItemAsyncFnOnce
     | 90 -> Ok RustcLangItemAsyncFnOnceOutput
     | 91 -> Ok RustcLangItemCallOnceFuture
     | 92 -> Ok RustcLangItemCallRefFuture
     | 93 -> Ok RustcLangItemAsyncFnKindHelper
     | 94 -> Ok RustcLangItemAsyncFnKindUpvars
     | 95 -> Ok RustcLangItemFnOnceOutput
     | 96 -> Ok RustcLangItemIterator
     | 97 -> Ok RustcLangItemFusedIterator
     | 98 -> Ok RustcLangItemFuture
     | 99 -> Ok RustcLangItemFutureOutput
     | 100 -> Ok RustcLangItemAsyncIterator
     | 101 -> Ok RustcLangItemCoroutineState
     | 102 -> Ok RustcLangItemCoroutine
     | 103 -> Ok RustcLangItemCoroutineReturn
     | 104 -> Ok RustcLangItemCoroutineYield
     | 105 -> Ok RustcLangItemCoroutineResume
     | 106 -> Ok RustcLangItemUnpin
     | 107 -> Ok RustcLangItemPin
     | 108 -> Ok RustcLangItemMove
     | 109 -> Ok RustcLangItemOrderingEnum
     | 110 -> Ok RustcLangItemPartialEq
     | 111 -> Ok RustcLangItemEq
     | 112 -> Ok RustcLangItemPartialOrd
     | 113 -> Ok RustcLangItemCVoid
     | 114 -> Ok RustcLangItemF16B
     | 115 -> Ok RustcLangItemTypeKind
     | 116 -> Ok RustcLangItemTypeGeneric
     | 117 -> Ok RustcLangItemTypeId
     | 118 -> Ok RustcLangItemPanic
     | 119 -> Ok RustcLangItemPanicNounwind
     | 120 -> Ok RustcLangItemPanicFmt
     | 121 -> Ok RustcLangItemPanicDisplay
     | 122 -> Ok RustcLangItemConstPanicFmt
     | 123 -> Ok RustcLangItemPanicBoundsCheck
     | 124 -> Ok RustcLangItemPanicMisalignedPointerDereference
     | 125 -> Ok RustcLangItemPanicInfo
     | 126 -> Ok RustcLangItemPanicLocation
     | 127 -> Ok RustcLangItemPanicImpl
     | 128 -> Ok RustcLangItemPanicCannotUnwind
     | 129 -> Ok RustcLangItemPanicInCleanup
     | 130 -> Ok RustcLangItemPanicAddOverflow
     | 131 -> Ok RustcLangItemPanicSubOverflow
     | 132 -> Ok RustcLangItemPanicMulOverflow
     | 133 -> Ok RustcLangItemPanicDivOverflow
     | 134 -> Ok RustcLangItemPanicRemOverflow
     | 135 -> Ok RustcLangItemPanicNegOverflow
     | 136 -> Ok RustcLangItemPanicShrOverflow
     | 137 -> Ok RustcLangItemPanicShlOverflow
     | 138 -> Ok RustcLangItemPanicDivZero
     | 139 -> Ok RustcLangItemPanicRemZero
     | 140 -> Ok RustcLangItemPanicCoroutineResumed
     | 141 -> Ok RustcLangItemPanicAsyncFnResumed
     | 142 -> Ok RustcLangItemPanicAsyncGenFnResumed
     | 143 -> Ok RustcLangItemPanicGenFnNone
     | 144 -> Ok RustcLangItemPanicCoroutineResumedPanic
     | 145 -> Ok RustcLangItemPanicAsyncFnResumedPanic
     | 146 -> Ok RustcLangItemPanicAsyncGenFnResumedPanic
     | 147 -> Ok RustcLangItemPanicGenFnNonePanic
     | 148 -> Ok RustcLangItemPanicNullPointerDereference
     | 149 -> Ok RustcLangItemPanicNullReferenceConstructed
     | 150 -> Ok RustcLangItemPanicInvalidEnumConstruction
     | 151 -> Ok RustcLangItemPanicCoroutineResumedDrop
     | 152 -> Ok RustcLangItemPanicAsyncFnResumedDrop
     | 153 -> Ok RustcLangItemPanicAsyncGenFnResumedDrop
     | 154 -> Ok RustcLangItemPanicGenFnNoneDrop
     | 155 -> Ok RustcLangItemBeginPanic
     | 156 -> Ok RustcLangItemFormatArgument
     | 157 -> Ok RustcLangItemFormatArguments
     | 158 -> Ok RustcLangItemDropGlue
     | 159 -> Ok RustcLangItemAllocLayout
     | 160 -> Ok RustcLangItemStart
     | 161 -> Ok RustcLangItemEhPersonality
     | 162 -> Ok RustcLangItemCompilerMove
     | 163 -> Ok RustcLangItemCompilerCopy
     | 164 -> Ok RustcLangItemOwnedBox
     | 165 -> Ok RustcLangItemGlobalAlloc
     | 166 -> Ok RustcLangItemPhantomData
     | 167 -> Ok RustcLangItemManuallyDrop
     | 168 -> Ok RustcLangItemMaybeDangling
     | 169 -> Ok RustcLangItemBikeshedGuaranteedNoDrop
     | 170 -> Ok RustcLangItemMaybeUninit
     | 171 -> Ok RustcLangItemTermination
     | 172 -> Ok RustcLangItemTry
     | 173 -> Ok RustcLangItemTuple
     | 174 -> Ok RustcLangItemSliceLen
     | 175 -> Ok RustcLangItemTryTraitFromResidual
     | 176 -> Ok RustcLangItemTryTraitFromOutput
     | 177 -> Ok RustcLangItemTryTraitBranch
     | 178 -> Ok RustcLangItemTryTraitFromYeet
     | 179 -> Ok RustcLangItemResidualIntoTryType
     | 180 -> Ok RustcLangItemCoercePointeeValidated
     | 181 -> Ok RustcLangItemConstParamTy
     | 182 -> Ok RustcLangItemPoll
     | 183 -> Ok RustcLangItemPollReady
     | 184 -> Ok RustcLangItemPollPending
     | 185 -> Ok RustcLangItemAsyncGenReady
     | 186 -> Ok RustcLangItemAsyncGenPending
     | 187 -> Ok RustcLangItemAsyncGenFinished
     | 188 -> Ok RustcLangItemResumeTy
     | 189 -> Ok RustcLangItemGetContext
     | 190 -> Ok RustcLangItemContext
     | 191 -> Ok RustcLangItemFuturePoll
     | 192 -> Ok RustcLangItemAsyncIteratorPollNext
     | 193 -> Ok RustcLangItemIntoAsyncIterIntoIter
     | 194 -> Ok RustcLangItemOption
     | 195 -> Ok RustcLangItemOptionSome
     | 196 -> Ok RustcLangItemOptionNone
     | 197 -> Ok RustcLangItemResultOk
     | 198 -> Ok RustcLangItemResultErr
     | 199 -> Ok RustcLangItemControlFlowContinue
     | 200 -> Ok RustcLangItemControlFlowBreak
     | 201 -> Ok RustcLangItemIntoFutureIntoFuture
     | 202 -> Ok RustcLangItemIntoIterIntoIter
     | 203 -> Ok RustcLangItemIteratorNext
     | 204 -> Ok RustcLangItemPinNewUnchecked
     | 205 -> Ok RustcLangItemRangeFrom
     | 206 -> Ok RustcLangItemRangeFull
     | 207 -> Ok RustcLangItemRangeInclusiveStruct
     | 208 -> Ok RustcLangItemRangeInclusiveNew
     | 209 -> Ok RustcLangItemRange
     | 210 -> Ok RustcLangItemRangeToInclusive
     | 211 -> Ok RustcLangItemRangeTo
     | 212 -> Ok RustcLangItemRangeMax
     | 213 -> Ok RustcLangItemRangeMin
     | 214 -> Ok RustcLangItemRangeSub
     | 215 -> Ok RustcLangItemRangeFromCopy
     | 216 -> Ok RustcLangItemRangeCopy
     | 217 -> Ok RustcLangItemRangeInclusiveCopy
     | 218 -> Ok RustcLangItemRangeToInclusiveCopy
     | 219 -> Ok RustcLangItemString
     | 220 -> Ok RustcLangItemCStr
     | 221 -> Ok RustcLangItemContractBuildCheckEnsures
     | 222 -> Ok RustcLangItemContractCheckRequires
     | 223 -> Ok RustcLangItemDefaultTrait4
     | 224 -> Ok RustcLangItemDefaultTrait3
     | 225 -> Ok RustcLangItemDefaultTrait2
     | 226 -> Ok RustcLangItemDefaultTrait1
     | 227 -> Ok RustcLangItemContractCheckEnsures
     | 228 -> Ok RustcLangItemReborrow
     | 229 -> Ok RustcLangItemCoerceShared
     | 230 -> Ok RustcLangItemFieldRepresentingType
     | 231 -> Ok RustcLangItemField
     | 232 -> Ok RustcLangItemFieldBase
     | 233 -> Ok RustcLangItemFieldType
     | 234 -> Ok RustcLangItemFieldOffset
     | 235 -> Ok RustcLangItemFrom
     | 236 -> Ok RustcLangItemFromFn
     | 237 -> Ok RustcLangItemFnPtr
     | 238 -> Ok RustcLangItemDynTrait
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and layout_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (layout, string) result =
  combine_error_msgs st __FUNCTION__
    (let* size = size_of_postcard ctx st in
     let* align = size_of_postcard ctx st in
     let* discriminator = option_of_postcard discriminator_of_postcard ctx st in
     let* inhabited = inhabited_predicate_of_postcard ctx st in
     let* variant_layouts =
       index_vec_of_postcard variant_id_of_postcard
         (option_of_postcard variant_layout_of_postcard)
         ctx st
     in
     let* union_chunks =
       option_of_postcard
         (list_of_postcard (pair_of_postcard u64_of_postcard u64_of_postcard))
         ctx st
     in
     let* repr = repr_options_of_postcard ctx st in
     Ok
       ({
          size;
          align;
          discriminator;
          inhabited;
          variant_layouts;
          union_chunks;
          repr;
        }
         : layout))

and rustc_linkage_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (rustc_linkage, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 -> Ok RustcLinkageAvailableExternally
     | 1 -> Ok RustcLinkageExternalWeak
     | 2 -> Ok RustcLinkageExternal
     | 3 -> Ok RustcLinkageInternal
     | 4 -> Ok RustcLinkageLinkOnceAny
     | 5 -> Ok RustcLinkageLinkOnceODR
     | 6 -> Ok RustcLinkageWeakAny
     | 7 -> Ok RustcLinkageWeakODR
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and linked_extern_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (linked_extern, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 ->
         let* _0 = fun_decl_ref_of_postcard ctx st in
         Ok (StronglyLinked _0)
     | 1 ->
         let* _0 = list_of_postcard fun_decl_ref_of_postcard ctx st in
         Ok (WeaklyLinked _0)
     | 2 ->
         let* _0 = fun_decl_ref_of_postcard ctx st in
         Ok (AllocatorShim _0)
     | 3 -> Ok Unlinked
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and local_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (local, string) result =
  combine_error_msgs st __FUNCTION__
    (let* index = local_id_of_postcard ctx st in
     let* name = option_of_postcard string_of_postcard ctx st in
     let* span = span_of_postcard ctx st in
     let* local_ty = ty_of_postcard ctx st in
     let* is_mutable = bool_of_postcard ctx st in
     let* borrowck_constraints =
       list_of_postcard place_type_constraint_of_postcard ctx st
     in
     let* drop_flag_for = option_of_postcard place_of_postcard ctx st in
     Ok
       ({
          index;
          name;
          span;
          local_ty;
          is_mutable;
          borrowck_constraints;
          drop_flag_for;
        }
         : local))

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

and name_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (name, string) result =
  combine_error_msgs st __FUNCTION__
    (list_of_postcard path_elem_of_postcard ctx st)

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
     | 0 ->
         let* _0 = size_expr_of_postcard ctx st in
         Ok (AtOffset _0)
     | 1 ->
         let* _0 = size_expr_of_postcard ctx st in
         Ok (GuaranteedAlignment _0)
     | 2 ->
         let* _0 = field_predecessor_of_postcard ctx st in
         Ok (ReprCField _0)
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

and rustc_os_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (rustc_os, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 -> Ok RustcOsAix
     | 1 -> Ok RustcOsAmdHsa
     | 2 -> Ok RustcOsAndroid
     | 3 -> Ok RustcOsCuda
     | 4 -> Ok RustcOsCygwin
     | 5 -> Ok RustcOsDragonfly
     | 6 -> Ok RustcOsEmscripten
     | 7 -> Ok RustcOsEspIdf
     | 8 -> Ok RustcOsFreeBsd
     | 9 -> Ok RustcOsFuchsia
     | 10 -> Ok RustcOsHaiku
     | 11 -> Ok RustcOsHelenOs
     | 12 -> Ok RustcOsHermit
     | 13 -> Ok RustcOsHorizon
     | 14 -> Ok RustcOsHurd
     | 15 -> Ok RustcOsHyperlight
     | 16 -> Ok RustcOsIllumos
     | 17 -> Ok RustcOsIOs
     | 18 -> Ok RustcOsL4Re
     | 19 -> Ok RustcOsLinux
     | 20 -> Ok RustcOsLynxOs178
     | 21 -> Ok RustcOsMacOs
     | 22 -> Ok RustcOsManagarm
     | 23 -> Ok RustcOsMotor
     | 24 -> Ok RustcOsNetBsd
     | 25 -> Ok RustcOsNone
     | 26 -> Ok RustcOsNto
     | 27 -> Ok RustcOsNuttX
     | 28 -> Ok RustcOsOpenBsd
     | 29 -> Ok RustcOsPs3
     | 30 -> Ok RustcOsPsp
     | 31 -> Ok RustcOsPsx
     | 32 -> Ok RustcOsQnx
     | 33 -> Ok RustcOsQtee
     | 34 -> Ok RustcOsQurt
     | 35 -> Ok RustcOsRedox
     | 36 -> Ok RustcOsRtems
     | 37 -> Ok RustcOsSerenity
     | 38 -> Ok RustcOsSolaris
     | 39 -> Ok RustcOsSolidAsp3
     | 40 -> Ok RustcOsTeeOs
     | 41 -> Ok RustcOsTrusty
     | 42 -> Ok RustcOsTvOs
     | 43 -> Ok RustcOsUefi
     | 44 -> Ok RustcOsVexOs
     | 45 -> Ok RustcOsVisionOs
     | 46 -> Ok RustcOsVita
     | 47 -> Ok RustcOsVxWorks
     | 48 -> Ok RustcOsWasi
     | 49 -> Ok RustcOsWatchOs
     | 50 -> Ok RustcOsWindows
     | 51 -> Ok RustcOsXous
     | 52 -> Ok RustcOsZkvm
     | 53 -> Ok RustcOsUnknown
     | 54 ->
         let* _0 = string_of_postcard ctx st in
         Ok (RustcOsOther _0)
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
         let* _1 = disambiguator_of_postcard ctx st in
         Ok (PeBuiltin (_0, _1))
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
     | 2 -> Ok Simd
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
       option_of_postcard integer_type_of_postcard ctx st
     in
     Ok
       ({ repr_algo; align_modif; transparent; explicit_discr_type }
         : repr_options))

and runtime_checks_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (runtime_checks, string) result =
  combine_error_msgs st __FUNCTION__
    (let* ub_checks = bool_of_postcard ctx st in
     let* overflow_checks = bool_of_postcard ctx st in
     let* contract_checks = bool_of_postcard ctx st in
     Ok ({ ub_checks; overflow_checks; contract_checks } : runtime_checks))

and rustc_rustc_version_of_postcard (ctx : of_postcard_ctx)
    (st : postcard_state) : (rustc_rustc_version, string) result =
  combine_error_msgs st __FUNCTION__
    (let* major = u16_of_postcard ctx st in
     let* minor = u16_of_postcard ctx st in
     let* patch = u16_of_postcard ctx st in
     Ok ({ major; minor; patch } : rustc_rustc_version))

and size_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (size, string) result =
  combine_error_msgs st __FUNCTION__
    (let* chosen = option_of_postcard size_expr_of_postcard ctx st in
     let* guarantee = option_of_postcard size_expr_of_postcard ctx st in
     Ok ({ chosen; guarantee } : size))

and size_expr_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (size_expr, string) result =
  combine_error_msgs st __FUNCTION__
    (dedup_val_of_postcard ctx.size_expr_dedup_tbl size_expr_kind_of_postcard
       ctx st)

and size_expr_kind_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (size_expr_kind, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 ->
         let* _0 = constant_expr_of_postcard ctx st in
         Ok (SizeExprConstant _0)
     | 1 ->
         let* _0 = metadata_value_of_postcard ctx st in
         Ok (SizeExprFromMetadata _0)
     | 2 ->
         let* _0 = list_of_postcard size_expr_of_postcard ctx st in
         Ok (SizeExprMax _0)
     | 3 ->
         let* _0 = list_of_postcard size_expr_of_postcard ctx st in
         Ok (SizeExprMin _0)
     | 4 ->
         let* _0 = size_expr_of_postcard ctx st in
         let* _1 = size_expr_of_postcard ctx st in
         Ok (SizeExprPlus (_0, _1))
     | 5 ->
         let* _0 = size_expr_of_postcard ctx st in
         let* _1 = constant_expr_of_postcard ctx st in
         Ok (SizeExprScale (_0, _1))
     | 6 ->
         let* _0 = size_expr_of_postcard ctx st in
         Ok (SizeExprAtLeast _0)
     | 7 ->
         let* base = size_expr_of_postcard ctx st in
         let* target_align = size_expr_of_postcard ctx st in
         Ok (SizeExprAlignTo (base, target_align))
     | 8 ->
         let* ty = ty_of_postcard ctx st in
         let* then_size = size_expr_of_postcard ctx st in
         let* else_size = size_expr_of_postcard ctx st in
         Ok (SizeExprIfInhabited (ty, then_size, else_size))
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and target_info_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (target_info, string) result =
  combine_error_msgs st __FUNCTION__
    (let* arch = rustc_arch_of_postcard ctx st in
     let* vendor = string_of_postcard ctx st in
     let* os = rustc_os_of_postcard ctx st in
     let* env = rustc_env_of_postcard ctx st in
     let* cfg_abi = rustc_cfg_abi_of_postcard ctx st in
     let* families = list_of_postcard string_of_postcard ctx st in
     let* binary_format = rustc_binary_format_of_postcard ctx st in
     let* target_pointer_size = u64_of_postcard ctx st in
     let* is_little_endian = bool_of_postcard ctx st in
     let* c_enum_smallest_repr_ty = int_ty_of_postcard ctx st in
     let* primitive_alignments =
       index_map_of_postcard scalar_type_of_postcard u64_of_postcard
         int_of_postcard ctx st
     in
     Ok
       ({
          arch;
          vendor;
          os;
          env;
          cfg_abi;
          families;
          binary_format;
          target_pointer_size;
          is_little_endian;
          c_enum_smallest_repr_ty;
          primitive_alignments;
        }
         : target_info))

and target_layouts_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (target_layouts, string) result =
  combine_error_msgs st __FUNCTION__
    (index_map_of_postcard string_of_postcard layout_of_postcard int_of_postcard
       ctx st)

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
     let* is_unsafe = bool_of_postcard ctx st in
     let* impl_restriction = impl_restriction_of_postcard ctx st in
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
          is_unsafe;
          impl_restriction;
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
     let* is_negative = bool_of_postcard ctx st in
     let* is_unsafe = bool_of_postcard ctx st in
     let* generics = generic_params_of_postcard ctx st in
     let* implied_trait_refs =
       index_vec_of_postcard trait_clause_id_of_postcard
         poly_trait_ref_of_postcard ctx st
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
     let* vtable = v_table_decl_of_postcard ctx st in
     Ok
       ({
          def_id;
          item_meta;
          src;
          impl_trait;
          is_negative;
          is_unsafe;
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
     | 2 -> Ok BuiltinTraitImpl
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
     let* preset = option_of_postcard preset_of_postcard ctx st in
     let* target_information =
       index_map_of_postcard string_of_postcard target_info_of_postcard
         int_of_postcard ctx st
     in
     let* runtime_checks = runtime_checks_of_postcard ctx st in
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
          preset;
          target_information;
          runtime_checks;
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
     let* layout = target_layouts_of_postcard ctx st in
     let* monomorphic_layouts =
       index_map_of_postcard generic_args_of_postcard target_layouts_of_postcard
         int_of_postcard ctx st
     in
     let* ptr_metadata = ptr_metadata_of_postcard ctx st in
     let* marker_traits =
       option_of_postcard
         (box_of_postcard implements_marker_traits_of_postcard)
         ctx st
     in
     Ok
       ({
          def_id;
          item_meta;
          generics;
          src;
          kind;
          layout;
          monomorphic_layouts;
          ptr_metadata;
          marker_traits;
        }
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
         let* info = coroutine_info_of_postcard ctx st in
         Ok (CoroutineType info)
     | 3 ->
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
     | 4 ->
         let* _0 = builtin_adt_of_postcard ctx st in
         Ok (BuiltinType _0)
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and v_table_decl_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (v_table_decl, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 -> Ok NotDynCompatible
     | 1 -> Ok Lazy
     | 2 ->
         let* _0 = global_decl_ref_of_postcard ctx st in
         Ok (VTableInstance _0)
     | 3 ->
         let* _0 = string_of_postcard ctx st in
         Ok (UnknownVTable _0)
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
         let* _1 = list_of_postcard field_id_of_postcard ctx st in
         Ok (VTableMethod (_0, _1))
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
     let* discriminant = integer_value_of_postcard ctx st in
     Ok ({ id; span; attr_info; variant_name; fields; discriminant } : variant))

and variant_layout_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (variant_layout, string) result =
  combine_error_msgs st __FUNCTION__
    (let* field_offsets =
       index_vec_of_postcard field_id_of_postcard offset_expr_of_postcard ctx st
     in
     let* inhabited = inhabited_predicate_of_postcard ctx st in
     let* tagger =
       list_of_postcard
         (pair_of_postcard u64_of_postcard integer_value_of_postcard)
         ctx st
     in
     Ok ({ field_offsets; inhabited; tagger } : variant_layout))
