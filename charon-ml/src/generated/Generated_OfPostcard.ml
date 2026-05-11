(** WARNING: this file is partially auto-generated. Do not edit `OfPostcard.ml`
    by hand. Edit `templates/OfPostcard.ml` instead, or improve the code
    generation tool so avoid the need for hand-writing things.

    `templates/OfPostcard.ml` contains the manual definitions and some `(*
    __REPLACEn__ *)` comments. These comments are replaced by auto-generated
    definitions by running `make generate-ml` in the crate root. The
    code-generation code is in `charon/src/bin/generate-ml`. *)

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
}

let empty_of_postcard_ctx : of_postcard_ctx =
  {
    id_to_file_map = FileTbl.create 8;
    ty_hashcons_map = ref HashConsId.Map.empty;
    tref_hashcons_map = ref HashConsId.Map.empty;
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

and abort_kind_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (abort_kind, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 ->
         let* x_0 = option_of_postcard name_of_postcard ctx st in
         Ok (Panic x_0)
     | 1 -> Ok UndefinedBehavior
     | 2 -> Ok UnwindTerminate
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and aggregate_kind_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (aggregate_kind, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 ->
         let* x_0 = type_decl_ref_of_postcard ctx st in
         let* x_1 = option_of_postcard variant_id_of_postcard ctx st in
         let* x_2 = option_of_postcard field_id_of_postcard ctx st in
         Ok (AggregatedAdt (x_0, x_1, x_2))
     | 1 ->
         let* x_0 = ty_of_postcard ctx st in
         let* x_1 = box_of_postcard constant_expr_of_postcard ctx st in
         Ok (AggregatedArray (x_0, x_1))
     | 2 ->
         let* x_0 = ty_of_postcard ctx st in
         let* x_1 = ref_kind_of_postcard ctx st in
         Ok (AggregatedRawPtr (x_0, x_1))
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
         let* x_0 = overflow_mode_of_postcard ctx st in
         Ok (Add x_0)
     | 10 ->
         let* x_0 = overflow_mode_of_postcard ctx st in
         Ok (Sub x_0)
     | 11 ->
         let* x_0 = overflow_mode_of_postcard ctx st in
         Ok (Mul x_0)
     | 12 ->
         let* x_0 = overflow_mode_of_postcard ctx st in
         Ok (Div x_0)
     | 13 ->
         let* x_0 = overflow_mode_of_postcard ctx st in
         Ok (Rem x_0)
     | 14 -> Ok AddChecked
     | 15 -> Ok SubChecked
     | 16 -> Ok MulChecked
     | 17 ->
         let* x_0 = overflow_mode_of_postcard ctx st in
         Ok (Shl x_0)
     | 18 ->
         let* x_0 = overflow_mode_of_postcard ctx st in
         Ok (Shr x_0)
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
         let* x_0 = trait_decl_id_of_postcard ctx st in
         let* x_1 = trait_item_name_of_postcard ctx st in
         Ok (BKTraitType (x_0, x_1))
     | 1 ->
         let* x_0 = trait_decl_id_of_postcard ctx st in
         let* x_1 = trait_item_name_of_postcard ctx st in
         Ok (BKTraitMethod (x_0, x_1))
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
         let* x_0 = binop_of_postcard ctx st in
         let* x_1 = operand_of_postcard ctx st in
         let* x_2 = operand_of_postcard ctx st in
         Ok (Overflow (x_0, x_1, x_2))
     | 2 ->
         let* x_0 = operand_of_postcard ctx st in
         Ok (OverflowNeg x_0)
     | 3 ->
         let* x_0 = operand_of_postcard ctx st in
         Ok (DivisionByZero x_0)
     | 4 ->
         let* x_0 = operand_of_postcard ctx st in
         Ok (RemainderByZero x_0)
     | 5 ->
         let* required = operand_of_postcard ctx st in
         let* found = operand_of_postcard ctx st in
         Ok (MisalignedPointerDereference (required, found))
     | 6 -> Ok NullPointerDereference
     | 7 ->
         let* x_0 = operand_of_postcard ctx st in
         Ok (InvalidEnumConstruction x_0)
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and builtin_fun_id_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (builtin_fun_id, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 -> Ok BoxNew
     | 1 -> Ok ArrayToSliceShared
     | 2 -> Ok ArrayToSliceMut
     | 3 -> Ok ArrayRepeat
     | 4 ->
         let* x_0 = builtin_index_op_of_postcard ctx st in
         Ok (Index x_0)
     | 5 ->
         let* x_0 = ref_kind_of_postcard ctx st in
         Ok (PtrFromParts x_0)
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and builtin_impl_data_of_postcard (ctx : of_postcard_ctx) (st : postcard_state)
    : (builtin_impl_data, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 -> Ok BuiltinSized
     | 1 -> Ok BuiltinMetaSized
     | 2 -> Ok BuiltinTuple
     | 3 -> Ok BuiltinPointee
     | 4 -> Ok BuiltinDiscriminantKind
     | 5 -> Ok BuiltinAuto
     | 6 -> Ok BuiltinNoopDestruct
     | 7 -> Ok BuiltinUntrackedDestruct
     | 8 -> Ok BuiltinFn
     | 9 -> Ok BuiltinFnMut
     | 10 -> Ok BuiltinFnOnce
     | 11 -> Ok BuiltinCopy
     | 12 -> Ok BuiltinClone
     | 13 -> Ok BuiltinRemovedAdtClause
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and builtin_index_op_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (builtin_index_op, string) result =
  combine_error_msgs st __FUNCTION__
    (let* is_array = bool_of_postcard ctx st in
     let* mutability = ref_kind_of_postcard ctx st in
     let* is_range = bool_of_postcard ctx st in
     Ok ({ is_array; mutability; is_range } : builtin_index_op))

and builtin_ty_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (builtin_ty, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 -> Ok TBox
     | 1 -> Ok TStr
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and byte_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (byte, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 -> Ok Uninit
     | 1 ->
         let* x_0 = u8_of_postcard ctx st in
         Ok (Value x_0)
     | 2 ->
         let* x_0 = provenance_of_postcard ctx st in
         let* x_1 = u8_of_postcard ctx st in
         Ok (Provenance (x_0, x_1))
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
         let* x_0 = literal_type_of_postcard ctx st in
         let* x_1 = literal_type_of_postcard ctx st in
         Ok (CastScalar (x_0, x_1))
     | 1 ->
         let* x_0 = ty_of_postcard ctx st in
         let* x_1 = ty_of_postcard ctx st in
         Ok (CastRawPtr (x_0, x_1))
     | 2 ->
         let* x_0 = ty_of_postcard ctx st in
         let* x_1 = ty_of_postcard ctx st in
         Ok (CastFnPtr (x_0, x_1))
     | 3 ->
         let* x_0 = ty_of_postcard ctx st in
         let* x_1 = ty_of_postcard ctx st in
         let* x_2 = unsizing_metadata_of_postcard ctx st in
         Ok (CastUnsize (x_0, x_1, x_2))
     | 4 ->
         let* x_0 = ty_of_postcard ctx st in
         let* x_1 = ty_of_postcard ctx st in
         Ok (CastTransmute (x_0, x_1))
     | 5 ->
         let* x_0 = ty_of_postcard ctx st in
         let* x_1 = ty_of_postcard ctx st in
         Ok (CastConcretize (x_0, x_1))
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
    (let* kind = constant_expr_kind_of_postcard ctx st in
     let* ty = ty_of_postcard ctx st in
     Ok ({ kind; ty } : constant_expr))

and constant_expr_kind_of_postcard (ctx : of_postcard_ctx) (st : postcard_state)
    : (constant_expr_kind, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 ->
         let* x_0 = literal_of_postcard ctx st in
         Ok (CLiteral x_0)
     | 1 ->
         let* x_0 = option_of_postcard variant_id_of_postcard ctx st in
         let* x_1 = list_of_postcard constant_expr_of_postcard ctx st in
         Ok (CAdt (x_0, x_1))
     | 2 ->
         let* x_0 = list_of_postcard constant_expr_of_postcard ctx st in
         Ok (CArray x_0)
     | 3 ->
         let* x_0 = global_decl_ref_of_postcard ctx st in
         Ok (CGlobal x_0)
     | 4 ->
         let* x_0 = trait_ref_of_postcard ctx st in
         let* x_1 = trait_item_name_of_postcard ctx st in
         Ok (CTraitConst (x_0, x_1))
     | 5 ->
         let* x_0 = trait_ref_of_postcard ctx st in
         Ok (CVTableRef x_0)
     | 6 ->
         let* x_0 = box_of_postcard constant_expr_of_postcard ctx st in
         let* x_1 = option_of_postcard unsizing_metadata_of_postcard ctx st in
         Ok (CRef (x_0, x_1))
     | 7 ->
         let* x_0 = ref_kind_of_postcard ctx st in
         let* x_1 = box_of_postcard constant_expr_of_postcard ctx st in
         let* x_2 = option_of_postcard unsizing_metadata_of_postcard ctx st in
         Ok (CPtr (x_0, x_1, x_2))
     | 8 ->
         let* x_0 =
           de_bruijn_var_of_postcard const_generic_var_id_of_postcard ctx st
         in
         Ok (CVar x_0)
     | 9 ->
         let* x_0 = fn_ptr_of_postcard ctx st in
         Ok (CFnDef x_0)
     | 10 ->
         let* x_0 = fn_ptr_of_postcard ctx st in
         Ok (CFnPtr x_0)
     | 11 ->
         let* x_0 = big_uint_of_postcard ctx st in
         Ok (CPtrNoProvenance x_0)
     | 12 ->
         let* x_0 = list_of_postcard byte_of_postcard ctx st in
         Ok (CRawMemory x_0)
     | 13 ->
         let* x_0 = string_of_postcard ctx st in
         Ok (COpaque x_0)
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and copy_non_overlapping_of_postcard (ctx : of_postcard_ctx)
    (st : postcard_state) : (copy_non_overlapping, string) result =
  combine_error_msgs st __FUNCTION__
    (let* src = operand_of_postcard ctx st in
     let* dst = operand_of_postcard ctx st in
     let* count = operand_of_postcard ctx st in
     Ok ({ src; dst; count } : copy_non_overlapping))

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
         let* x_0 = de_bruijn_id_of_postcard ctx st in
         let* x_1 = arg0_of_postcard ctx st in
         Ok (Bound (x_0, x_1))
     | 1 ->
         let* x_0 = arg0_of_postcard ctx st in
         Ok (Free x_0)
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

and field_proj_kind_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (field_proj_kind, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 ->
         let* x_0 = type_decl_id_of_postcard ctx st in
         let* x_1 = option_of_postcard variant_id_of_postcard ctx st in
         Ok (ProjAdt (x_0, x_1))
     | 1 ->
         let* x_0 = usize_of_postcard ctx st in
         Ok (ProjTuple x_0)
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

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
         let* x_0 = fn_ptr_of_postcard ctx st in
         Ok (FnOpRegular x_0)
     | 1 ->
         let* x_0 = operand_of_postcard ctx st in
         Ok (FnOpDynamic x_0)
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
         let* x_0 = fun_id_of_postcard ctx st in
         Ok (FunId x_0)
     | 1 ->
         let* x_0 = trait_ref_of_postcard ctx st in
         let* x_1 = trait_item_name_of_postcard ctx st in
         let* x_2 = fun_decl_id_of_postcard ctx st in
         Ok (TraitMethod (x_0, x_1, x_2))
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
         let* x_0 = fun_decl_id_of_postcard ctx st in
         Ok (FRegular x_0)
     | 1 ->
         let* x_0 = builtin_fun_id_of_postcard ctx st in
         Ok (FBuiltin x_0)
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and fun_sig_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (fun_sig, string) result =
  combine_error_msgs st __FUNCTION__
    (let* is_unsafe = bool_of_postcard ctx st in
     let* inputs = list_of_postcard ty_of_postcard ctx st in
     let* output = ty_of_postcard ctx st in
     Ok ({ is_unsafe; inputs; output } : fun_sig))

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
         let* x_0 =
           box_of_postcard (binder_of_postcard ty_of_postcard) ctx st
         in
         Ok (ImplElemTy x_0)
     | 1 ->
         let* x_0 = trait_impl_id_of_postcard ctx st in
         Ok (ImplElemTrait x_0)
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
         let* x_0 = scalar_value_of_postcard ctx st in
         Ok (VScalar x_0)
     | 1 ->
         let* x_0 = float_value_of_postcard ctx st in
         Ok (VFloat x_0)
     | 2 ->
         let* x_0 = bool_of_postcard ctx st in
         Ok (VBool x_0)
     | 3 ->
         let* x_0 = char_of_postcard ctx st in
         Ok (VChar x_0)
     | 4 ->
         let* x_0 = list_of_postcard u8_of_postcard ctx st in
         Ok (VByteStr x_0)
     | 5 ->
         let* x_0 = string_of_postcard ctx st in
         Ok (VStr x_0)
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and literal_type_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (literal_type, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 ->
         let* x_0 = int_ty_of_postcard ctx st in
         Ok (TInt x_0)
     | 1 ->
         let* x_0 = u_int_ty_of_postcard ctx st in
         Ok (TUInt x_0)
     | 2 ->
         let* x_0 = float_type_of_postcard ctx st in
         Ok (TFloat x_0)
     | 3 -> Ok TBool
     | 4 -> Ok TChar
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and loc_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (loc, string) result =
  combine_error_msgs st __FUNCTION__
    (let* line = usize_of_postcard ctx st in
     let* col = usize_of_postcard ctx st in
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
         let* x_0 = type_decl_ref_of_postcard ctx st in
         let* x_1 = option_of_postcard variant_id_of_postcard ctx st in
         let* x_2 = field_id_of_postcard ctx st in
         Ok (OffsetOf (x_0, x_1, x_2))
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
         let* x_0 = place_of_postcard ctx st in
         Ok (Copy x_0)
     | 1 ->
         let* x_0 = place_of_postcard ctx st in
         Ok (Move x_0)
     | 2 ->
         let* x_0 = box_of_postcard constant_expr_of_postcard ctx st in
         Ok (Constant x_0)
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
    (let* x_0 = arg0_of_postcard ctx st in
     let* x_1 = arg1_of_postcard ctx st in
     Ok (x_0, x_1))

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
         let* x_0 = string_of_postcard ctx st in
         let* x_1 = disambiguator_of_postcard ctx st in
         Ok (PeIdent (x_0, x_1))
     | 1 ->
         let* x_0 = impl_elem_of_postcard ctx st in
         Ok (PeImpl x_0)
     | 2 ->
         let* x_0 =
           box_of_postcard (binder_of_postcard generic_args_of_postcard) ctx st
         in
         Ok (PeInstantiated x_0)
     | 3 ->
         let* x_0 = string_of_postcard ctx st in
         Ok (PeTarget x_0)
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
         let* x_0 = local_id_of_postcard ctx st in
         Ok (PlaceLocal x_0)
     | 1 ->
         let* x_0 = box_of_postcard place_of_postcard ctx st in
         let* x_1 = projection_elem_of_postcard ctx st in
         Ok (PlaceProjection (x_0, x_1))
     | 2 ->
         let* x_0 = global_decl_ref_of_postcard ctx st in
         Ok (PlaceGlobal x_0)
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
         let* x_0 = trait_item_name_of_postcard ctx st in
         Ok (TraitItem x_0)
     | 6 -> Ok OriginDyn
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and projection_elem_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (projection_elem, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 -> Ok Deref
     | 1 ->
         let* x_0 = field_proj_kind_of_postcard ctx st in
         let* x_1 = field_id_of_postcard ctx st in
         Ok (Field (x_0, x_1))
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
         let* x_0 = global_decl_ref_of_postcard ctx st in
         Ok (ProvGlobal x_0)
     | 1 ->
         let* x_0 = fun_decl_ref_of_postcard ctx st in
         Ok (ProvFunction x_0)
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
         let* x_0 = de_bruijn_var_of_postcard region_id_of_postcard ctx st in
         Ok (RVar x_0)
     | 1 -> Ok RStatic
     | 2 ->
         let* x_0 = region_id_of_postcard ctx st in
         Ok (RBody x_0)
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
     let* mutability = lifetime_mutability_of_postcard ctx st in
     Ok ({ index; name; mutability } : region_param))

and rvalue_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (rvalue, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 ->
         let* x_0 = operand_of_postcard ctx st in
         Ok (Use x_0)
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
         let* x_0 = binop_of_postcard ctx st in
         let* x_1 = operand_of_postcard ctx st in
         let* x_2 = operand_of_postcard ctx st in
         Ok (BinaryOp (x_0, x_1, x_2))
     | 4 ->
         let* x_0 = unop_of_postcard ctx st in
         let* x_1 = operand_of_postcard ctx st in
         Ok (UnaryOp (x_0, x_1))
     | 5 ->
         let* x_0 = nullop_of_postcard ctx st in
         let* x_1 = ty_of_postcard ctx st in
         Ok (NullaryOp (x_0, x_1))
     | 6 ->
         let* x_0 = place_of_postcard ctx st in
         Ok (Discriminant x_0)
     | 7 ->
         let* x_0 = aggregate_kind_of_postcard ctx st in
         let* x_1 = list_of_postcard operand_of_postcard ctx st in
         Ok (Aggregate (x_0, x_1))
     | 8 ->
         let* x_0 = place_of_postcard ctx st in
         let* x_1 = ty_of_postcard ctx st in
         let* x_2 =
           option_of_postcard (box_of_postcard constant_expr_of_postcard) ctx st
         in
         Ok (Len (x_0, x_1, x_2))
     | 9 ->
         let* x_0 = operand_of_postcard ctx st in
         let* x_1 = ty_of_postcard ctx st in
         let* x_2 = box_of_postcard constant_expr_of_postcard ctx st in
         Ok (Repeat (x_0, x_1, x_2))
     | 10 ->
         let* x_0 = operand_of_postcard ctx st in
         let* x_1 = ty_of_postcard ctx st in
         Ok (ShallowInitBox (x_0, x_1))
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and scalar_value_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (scalar_value, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 ->
         let* x_0 = u_int_ty_of_postcard ctx st in
         let* x_1 = big_uint_of_postcard ctx st in
         Ok (UnsignedScalar (x_0, x_1))
     | 1 ->
         let* x_0 = int_ty_of_postcard ctx st in
         let* x_1 = big_int_of_postcard ctx st in
         Ok (SignedScalar (x_0, x_1))
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

and trait_assoc_ty_impl_of_postcard (ctx : of_postcard_ctx)
    (st : postcard_state) : (trait_assoc_ty_impl, string) result =
  combine_error_msgs st __FUNCTION__
    (let* value = ty_of_postcard ctx st in
     let* _ =
       index_vec_of_postcard trait_clause_id_of_postcard trait_ref_of_postcard
         ctx st
     in
     Ok ({ value } : trait_assoc_ty_impl))

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

and trait_item_name_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (trait_item_name, string) result =
  combine_error_msgs st __FUNCTION__ (string_of_postcard ctx st)

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
         let* x_0 = trait_impl_ref_of_postcard ctx st in
         Ok (TraitImpl x_0)
     | 1 ->
         let* x_0 =
           de_bruijn_var_of_postcard trait_clause_id_of_postcard ctx st
         in
         Ok (Clause x_0)
     | 2 ->
         let* x_0 = box_of_postcard trait_ref_of_postcard ctx st in
         let* x_1 = trait_clause_id_of_postcard ctx st in
         Ok (ParentClause (x_0, x_1))
     | 3 ->
         let* x_0 = box_of_postcard trait_ref_of_postcard ctx st in
         let* x_1 = trait_item_name_of_postcard ctx st in
         let* x_2 = trait_clause_id_of_postcard ctx st in
         Ok (ItemClause (x_0, x_1, x_2))
     | 4 -> Ok Self
     | 5 ->
         let* builtin_data = builtin_impl_data_of_postcard ctx st in
         let* parent_trait_refs =
           index_vec_of_postcard trait_clause_id_of_postcard
             trait_ref_of_postcard ctx st
         in
         let* types =
           list_of_postcard
             (pair_of_postcard trait_item_name_of_postcard
                trait_assoc_ty_impl_of_postcard)
             ctx st
         in
         Ok (BuiltinOrAuto (builtin_data, parent_trait_refs, types))
     | 6 -> Ok Dyn
     | 7 ->
         let* x_0 = string_of_postcard ctx st in
         Ok (UnknownTrait x_0)
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and trait_type_constraint_of_postcard (ctx : of_postcard_ctx)
    (st : postcard_state) : (trait_type_constraint, string) result =
  combine_error_msgs st __FUNCTION__
    (let* trait_ref = trait_ref_of_postcard ctx st in
     let* type_name = trait_item_name_of_postcard ctx st in
     let* ty = ty_of_postcard ctx st in
     Ok ({ trait_ref; type_name; ty } : trait_type_constraint))

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
         let* x_0 = type_decl_ref_of_postcard ctx st in
         Ok (TAdt x_0)
     | 1 ->
         let* x_0 = de_bruijn_var_of_postcard type_var_id_of_postcard ctx st in
         Ok (TVar x_0)
     | 2 ->
         let* x_0 = literal_type_of_postcard ctx st in
         Ok (TLiteral x_0)
     | 3 -> Ok TNever
     | 4 ->
         let* x_0 = region_of_postcard ctx st in
         let* x_1 = ty_of_postcard ctx st in
         let* x_2 = ref_kind_of_postcard ctx st in
         Ok (TRef (x_0, x_1, x_2))
     | 5 ->
         let* x_0 = ty_of_postcard ctx st in
         let* x_1 = ref_kind_of_postcard ctx st in
         Ok (TRawPtr (x_0, x_1))
     | 6 ->
         let* x_0 = trait_ref_of_postcard ctx st in
         let* x_1 = trait_item_name_of_postcard ctx st in
         Ok (TTraitType (x_0, x_1))
     | 7 ->
         let* x_0 = dyn_predicate_of_postcard ctx st in
         Ok (TDynTrait x_0)
     | 8 ->
         let* x_0 = region_binder_of_postcard fun_sig_of_postcard ctx st in
         Ok (TFnPtr x_0)
     | 9 ->
         let* x_0 = region_binder_of_postcard fn_ptr_of_postcard ctx st in
         Ok (TFnDef x_0)
     | 10 ->
         let* x_0 = ty_of_postcard ctx st in
         Ok (TPtrMetadata x_0)
     | 11 ->
         let* x_0 = ty_of_postcard ctx st in
         let* x_1 = box_of_postcard constant_expr_of_postcard ctx st in
         Ok (TArray (x_0, x_1))
     | 12 ->
         let* x_0 = ty_of_postcard ctx st in
         Ok (TSlice x_0)
     | 13 ->
         let* x_0 = string_of_postcard ctx st in
         Ok (TError x_0)
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and type_decl_id_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (type_decl_id, string) result =
  combine_error_msgs st __FUNCTION__ (TypeDeclId.id_of_postcard ctx st)

and type_decl_ref_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (type_decl_ref, string) result =
  combine_error_msgs st __FUNCTION__
    (let* id = type_id_of_postcard ctx st in
     let* generics = box_of_postcard generic_args_of_postcard ctx st in
     Ok ({ id; generics } : type_decl_ref))

and type_id_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (type_id, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 ->
         let* x_0 = type_decl_id_of_postcard ctx st in
         Ok (TAdtId x_0)
     | 1 -> Ok TTuple
     | 2 ->
         let* x_0 = builtin_ty_of_postcard ctx st in
         Ok (TBuiltin x_0)
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and type_param_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (type_param, string) result =
  combine_error_msgs st __FUNCTION__
    (let* index = type_var_id_of_postcard ctx st in
     let* name = string_of_postcard ctx st in
     Ok ({ index; name } : type_param))

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
         let* x_0 = overflow_mode_of_postcard ctx st in
         Ok (Neg x_0)
     | 2 ->
         let* x_0 = cast_kind_of_postcard ctx st in
         Ok (Cast x_0)
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and unsizing_metadata_of_postcard (ctx : of_postcard_ctx) (st : postcard_state)
    : (unsizing_metadata, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 ->
         let* x_0 = box_of_postcard constant_expr_of_postcard ctx st in
         Ok (MetaLength x_0)
     | 1 ->
         let* x_0 = trait_ref_of_postcard ctx st in
         let* x_1 = box_of_postcard constant_expr_of_postcard ctx st in
         Ok (MetaVTable (x_0, x_1))
     | 2 ->
         let* x_0 = list_of_postcard field_id_of_postcard ctx st in
         Ok (MetaVTableUpcast x_0)
     | 3 -> Ok MetaUnknown
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and variant_id_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (variant_id, string) result =
  combine_error_msgs st __FUNCTION__ (VariantId.id_of_postcard ctx st)

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
           let* x_0 = place_of_postcard ctx st in
           let* x_1 = rvalue_of_postcard ctx st in
           Ok (Assign (x_0, x_1))
       | 1 ->
           let* x_0 = place_of_postcard ctx st in
           let* x_1 = variant_id_of_postcard ctx st in
           Ok (SetDiscriminant (x_0, x_1))
       | 2 ->
           let* x_0 = box_of_postcard copy_non_overlapping_of_postcard ctx st in
           Ok (CopyNonOverlapping x_0)
       | 3 ->
           let* x_0 = local_id_of_postcard ctx st in
           Ok (StorageLive x_0)
       | 4 ->
           let* x_0 = local_id_of_postcard ctx st in
           Ok (StorageDead x_0)
       | 5 ->
           let* x_0 = place_of_postcard ctx st in
           Ok (PlaceMention x_0)
       | 6 ->
           let* assert_ = assertion_of_postcard ctx st in
           let* on_failure = abort_kind_of_postcard ctx st in
           Ok (Assert (assert_, on_failure))
       | 7 -> Ok Nop
       | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

  and switch_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
      (Generated_UllbcAst.switch, string) result =
    combine_error_msgs st __FUNCTION__
      (let* __tag = int_of_postcard ctx st in
       match __tag with
       | 0 ->
           let* x_0 = block_id_of_postcard ctx st in
           let* x_1 = block_id_of_postcard ctx st in
           Ok (If (x_0, x_1))
       | 1 ->
           let* x_0 = literal_type_of_postcard ctx st in
           let* x_1 =
             list_of_postcard
               (pair_of_postcard literal_of_postcard block_id_of_postcard)
               ctx st
           in
           let* x_2 = block_id_of_postcard ctx st in
           Ok (SwitchInt (x_0, x_1, x_2))
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
           let* discr = operand_of_postcard ctx st in
           let* targets = switch_of_postcard ctx st in
           Ok (Switch (discr, targets))
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
           let* x_0 = abort_kind_of_postcard ctx st in
           Ok (Abort x_0)
       | 6 -> Ok Return
       | 7 -> Ok UnwindResume
       | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))
end

module Llbc = struct
  open LlbcAst

  let rec ___ = ()

  and block_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
      (Generated_LlbcAst.block, string) result =
    combine_error_msgs st __FUNCTION__
      (let* span = span_of_postcard ctx st in
       let* statements = list_of_postcard statement_of_postcard ctx st in
       Ok ({ span; statements } : Generated_LlbcAst.block))

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
           let* x_0 = place_of_postcard ctx st in
           let* x_1 = rvalue_of_postcard ctx st in
           Ok (Assign (x_0, x_1))
       | 1 ->
           let* x_0 = place_of_postcard ctx st in
           let* x_1 = variant_id_of_postcard ctx st in
           Ok (SetDiscriminant (x_0, x_1))
       | 2 ->
           let* x_0 = box_of_postcard copy_non_overlapping_of_postcard ctx st in
           Ok (CopyNonOverlapping x_0)
       | 3 ->
           let* x_0 = local_id_of_postcard ctx st in
           Ok (StorageLive x_0)
       | 4 ->
           let* x_0 = local_id_of_postcard ctx st in
           Ok (StorageDead x_0)
       | 5 ->
           let* x_0 = place_of_postcard ctx st in
           Ok (PlaceMention x_0)
       | 6 ->
           let* x_0 = place_of_postcard ctx st in
           let* x_1 = fn_ptr_of_postcard ctx st in
           let* x_2 = drop_kind_of_postcard ctx st in
           Ok (Drop (x_0, x_1, x_2))
       | 7 ->
           let* assert_ = assertion_of_postcard ctx st in
           let* on_failure = abort_kind_of_postcard ctx st in
           Ok (Assert (assert_, on_failure))
       | 8 ->
           let* x_0 = call_of_postcard ctx st in
           Ok (Call x_0)
       | 9 ->
           let* x_0 = abort_kind_of_postcard ctx st in
           Ok (Abort x_0)
       | 10 -> Ok Return
       | 11 ->
           let* x_0 = usize_of_postcard ctx st in
           Ok (Break x_0)
       | 12 ->
           let* x_0 = usize_of_postcard ctx st in
           Ok (Continue x_0)
       | 13 -> Ok Nop
       | 14 ->
           let* x_0 = switch_of_postcard ctx st in
           Ok (Switch x_0)
       | 15 ->
           let* x_0 = block_of_postcard ctx st in
           Ok (Loop x_0)
       | 16 ->
           let* x_0 = string_of_postcard ctx st in
           Ok (Error x_0)
       | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

  and switch_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
      (Generated_LlbcAst.switch, string) result =
    combine_error_msgs st __FUNCTION__
      (let* __tag = int_of_postcard ctx st in
       match __tag with
       | 0 ->
           let* x_0 = operand_of_postcard ctx st in
           let* x_1 = block_of_postcard ctx st in
           let* x_2 = block_of_postcard ctx st in
           Ok (If (x_0, x_1, x_2))
       | 1 ->
           let* x_0 = operand_of_postcard ctx st in
           let* x_1 = literal_type_of_postcard ctx st in
           let* x_2 =
             list_of_postcard
               (pair_of_postcard
                  (list_of_postcard literal_of_postcard)
                  block_of_postcard)
               ctx st
           in
           let* x_3 = block_of_postcard ctx st in
           Ok (SwitchInt (x_0, x_1, x_2, x_3))
       | 2 ->
           let* x_0 = place_of_postcard ctx st in
           let* x_1 =
             list_of_postcard
               (pair_of_postcard
                  (list_of_postcard variant_id_of_postcard)
                  block_of_postcard)
               ctx st
           in
           let* x_2 = option_of_postcard block_of_postcard ctx st in
           Ok (Match (x_0, x_1, x_2))
       | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))
end

let rec ___ = ()

and alignment_modifier_of_postcard (ctx : of_postcard_ctx) (st : postcard_state)
    : (alignment_modifier, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 ->
         let* x_0 = u64_of_postcard ctx st in
         Ok (Align x_0)
     | 1 ->
         let* x_0 = u64_of_postcard ctx st in
         Ok (Pack x_0)
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

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
         let* x_0 = string_of_postcard ctx st in
         Ok (AttrRename x_0)
     | 3 ->
         let* x_0 = string_of_postcard ctx st in
         Ok (AttrVariantsPrefix x_0)
     | 4 ->
         let* x_0 = string_of_postcard ctx st in
         Ok (AttrVariantsSuffix x_0)
     | 5 ->
         let* x_0 = string_of_postcard ctx st in
         Ok (AttrDocComment x_0)
     | 6 ->
         let* x_0 = raw_attribute_of_postcard ctx st in
         Ok (AttrUnknown x_0)
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and body_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (body, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 ->
         let* x_0 =
           gexpr_body_of_postcard
             (index_vec_of_postcard Ullbc.block_id_of_postcard
                Ullbc.block_of_postcard)
             ctx st
         in
         Ok (UnstructuredBody x_0)
     | 1 ->
         let* x_0 = gexpr_body_of_postcard Llbc.block_of_postcard ctx st in
         Ok (StructuredBody x_0)
     | 2 ->
         let* x_0 =
           index_map_of_postcard string_of_postcard fun_decl_ref_of_postcard
             int_of_postcard ctx st
         in
         Ok (TargetDispatchBody x_0)
     | 3 -> Ok TraitMethodWithoutDefaultBody
     | 4 ->
         let* x_0 = string_of_postcard ctx st in
         Ok (ExternBody x_0)
     | 5 ->
         let* name = string_of_postcard ctx st in
         let* arg_names =
           list_of_postcard (option_of_postcard string_of_postcard) ctx st
         in
         Ok (IntrinsicBody (name, arg_names))
     | 6 -> Ok OpaqueBody
     | 7 -> Ok MissingBody
     | 8 ->
         let* x_0 = error_of_postcard ctx st in
         Ok (ErrorBody x_0)
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and cli_options_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (cli_options, string) result =
  combine_error_msgs st __FUNCTION__
    (let* ullbc = bool_of_postcard ctx st in
     let* precise_drops = bool_of_postcard ctx st in
     let* skip_borrowck = bool_of_postcard ctx st in
     let* mir = option_of_postcard mir_level_of_postcard ctx st in
     let* rustc_args = list_of_postcard string_of_postcard ctx st in
     let* targets = list_of_postcard string_of_postcard ctx st in
     let* monomorphize = bool_of_postcard ctx st in
     let* monomorphize_mut =
       option_of_postcard monomorphize_mut_of_postcard ctx st
     in
     let* start_from = list_of_postcard string_of_postcard ctx st in
     let* start_from_if_exists = list_of_postcard string_of_postcard ctx st in
     let* start_from_attribute = option_of_postcard string_of_postcard ctx st in
     let* start_from_pub = bool_of_postcard ctx st in
     let* included = list_of_postcard string_of_postcard ctx st in
     let* opaque = list_of_postcard string_of_postcard ctx st in
     let* exclude = list_of_postcard string_of_postcard ctx st in
     let* extract_opaque_bodies = bool_of_postcard ctx st in
     let* translate_all_methods = bool_of_postcard ctx st in
     let* lift_associated_types = list_of_postcard string_of_postcard ctx st in
     let* hide_marker_traits = bool_of_postcard ctx st in
     let* remove_adt_clauses = bool_of_postcard ctx st in
     let* hide_allocator = bool_of_postcard ctx st in
     let* remove_unused_self_clauses = bool_of_postcard ctx st in
     let* desugar_drops = bool_of_postcard ctx st in
     let* ops_to_function_calls = bool_of_postcard ctx st in
     let* index_to_function_calls = bool_of_postcard ctx st in
     let* treat_box_as_builtin = bool_of_postcard ctx st in
     let* raw_consts = bool_of_postcard ctx st in
     let* unsized_strings = bool_of_postcard ctx st in
     let* reconstruct_fallible_operations = bool_of_postcard ctx st in
     let* reconstruct_asserts = bool_of_postcard ctx st in
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
     let* no_typecheck = bool_of_postcard ctx st in
     let* no_normalize = bool_of_postcard ctx st in
     let* abort_on_error = bool_of_postcard ctx st in
     let* error_on_warnings = bool_of_postcard ctx st in
     let* preset = option_of_postcard preset_of_postcard ctx st in
     Ok
       ({
          ullbc;
          precise_drops;
          skip_borrowck;
          mir;
          rustc_args;
          targets;
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
          lift_associated_types;
          hide_marker_traits;
          remove_adt_clauses;
          hide_allocator;
          remove_unused_self_clauses;
          desugar_drops;
          ops_to_function_calls;
          index_to_function_calls;
          treat_box_as_builtin;
          raw_consts;
          unsized_strings;
          reconstruct_fallible_operations;
          reconstruct_asserts;
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
          no_typecheck;
          no_normalize;
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

and declaration_group_of_postcard (ctx : of_postcard_ctx) (st : postcard_state)
    : (declaration_group, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 ->
         let* x_0 =
           g_declaration_group_of_postcard type_decl_id_of_postcard ctx st
         in
         Ok (TypeGroup x_0)
     | 1 ->
         let* x_0 =
           g_declaration_group_of_postcard fun_decl_id_of_postcard ctx st
         in
         Ok (FunGroup x_0)
     | 2 ->
         let* x_0 =
           g_declaration_group_of_postcard global_decl_id_of_postcard ctx st
         in
         Ok (GlobalGroup x_0)
     | 3 ->
         let* x_0 =
           g_declaration_group_of_postcard trait_decl_id_of_postcard ctx st
         in
         Ok (TraitDeclGroup x_0)
     | 4 ->
         let* x_0 =
           g_declaration_group_of_postcard trait_impl_id_of_postcard ctx st
         in
         Ok (TraitImplGroup x_0)
     | 5 ->
         let* x_0 =
           g_declaration_group_of_postcard item_id_of_postcard ctx st
         in
         Ok (MixedGroup x_0)
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and discriminant_layout_of_postcard (ctx : of_postcard_ctx)
    (st : postcard_state) : (discriminant_layout, string) result =
  combine_error_msgs st __FUNCTION__
    (let* offset = u64_of_postcard ctx st in
     let* tag_ty = integer_type_of_postcard ctx st in
     let* encoding = tag_encoding_of_postcard ctx st in
     Ok ({ offset; tag_ty; encoding } : discriminant_layout))

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
     let* field_name = option_of_postcard string_of_postcard ctx st in
     let* field_ty = ty_of_postcard ctx st in
     Ok ({ span; attr_info; field_name; field_ty } : field))

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
         let* x_0 = path_buf_of_postcard ctx st in
         Ok (Virtual x_0)
     | 1 ->
         let* x_0 = path_buf_of_postcard ctx st in
         Ok (Local x_0)
     | 2 ->
         let* x_0 = string_of_postcard ctx st in
         Ok (NotReal x_0)
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and fun_decl_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (fun_decl, string) result =
  combine_error_msgs st __FUNCTION__
    (let* def_id = fun_decl_id_of_postcard ctx st in
     let* item_meta = item_meta_of_postcard ctx st in
     let* generics = generic_params_of_postcard ctx st in
     let* signature = fun_sig_of_postcard ctx st in
     let* src = item_source_of_postcard ctx st in
     let* is_global_initializer =
       option_of_postcard global_decl_id_of_postcard ctx st
     in
     let* body = body_of_postcard ctx st in
     Ok
       ({
          def_id;
          item_meta;
          generics;
          signature;
          src;
          is_global_initializer;
          body;
        }
         : fun_decl))

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
         let* x_0 = arg0_of_postcard ctx st in
         Ok (NonRecGroup x_0)
     | 1 ->
         let* x_0 = list_of_postcard arg0_of_postcard ctx st in
         Ok (RecGroup x_0)
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
         (pair_of_postcard usize_of_postcard
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
     let* src = item_source_of_postcard ctx st in
     let* global_kind = global_kind_of_postcard ctx st in
     let* init = fun_decl_id_of_postcard ctx st in
     Ok
       ({ def_id; item_meta; generics; ty; src; global_kind; init }
         : global_decl))

and global_kind_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (global_kind, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 -> Ok Static
     | 1 -> Ok NamedConst
     | 2 -> Ok AnonConst
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

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

and integer_type_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (integer_type, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 ->
         let* x_0 = int_ty_of_postcard ctx st in
         Ok (Signed x_0)
     | 1 ->
         let* x_0 = u_int_ty_of_postcard ctx st in
         Ok (Unsigned x_0)
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and item_id_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (item_id, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 ->
         let* x_0 = type_decl_id_of_postcard ctx st in
         Ok (IdType x_0)
     | 1 ->
         let* x_0 = trait_decl_id_of_postcard ctx st in
         Ok (IdTraitDecl x_0)
     | 2 ->
         let* x_0 = trait_impl_id_of_postcard ctx st in
         Ok (IdTraitImpl x_0)
     | 3 ->
         let* x_0 = fun_decl_id_of_postcard ctx st in
         Ok (IdFun x_0)
     | 4 ->
         let* x_0 = global_decl_id_of_postcard ctx st in
         Ok (IdGlobal x_0)
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
     let* lang_item = option_of_postcard string_of_postcard ctx st in
     Ok
       ({ name; span; source_text; attr_info; is_local; opacity; lang_item }
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

and item_source_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (item_source, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 -> Ok TopLevelItem
     | 1 ->
         let* info = closure_info_of_postcard ctx st in
         Ok (ClosureItem info)
     | 2 ->
         let* trait_ref = trait_decl_ref_of_postcard ctx st in
         let* item_name = trait_item_name_of_postcard ctx st in
         let* has_default = bool_of_postcard ctx st in
         Ok (TraitDeclItem (trait_ref, item_name, has_default))
     | 3 ->
         let* impl_ref = trait_impl_ref_of_postcard ctx st in
         let* trait_ref = trait_decl_ref_of_postcard ctx st in
         let* item_name = trait_item_name_of_postcard ctx st in
         let* reuses_default = bool_of_postcard ctx st in
         Ok (TraitImplItem (impl_ref, trait_ref, item_name, reuses_default))
     | 4 ->
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
         Ok (VTableTyItem (dyn_predicate, field_map, supertrait_map))
     | 5 ->
         let* impl_ref = trait_impl_ref_of_postcard ctx st in
         Ok (VTableInstanceItem impl_ref)
     | 6 -> Ok VTableMethodShimItem
     | 7 -> Ok VTableInstanceMonoItem
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and layout_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (layout, string) result =
  combine_error_msgs st __FUNCTION__
    (let* size = option_of_postcard u64_of_postcard ctx st in
     let* align = option_of_postcard u64_of_postcard ctx st in
     let* discriminant_layout =
       option_of_postcard discriminant_layout_of_postcard ctx st
     in
     let* uninhabited = bool_of_postcard ctx st in
     let* variant_layouts =
       index_vec_of_postcard variant_id_of_postcard variant_layout_of_postcard
         ctx st
     in
     Ok
       ({ size; align; discriminant_layout; uninhabited; variant_layouts }
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
         let* x_0 = type_decl_ref_of_postcard ctx st in
         Ok (VTable x_0)
     | 3 ->
         let* x_0 = ty_of_postcard ctx st in
         Ok (InheritFrom x_0)
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
     let* explicit_discr_type = bool_of_postcard ctx st in
     Ok
       ({ repr_algo; align_modif; transparent; explicit_discr_type }
         : repr_options))

and serialization_format_arg_of_postcard (ctx : of_postcard_ctx)
    (st : postcard_state) : (serialization_format_arg, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 -> Ok Json
     | 1 -> Ok Postcard
     | 2 -> Ok AllFormats
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and tag_encoding_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (tag_encoding, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 -> Ok Direct
     | 1 ->
         let* untagged_variant = variant_id_of_postcard ctx st in
         Ok (Niche untagged_variant)
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and target_info_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (target_info, string) result =
  combine_error_msgs st __FUNCTION__
    (let* target_pointer_size = u64_of_postcard ctx st in
     let* is_little_endian = bool_of_postcard ctx st in
     Ok ({ target_pointer_size; is_little_endian } : target_info))

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
     let* generics = generic_params_of_postcard ctx st in
     let* implied_clauses =
       index_vec_of_postcard trait_clause_id_of_postcard trait_param_of_postcard
         ctx st
     in
     let* consts = list_of_postcard trait_assoc_const_of_postcard ctx st in
     let* types =
       list_of_postcard (binder_of_postcard trait_assoc_ty_of_postcard) ctx st
     in
     let* methods =
       list_of_postcard (binder_of_postcard trait_method_of_postcard) ctx st
     in
     let* vtable = option_of_postcard type_decl_ref_of_postcard ctx st in
     Ok
       ({
          def_id;
          item_meta;
          generics;
          implied_clauses;
          consts;
          types;
          methods;
          vtable;
        }
         : trait_decl))

and trait_impl_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (trait_impl, string) result =
  combine_error_msgs st __FUNCTION__
    (let* def_id = trait_impl_id_of_postcard ctx st in
     let* item_meta = item_meta_of_postcard ctx st in
     let* impl_trait = trait_decl_ref_of_postcard ctx st in
     let* generics = generic_params_of_postcard ctx st in
     let* implied_trait_refs =
       index_vec_of_postcard trait_clause_id_of_postcard trait_ref_of_postcard
         ctx st
     in
     let* consts =
       list_of_postcard
         (pair_of_postcard trait_item_name_of_postcard
            global_decl_ref_of_postcard)
         ctx st
     in
     let* types =
       list_of_postcard
         (pair_of_postcard trait_item_name_of_postcard
            (binder_of_postcard trait_assoc_ty_impl_of_postcard))
         ctx st
     in
     let* methods =
       list_of_postcard
         (pair_of_postcard trait_item_name_of_postcard
            (binder_of_postcard fun_decl_ref_of_postcard))
         ctx st
     in
     let* vtable = option_of_postcard global_decl_ref_of_postcard ctx st in
     Ok
       ({
          def_id;
          item_meta;
          impl_trait;
          generics;
          implied_trait_refs;
          consts;
          types;
          methods;
          vtable;
        }
         : trait_impl))

and trait_method_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (trait_method, string) result =
  combine_error_msgs st __FUNCTION__
    (let* name = trait_item_name_of_postcard ctx st in
     let* attr_info = attr_info_of_postcard ctx st in
     let* signature = fun_sig_of_postcard ctx st in
     let* item = fun_decl_ref_of_postcard ctx st in
     Ok ({ name; attr_info; signature; item } : trait_method))

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
     let* src = item_source_of_postcard ctx st in
     let* kind = type_decl_kind_of_postcard ctx st in
     let* layout =
       index_map_of_postcard string_of_postcard layout_of_postcard
         int_of_postcard ctx st
     in
     let* ptr_metadata = ptr_metadata_of_postcard ctx st in
     let* repr = option_of_postcard repr_options_of_postcard ctx st in
     Ok
       ({ def_id; item_meta; generics; src; kind; layout; ptr_metadata; repr }
         : type_decl))

and type_decl_kind_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (type_decl_kind, string) result =
  combine_error_msgs st __FUNCTION__
    (let* __tag = int_of_postcard ctx st in
     match __tag with
     | 0 ->
         let* x_0 =
           index_vec_of_postcard field_id_of_postcard field_of_postcard ctx st
         in
         Ok (Struct x_0)
     | 1 ->
         let* x_0 =
           index_vec_of_postcard variant_id_of_postcard variant_of_postcard ctx
             st
         in
         Ok (Enum x_0)
     | 2 ->
         let* x_0 =
           index_vec_of_postcard field_id_of_postcard field_of_postcard ctx st
         in
         Ok (Union x_0)
     | 3 -> Ok Opaque
     | 4 ->
         let* x_0 = ty_of_postcard ctx st in
         Ok (Alias x_0)
     | 5 ->
         let* x_0 = string_of_postcard ctx st in
         Ok (TDeclError x_0)
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
         let* x_0 = trait_item_name_of_postcard ctx st in
         Ok (VTableMethod x_0)
     | 4 ->
         let* x_0 = trait_clause_id_of_postcard ctx st in
         Ok (VTableSuperTrait x_0)
     | _ -> Error ("unknown enum variant tag: " ^ string_of_int __tag))

and variant_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (variant, string) result =
  combine_error_msgs st __FUNCTION__
    (let* span = span_of_postcard ctx st in
     let* attr_info = attr_info_of_postcard ctx st in
     let* variant_name = string_of_postcard ctx st in
     let* fields =
       index_vec_of_postcard field_id_of_postcard field_of_postcard ctx st
     in
     let* discriminant = literal_of_postcard ctx st in
     Ok ({ span; attr_info; variant_name; fields; discriminant } : variant))

and variant_layout_of_postcard (ctx : of_postcard_ctx) (st : postcard_state) :
    (variant_layout, string) result =
  combine_error_msgs st __FUNCTION__
    (let* field_offsets =
       index_vec_of_postcard field_id_of_postcard u64_of_postcard ctx st
     in
     let* uninhabited = bool_of_postcard ctx st in
     let* tag = option_of_postcard scalar_value_of_postcard ctx st in
     Ok ({ field_offsets; uninhabited; tag } : variant_layout))
