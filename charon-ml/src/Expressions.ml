(** WARNING: this file is partially auto-generated. Do not edit `src/Expressions.ml`
    by hand. Edit `templates/Expressions.ml` instead, or improve the code
    generation tool so avoid the need for hand-writing things.

    `templates/Expressions.ml` contains the manual definitions and some `(*
    __REPLACEn__ *)` comments. These comments are replaced by auto-generated
    definitions by running `make generate-ml` in the crate root. The
    code-generation code is in `charon/src/bin/generate-ml`.
 *)
open Identifiers

open Types
open Values
module VarId = IdGen ()
module GlobalDeclId = Types.GlobalDeclId
module FunDeclId = Types.FunDeclId

(** We define this type to control the name of the visitor functions
    (see e.g., {!Charon.UllbcAst.iter_statement_base}).
  *)
type var_id = VarId.id [@@deriving show, ord]

(** An built-in function identifier, identifying a function coming from a
    standard library.
 *)
type assumed_fun_id =
  | BoxNew  (** `alloc::boxed::Box::new` *)
  | ArrayToSliceShared
      (** Cast an array as a slice.

          Converted from [UnOp::ArrayToSlice]
       *)
  | ArrayToSliceMut
      (** Cast an array as a slice.

          Converted from [UnOp::ArrayToSlice]
       *)
  | ArrayRepeat
      (** `repeat(n, x)` returns an array where `x` has been replicated `n` times.

          We introduce this when desugaring the [ArrayRepeat] rvalue.
       *)
  | Index of builtin_index_op
      (** Converted from indexing `ProjectionElem`s. The signature depends on the parameters. It
          could look like:
          - `fn ArrayIndexShared<T,N>(&[T;N], usize) -> &T`
          - `fn SliceIndexShared<T>(&[T], usize) -> &T`
          - `fn ArraySubSliceShared<T,N>(&[T;N], usize, usize) -> &[T]`
          - `fn SliceSubSliceMut<T>(&mut [T], usize, usize) -> &mut [T]`
          - etc
       *)

(** One of 8 built-in indexing operations. *)
and builtin_index_op = {
  is_array : bool;  (** Whether this is a slice or array. *)
  mutability : ref_kind;
      (** Whether we're indexing mutably or not. Determines the type ofreference of the input and
        output.
     *)
  is_range : bool;
      (** Whether we're indexing a single element or a subrange. If `true`, the function takes
        two indices and the output is a slice; otherwise, the function take one index and the
        output is a reference to a single element.
     *)
}

and abort_kind =
  | Panic of name  (** A built-in panicking function. *)
  | UndefinedBehavior
      (** A MIR `Unreachable` terminator corresponds to undefined behavior in the rust abstract
          machine.
       *)
[@@deriving show, ord]

(** Ancestor the field_proj_kind iter visitor *)
class ['self] iter_place_base =
  object (_self : 'self)
    inherit [_] VisitorsRuntime.iter
    method visit_type_decl_id : 'env -> type_decl_id -> unit = fun _ _ -> ()
    method visit_var_id : 'env -> var_id -> unit = fun _ _ -> ()
    method visit_variant_id : 'env -> variant_id -> unit = fun _ _ -> ()
    method visit_field_id : 'env -> field_id -> unit = fun _ _ -> ()
  end

(** Ancestor the field_proj_kind map visitor *)
class ['self] map_place_base =
  object (_self : 'self)
    inherit [_] VisitorsRuntime.map

    method visit_type_decl_id : 'env -> type_decl_id -> type_decl_id =
      fun _ x -> x

    method visit_var_id : 'env -> var_id -> var_id = fun _ x -> x
    method visit_variant_id : 'env -> variant_id -> variant_id = fun _ x -> x
    method visit_field_id : 'env -> field_id -> field_id = fun _ x -> x
  end

type field_proj_kind =
  | ProjAdt of type_decl_id * variant_id option
  | ProjTuple of int
      (** If we project from a tuple, the projection kind gives the arity of the tuple. *)

(** Note that we don't have the equivalent of "downcasts".
    Downcasts are actually necessary, for instance when initializing enumeration
    values: the value is initially `Bottom`, and we need a way of knowing the
    variant.
    For example:
    `((_0 as Right).0: T2) = move _1;`
    In MIR, downcasts always happen before field projections: in our internal
    language, we thus merge downcasts and field projections.
 *)
and projection_elem =
  | Deref  (** Dereference a shared/mutable reference or a raw pointer. *)
  | DerefBox
      (** Dereference a boxed value.
          Note that this doesn't exist in MIR where `Deref` is used both for the
          mutable and shared references *and* the boxed values. As semantically we
          don't handle those two cases the same way at all, we disambiguate them
          during the translation.
          In rust, this comes from the `*` operator applied on boxes.
       *)
  | Field of field_proj_kind * field_id
      (** Projection from ADTs (variants, structures).
          We allow projections to be used as left-values and right-values.
          We should never have projections to fields of symbolic variants (they
          should have been expanded before through a match).
       *)

and projection = projection_elem list

and place = { var_id : var_id; projection : projection_elem list }
[@@deriving
  show,
    ord,
    visitors
      {
        name = "iter_place";
        variety = "iter";
        ancestors = [ "iter_place_base" ];
        nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
        concrete = true;
      },
    visitors
      {
        name = "map_place";
        variety = "map";
        ancestors = [ "map_place_base" ];
        nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
        concrete = true;
      }]

type borrow_kind =
  | BShared
  | BMut
  | BTwoPhaseMut
      (** See <https://doc.rust-lang.org/beta/nightly-rustc/rustc_middle/mir/enum.MutBorrowKind.html#variant.TwoPhaseBorrow>
          and <https://rustc-dev-guide.rust-lang.org/borrow_check/two_phase_borrows.html>
       *)
  | BShallow
      (** Those are typically introduced when using guards in matches, to make sure guards don't
          change the variant of an enum value while me match over it.

          See <https://doc.rust-lang.org/beta/nightly-rustc/rustc_middle/mir/enum.FakeBorrowKind.html#variant.Shallow>.
       *)
  | BUniqueImmutable
      (** Data must be immutable but not aliasable. In other words you can't mutate the data but you
          can mutate *through it*, e.g. if it points to a `&mut T`. This is only used in closure
          captures, e.g.
          ```rust,ignore
          let mut z = 3;
          let x: &mut isize = &mut z;
          let y = || *x += 5;
          ```
          Here the captured variable can't be `&mut &mut x` since the `x` binding is not mutable, yet
          we must be able to mutate what it points to.

          See <https://doc.rust-lang.org/beta/nightly-rustc/rustc_middle/mir/enum.MutBorrowKind.html#variant.ClosureCapture>.
       *)

(** Binary operations. *)
and binop =
  | BitXor
  | BitAnd
  | BitOr
  | Eq
  | Lt
  | Le
  | Ne
  | Ge
  | Gt
  | Div
      (** Fails if the divisor is 0, or if the operation is `int::MIN / -1`. *)
  | Rem
      (** Fails if the divisor is 0, or if the operation is `int::MIN % -1`. *)
  | Add  (** Fails on overflow. *)
  | Sub  (** Fails on overflow. *)
  | Mul  (** Fails on overflow. *)
  | CheckedAdd
      (** Returns `(result, did_overflow)`, where `result` is the result of the operation with
          wrapping semantics, and `did_overflow` is a boolean that indicates whether the operation
          overflowed. This operation does not fail.
       *)
  | CheckedSub  (** Like `CheckedAdd`. *)
  | CheckedMul  (** Like `CheckedAdd`. *)
  | Shl  (** Fails if the shift is bigger than the bit-size of the type. *)
  | Shr  (** Fails if the shift is bigger than the bit-size of the type. *)
[@@deriving show, ord]

let all_binops =
  [
    BitXor;
    BitAnd;
    BitOr;
    Eq;
    Lt;
    Le;
    Ne;
    Ge;
    Gt;
    Div;
    Rem;
    Add;
    Sub;
    Mul;
    Shl;
    Shr;
  ]

(** Ancestor for the constant_expr iter visitor *)
class ['self] iter_constant_expr_base =
  object (_self : 'self)
    inherit [_] iter_place
    inherit! [_] iter_ty
    method visit_assumed_fun_id : 'env -> assumed_fun_id -> unit = fun _ _ -> ()
  end

(** Ancestor the constant_expr map visitor *)
class ['self] map_constant_expr_base =
  object (_self : 'self)
    inherit [_] map_place
    inherit! [_] map_ty

    method visit_assumed_fun_id : 'env -> assumed_fun_id -> assumed_fun_id =
      fun _ x -> x
  end

(** For all the variants: the first type gives the source type, the second one gives
    the destination type.
 *)
type cast_kind =
  | CastScalar of literal_type * literal_type
      (** Conversion between types in {Integer, Bool}
          Remark: for now we don't support conversions with Char.
       *)
  | CastRawPtr of ty * ty
  | CastFnPtr of ty * ty
  | CastUnsize of ty * ty
      (** [Unsize coercion](https://doc.rust-lang.org/std/ops/trait.CoerceUnsized.html). This is
          either `[T; N]` -> `[T]` or `T: Trait` -> `dyn Trait` coercions, behind a pointer
          (reference, `Box`, or other type that implements `CoerceUnsized`).

          The special case of `&[T; N]` -> `&[T]` coercion is caught by `UnOp::ArrayToSlice`.
       *)
  | CastTransmute of ty * ty
      (** Reinterprets the bits of a value of one type as another type, i.e. exactly what
          [`std::mem::transmute`] does.
       *)

(** Unary operation *)
and unop =
  | Not
  | Neg
      (** This can overflow. In practice, rust introduces an assert before
          (in debug mode) to check that it is not equal to the minimum integer
          value (for the proper type).
       *)
  | Cast of cast_kind
      (** Casts are rvalues in MIR, but we treat them as unops. *)

(** Nullary operation *)
and nullop = SizeOf | AlignOf | OffsetOf of (int * field_id) list | UbChecks

(** A constant expression.

    Only the [Literal] and [Var] cases are left in the final LLBC.

    The other cases come from a straight translation from the MIR:

    [Adt] case:
    It is a bit annoying, but rustc treats some ADT and tuple instances as
    constants when generating MIR:
    - an enumeration with one variant and no fields is a constant.
    - a structure with no field is a constant.
    - sometimes, Rust stores the initialization of an ADT as a constant
      (if all the fields are constant) rather than as an aggregated value
    We later desugar those to regular ADTs, see [regularize_constant_adts.rs].

    [Global] case: access to a global variable. We later desugar it to
    a separate statement.

    [Ref] case: reference to a constant value. We later desugar it to a separate
    statement.

    [FnPtr] case: a function pointer (to a top-level function).

    Remark:
    MIR seems to forbid more complex expressions like paths. For instance,
    reading the constant `a.b` is translated to `{ _1 = const a; _2 = (_1.0) }`.
 *)
and raw_constant_expr =
  | CLiteral of literal
  | CTraitConst of trait_ref * trait_item_name
      (** 
          A trait constant.

          Ex.:
          ```text
          impl Foo for Bar {
            const C : usize = 32; // <-
          }
          ```

          Remark: trait constants can not be used in types, they are necessarily
          values.
       *)
  | CVar of const_generic_var_id  (** A const generic var *)
  | CFnPtr of fn_ptr  (** Function pointer *)

and constant_expr = { value : raw_constant_expr; ty : ty }
and fn_ptr = { func : fun_id_or_trait_method_ref; generics : generic_args }

and fun_id_or_trait_method_ref =
  | FunId of fun_id
  | TraitMethod of trait_ref * trait_item_name * fun_decl_id
      (** If a trait: the reference to the trait and the id of the trait method.
          The fun decl id is not really necessary - we put it here for convenience
          purposes.
       *)

(** A function identifier. See [crate::ullbc_ast::Terminator] *)
and fun_id =
  | FRegular of fun_decl_id
      (** A "regular" function (function local to the crate, external function
          not treated as a primitive one).
       *)
  | FAssumed of assumed_fun_id
      (** A primitive function, coming from a standard library (for instance:
          `alloc::boxed::Box::new`).
          TODO: rename to "Primitive"
       *)
[@@deriving
  show,
    ord,
    visitors
      {
        name = "iter_constant_expr";
        variety = "iter";
        ancestors = [ "iter_constant_expr_base" ];
        nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
        concrete = true;
      },
    visitors
      {
        name = "map_constant_expr";
        variety = "map";
        ancestors = [ "map_constant_expr_base" ];
        nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
        concrete = true;
      }]

(** Ancestor the operand iter visitor *)
class ['self] iter_rvalue_base =
  object (_self : 'self)
    inherit [_] iter_constant_expr
    method visit_binop : 'env -> binop -> unit = fun _ _ -> ()
    method visit_borrow_kind : 'env -> borrow_kind -> unit = fun _ _ -> ()
  end

(** Ancestor the operand map visitor *)
class ['self] map_rvalue_base =
  object (_self : 'self)
    inherit [_] map_constant_expr
    method visit_binop : 'env -> binop -> binop = fun _ x -> x
    method visit_borrow_kind : 'env -> borrow_kind -> borrow_kind = fun _ x -> x
  end

type operand =
  | Copy of place
  | Move of place
  | Constant of constant_expr
      (** Constant value (including constant and static variables) *)

(** An aggregated ADT.

    Note that ADTs are desaggregated at some point in MIR. For instance, if
    we have in Rust:
    ```ignore
      let ls = Cons(hd, tl);
    ```

    In MIR we have (yes, the discriminant update happens *at the end* for some
    reason):
    ```text
      (ls as Cons).0 = move hd;
      (ls as Cons).1 = move tl;
      discriminant(ls) = 0; // assuming `Cons` is the variant of index 0
    ```

    Rem.: in the Aeneas semantics, both cases are handled (in case of desaggregated
    initialization, `ls` is initialized to `⊥`, then this `⊥` is expanded to
    `Cons (⊥, ⊥)` upon the first assignment, at which point we can initialize
    the field 0, etc.).
 *)
and aggregate_kind =
  | AggregatedAdt of type_id * variant_id option * generic_args
  | AggregatedArray of ty * const_generic
      (** We don't put this with the ADT cas because this is the only built-in type
          with aggregates, and it is a primitive type. In particular, it makes
          sense to treat it differently because it has a variable number of fields.
       *)
  | AggregatedClosure of fun_decl_id * generic_args
      (** Aggregated values for closures group the function id together with its
          state.
       *)

(** TODO: we could factor out [Rvalue] and function calls (for LLBC, not ULLBC).
    We can also factor out the unops, binops with the function calls.
    TODO: move the aggregate kind to operands
    TODO: we should prefix the type variants with "R" or "Rv", this would avoid collisions
 *)
and rvalue =
  | Use of operand  (** Lifts an operand as an rvalue. *)
  | RvRef of place * borrow_kind  (** Takes a reference to the given place. *)
  | RawPtr of place * ref_kind
      (** Takes a raw pointer with the given mutability to the given place. This is generated by
          pointer casts like `&v as *const _` or raw borrow expressions like `&raw const v.`
       *)
  | BinaryOp of binop * operand * operand
      (** Binary operations (note that we merge "checked" and "unchecked" binops) *)
  | UnaryOp of unop * operand  (** Unary operation (e.g. not, neg) *)
  | NullaryOp of nullop * ty  (** Nullary operation (e.g. `size_of`) *)
  | Discriminant of place * type_decl_id
      (** Discriminant (for enumerations).
          Note that discriminant values have type isize. We also store the identifier
          of the type from which we read the discriminant.

          This case is filtered in [crate::remove_read_discriminant]
       *)
  | Aggregate of aggregate_kind * operand list
      (** Creates an aggregate value, like a tuple, a struct or an enum:
          ```text
          l = List::Cons { value:x, tail:tl };
          ```
          Note that in some MIR passes (like optimized MIR), aggregate values are
          decomposed, like below:
          ```text
          (l as List::Cons).value = x;
          (l as List::Cons).tail = tl;
          ```
          Because we may want to plug our translation mechanism at various
          places, we need to take both into accounts in the translation and in
          our semantics. Aggregate value initialization is easy, you might want
          to have a look at expansion of `Bottom` values for explanations about the
          other case.

          Remark: in case of closures, the aggregated value groups the closure id
          together with its state.
       *)
  | Global of global_decl_ref
      (** Not present in MIR: we introduce it when replacing constant variables
          in operands in [extract_global_assignments.rs].
       *)
  | Len of place * ty * const_generic option
      (** Length of a memory location. The run-time length of e.g. a vector or a slice is
          represented differently (but pretty-prints the same, FIXME).
          Should be seen as a function of signature:
          - `fn<T;N>(&[T;N]) -> usize`
          - `fn<T>(&[T]) -> usize`

          We store the type argument and the const generic (the latter only for arrays).

          [Len] is automatically introduced by rustc, notably for the bound checks:
          we eliminate it together with the bounds checks whenever possible.
          There are however occurrences that we don't eliminate (yet).
          For instance, for the following Rust code:
          ```text
          fn slice_pattern_4(x: &[()]) {
              match x {
                  [_named] => (),
                  _ => (),
              }
          }
          ```
          rustc introduces a check that the length of the slice is exactly equal
          to 1 and that we preserve.
       *)
[@@deriving
  show,
    visitors
      {
        name = "iter_rvalue";
        variety = "iter";
        ancestors = [ "iter_rvalue_base" ];
        nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
        concrete = true;
      },
    visitors
      {
        name = "map_rvalue";
        variety = "map";
        ancestors = [ "map_rvalue_base" ];
        nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
        concrete = true;
      }]
