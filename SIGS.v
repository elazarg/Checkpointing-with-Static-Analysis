From Coq Require Import String List Bool Arith ZArith PeanoNat.
Import ListNotations.

Require Import IR.

Module Type TypeSystemSig.
  Import TAC.

  (* Type expressions - abstract to the signature *)
  Parameter TypeExpr : Type.
  Parameter type_bot : TypeExpr.
  Parameter type_top : TypeExpr.
  Parameter type_join : TypeExpr -> TypeExpr -> TypeExpr.
  Parameter type_is_subtype : TypeExpr -> TypeExpr -> bool.
  Parameter type_is_immutable : TypeExpr -> bool.

  Record SideEffect := {
    se_new : bool;
    se_bound_method : bool;
    se_update : option TypeExpr;
    se_update_indices : list nat;
    se_points_to_args : bool
  }.
  
  Parameter empty_effect : SideEffect.
  Parameter literal_type : ConstV -> TypeExpr.
  Parameter get_type_hash : TypeExpr -> nat.

  Parameter is_overloaded : TypeExpr -> bool.
  Parameter is_property : TypeExpr -> bool.
  Parameter is_bound_method : TypeExpr -> bool.
  Parameter any_new : TypeExpr -> bool.
  Parameter all_new : TypeExpr -> bool.
  Parameter get_return : TypeExpr -> TypeExpr.
  Parameter get_side_effect : TypeExpr -> SideEffect.

  Parameter subscr : TypeExpr -> string -> TypeExpr.
  Parameter subscr_literal : TypeExpr -> ConstV -> TypeExpr.
  Parameter subscr_index : TypeExpr -> nat -> TypeExpr.

  Parameter partial : TypeExpr -> list TypeExpr -> TypeExpr.
  Parameter get_unop : TypeExpr -> string -> TypeExpr.
  Parameter partial_binop : TypeExpr -> TypeExpr -> string -> TypeExpr.

  Parameter make_list_constructor : TypeExpr.
  Parameter make_tuple_constructor : TypeExpr.
  Parameter make_dict_constructor : TypeExpr.
  Parameter make_set_constructor : TypeExpr.
  Parameter make_slice_constructor : TypeExpr.

  Parameter type_is_callable : TypeExpr -> bool.

  (* Operator resolution with typed operands *)
  Inductive DunderInfo :=
  | TDUnOp  (op:UnOpTag)  (arg:TypeExpr)
  | TDBinOp (op:BinOpTag) (lhs rhs:TypeExpr) (mode:Inplace)
  | TDCmpOp (op:CmpOpTag) (lhs rhs:TypeExpr).

  Parameter dunder_lookup : DunderInfo -> TypeExpr.
End TypeSystemSig.
