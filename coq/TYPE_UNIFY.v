(*
  TYPE_UNIFY.v
  (* Substitution operations *)
  (* Full unification matching Python implementation *)
  (* Binding type for partial application *)
*)
From Coq Require Import String List Bool Arith PeanoNat Lia Program.Wf.
Import ListNotations.

Require Import TYPE_CORE.
Import TypeCore.

Module TypeUnification.
  Import TypeCore TypeLattice.
  Export unify, apply_subst, Binding.
End TypeUnification.
