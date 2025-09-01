
(*
  TYPE_OPS.v — Non‑lattice operations for the type system
  ---------------------------------------------------------------------------
  Purpose: implement the operational (non‑lattice) primitives used by the
  transfer function, while keeping environment‑dependent and subtle pieces
  parametric.

  Design decisions:
  - Overload effects are *unioned* arm‑wise (safe over‑approx for transfer).
  - Overload predicates are *all‑arms*: mixed overloads do not globally
    count as properties/bound‑methods/callables.
  - Member access distributes over unions/overloads, resolves references,
    and we provide a lightweight self‑binding helper that does not touch
    defaults (full reindexing belongs in the binder implementation).
  - Partial application / argument binding remains a single parametric hook
    with a clear contract.
*)

From Stdlib Require Import String List Bool Arith PeanoNat ZArith Lia.
Import ListNotations.

Module TypeSystem.
  Import TypeCore.

  (* ===== Re‑exports to satisfy the signature ===== *)
  Definition TypeExpr := TypeCore.TypeExpr.
  Definition type_bot : TypeExpr := TypeCore.type_bot.
  Definition type_top : TypeExpr := TypeCore.type_top.
  Definition type_join : TypeExpr -> TypeExpr -> TypeExpr := TypeLattice.join.

  (* Effects as specialized in TYPE_CORE. *)
  Definition SideEffect := TypeCore.SideEffect.   (* = Effect TypeExpr *)
  Definition empty_effect : SideEffect := TypeCore.empty_effect.

  (* ===== Parametric hooks (environment / policy) ===== *)
  (* Map Tac constants to literal values. *)
  Definition ConstV := TS.ConstV.
  Definition UnOpTag : TS.UnOpTag.
  Definition BinOpTag : TS.BinOpTag.
  Definition CmpOpTag : TS.CmpOpTag.
  
  Parameter const_to_literal : ConstV -> LiteralValue.
  (* Resolve string references (e.g., "builtins.list") to concrete types. *)
  Parameter resolve_ref : string -> TypeExpr.
  (* Operator tag → dunder mapping policies. *)
  Parameter unop_to_dunder  : UnOpTag  -> string.
  Parameter binop_to_dunder : BinOpTag -> string * bool (* name, inplace? *).
  Parameter cmpop_to_dunder : CmpOpTag -> string.

  (* ===== Small helpers ===== *)
  Definition join_all (ts:list TypeExpr) : TypeExpr :=
    fold_left type_join ts type_bot.

  (* ClosedRows helper: collect all matches for a query key. *)
  Definition row_collect_matches (rows:ClosedRows) (kq:KeyTy) : list TypeExpr :=
    row_lookup_all rows kq.

  (* ===== Predicates & projections (conservative) ===== *)
  Definition is_overloaded (t:TypeExpr) : bool :=
    match t with TE_Overload _ => true | _ => false end.

  (* All‑arms policy for properties on overloads. *)
  Fixpoint all_fun_props (fs:list TypeExpr) : bool :=
    match fs with
    | [] => true
    | f::fs' => match f with
                | TE_Fun _ _ _ _ ip _ => andb ip (all_fun_props fs')
                | _ => false
                end
    end.

  Definition is_property (t:TypeExpr) : bool :=
    match t with
    | TE_Fun _ _ _ _ ip _ => ip
    | TE_Overload fs => all_fun_props fs
    | _ => false
    end.

  Fixpoint all_bound (fs:list TypeExpr) : bool :=
    match fs with
    | [] => true
    | f::fs' => match f with
                | TE_Fun _ _ _ eff _ _ => andb (se_bound_method eff) (all_bound fs')
                | _ => false
                end
    end.

  Definition is_bound_method (t:TypeExpr) : bool :=
    match t with
    | TE_Fun _ _ _ eff _ _ => se_bound_method eff
    | TE_Overload fs => all_bound fs
    | _ => false
    end.

  Fixpoint any_new_list (fs:list TypeExpr) : bool :=
    match fs with
    | [] => false
    | f::fs' => match f with
                | TE_Fun _ _ _ eff _ _ => orb (se_new eff) (any_new_list fs')
                | _ => any_new_list fs'
                end
    end.

  Fixpoint all_new_list (fs:list TypeExpr) : bool :=
    match fs with
    | [] => true
    | f::fs' => match f with
                | TE_Fun _ _ _ eff _ _ => andb (se_new eff) (all_new_list fs')
                | _ => false
                end
    end.

  Definition any_new (t:TypeExpr) : bool :=
    match t with
    | TE_Fun _ _ _ eff _ _ => se_new eff
    | TE_Overload fs => any_new_list fs
    | _ => false
    end.

  Definition all_new (t:TypeExpr) : bool :=
    match t with
    | TE_Fun _ _ _ eff _ _ => se_new eff
    | TE_Overload fs => all_new_list fs
    | _ => false
    end.

  (* Return type: ⊥ for non‑callables (exposes misuse; callers can widen). *)
  Fixpoint get_return_ (fs:list TypeExpr) : TypeExpr :=
    match fs with
    | [] => type_bot
    | f::fs' => let r := match f with | TE_Fun _ _ ret _ _ _ => ret | _ => type_bot end in
                type_join r (get_return_ fs')
    end.

  Definition get_return (t:TypeExpr) : TypeExpr :=
    match t with
    | TE_Fun _ _ ret _ _ _ => ret
    | TE_Overload fs => get_return_ fs
    | _ => type_bot
    end.

  (* Effect union (safe over‑approx). *)
  Definition effect_union (a b:SideEffect) : SideEffect :=
    {| se_new            := orb (se_new a) (se_new b);
       se_bound_method   := orb (se_bound_method a) (se_bound_method b);
       se_update         := match se_update a, se_update b with
                            | Some u1, Some u2 => Some (type_join u1 u2)
                            | Some u, None | None, Some u => Some u
                            | None, None => None
                            end;
       se_update_indices := se_update_indices a ++ se_update_indices b;
       se_points_to_args := orb (se_points_to_args a) (se_points_to_args b) |}.

  Fixpoint get_side_effect (t:TypeExpr) : SideEffect :=
    match t with
    | TE_Fun _ _ _ eff _ _ => eff
    | TE_Overload fs => fold_left effect_union (map get_side_effect fs) empty_effect
    | _ => empty_effect
    end.

  (* ===== Method binding helper (no default reindexing) ===== *)
  (* Removes first positional parameter and marks bound; defaults are left
     unchanged here (full reindexing should live in the binder impl). *)
  Fixpoint bind_self (receiver:TypeExpr) (method:TypeExpr) : TypeExpr :=
    match method with
    | TE_Fun params defaults ret eff ip tvars =>
        match pr_fixed params with
        | [] => method
        | (KPos 0, _) :: rest =>
            let reindexed := map (fun row =>
              match row with
              | (KPos n,    t) => (KPos (Nat.pred n), t)
              | (KBoth n s, t) => (KBoth (Nat.pred n) s, t)
              | r => r
              end) rest in
            TE_Fun {| pr_star := pr_star params;
                      pr_kwstar := pr_kwstar params;
                      pr_fixed := reindexed |}
                   (* defaults intentionally left [] here *)
                   []
                   ret
                   {| se_new := se_new eff;
                      se_bound_method := true;
                      se_update := se_update eff;
                      se_update_indices := se_update_indices eff;
                      se_points_to_args := se_points_to_args eff |}
                   ip
                   tvars
        | _ => method
        end
    | TE_Overload ms => TE_Overload (map (bind_self receiver) ms)
    | _ => method
    end.
    
  (* ===== Member access (distributes; resolves refs; core+bind variants) ===== *)
  
  (* We only need to resolve references at the *top-level receiver* once.
  After that, recursion is purely structural. *)
  Fixpoint subscr_core_noref (t:TypeExpr) (k:KeyTy) {struct t} : TypeExpr :=
    match t with
    | TE_Module _ rows => mk_overload (row_collect_matches rows k)
    | TE_Class _ rows _ _ _ => mk_overload (row_collect_matches rows k)
    | TE_Instance g _ => subscr_core_noref g k
    | TE_Union ts => join_all (map (fun f => subscr_core_noref f k) ts)
    | TE_Overload fs => mk_overload (map (fun f => subscr_core_noref f k) fs)
    | TE_Ref _ => t (* By design, top-level wrapper resolves refs; subterms needn't. *)
    | _ => type_bot
    end.

  (* Top-level wrapper: resolve a single leading TE_Ref, then use the
  structurally recursive core. *)
  Definition subscr_core (t:TypeExpr) (k:KeyTy) : TypeExpr :=
  match t with
  | TE_Ref s => subscr_core_noref (resolve_ref s) k
  | _ => subscr_core_noref t k
  end.


  Definition subscr (t:TypeExpr) (name:string) : TypeExpr :=
  subscr_core t (KName name).


  Definition subscr_index (t:TypeExpr) (i:nat) : TypeExpr :=
  subscr_core t (KPos i).


  Definition subscr_literal (t:TypeExpr) (c:ConstV) : TypeExpr :=
  match const_to_literal c with
  | L_String s => subscr t s
  | L_Int z => subscr_index t (Z.to_nat z)
  | _ => type_bot
  end.

  (* Attribute access that binds non‑property functions to the receiver. *)
  Definition subscr_bind (receiver:TypeExpr) (name:string) : TypeExpr :=
    let raw := subscr receiver name in
    match raw with
    | TE_Fun _ _ _ _ ip _ => if negb ip then bind_self receiver raw else raw
    | TE_Overload _ => bind_self receiver raw
    | _ => raw
    end.

  (* ===== Call/partial application (delegated) ===== *)
  (* CONTRACT (bind_then_apply):
     Given a callable `f` (fun or overload) and positional args `args`,
     return either (a) a return type when fully applied, or (b) a (possibly
     narrowed) callable for partial application. Must distribute over
     overloads and unions of callees, and be monotone in its arguments. *)
  Parameter bind_then_apply : TypeExpr -> list TypeExpr -> TypeExpr.

  Fixpoint partial_noref (f:TypeExpr) (args:list TypeExpr) {struct f} : TypeExpr :=
    match f with
    | TE_Union ts    => join_all (map (fun u => partial_noref u args) ts)
    | TE_Overload fs => mk_overload (map (fun g => partial_noref g args) fs)
    | TE_Ref s       => f
    | _              => bind_then_apply f args
    end.
    
  Definition partial (f:TypeExpr) (args:list TypeExpr) : TypeExpr :=
    match f with
    | TE_Ref s => partial_noref (resolve_ref s) args
    | _ => partial_noref f args
    end.

  (* ===== Operator conveniences (via mapping policy) ===== *)
  Definition get_unop (t:TypeExpr) (op:string) : TypeExpr :=
    get_return (partial (subscr t op) []).

  Definition partial_binop (lhs rhs:TypeExpr) (op:string) : TypeExpr :=
    get_return (partial (subscr lhs op) [rhs]).

  
  Definition dunder_lookup (info: TS.Dunder) : TypeExpr :=
    match info with
    | TS.TDUnOp  u a         => get_unop a (unop_to_dunder u)
    | TS.TDBinOp b l r _inpl => partial_binop l r (fst (binop_to_dunder b))
    | TS.DCmpOp c l r       => partial_binop l r (cmpop_to_dunder c)
    end.

  (* ===== Literals and builtin constructors ===== *)
  Definition literal_type (k:ConstV) : TypeExpr := TE_Literal (const_to_literal k).

  (* Literal constructors (distinct from class __init__/__new__).
  These are zero- or fixed-arity factory functions that *allocate* new
  objects. They are **not** implemented via attribute lookup; they are
  first-class callable values with se_new=true. *)
  Definition make_list_constructor : TypeExpr := TE_Fun
      {| pr_star := None; pr_kwstar := None; pr_fixed := [] |}
      []
      (TE_Ref "builtins.list")
      {| se_new := true; se_bound_method := false; se_update := None;  se_update_indices := []; se_points_to_args := true |}
      false
      [].


  Definition make_tuple_constructor : TypeExpr := TE_Fun
    {| pr_star := None; pr_kwstar := None; pr_fixed := [] |}
    []
    (TE_Ref "builtins.tuple")
    {| se_new := true; se_bound_method := false; se_update := None; se_update_indices := []; se_points_to_args := true |}
    false
    [].


  Definition make_dict_constructor : TypeExpr := TE_Fun
    {| pr_star := None; pr_kwstar := None; pr_fixed := [] |}
    []
    (TE_Ref "builtins.dict")
    {| se_new := true; se_bound_method := false; se_update := None; se_update_indices := []; se_points_to_args := false |}
    false
    [].


  Definition make_set_constructor : TypeExpr := TE_Fun
    {| pr_star := None; pr_kwstar := None; pr_fixed := [] |}
    [] (TE_Ref "builtins.set")
    {| se_new := true; se_bound_method := false; se_update := None;  se_update_indices := []; se_points_to_args := false |}
    false
    [].


  (* Minimal two-arg slice constructor; extend arity as needed. *)
  Definition make_slice_constructor : TypeExpr := TE_Fun
    {| pr_star := None; pr_kwstar := None; pr_fixed := [(KPos 0, TypeCore.type_any); (KPos 1, TypeCore.type_any)] |}
    []
    (TE_Ref "builtins.slice")
    {| se_new := true; se_bound_method := false; se_update := None; se_update_indices := []; se_points_to_args := false |}
    false
    [].

  (* ===== Callability predicate (strict) ===== *)
  Fixpoint all_funs (fs:list TypeExpr) : bool :=
    match fs with
    | [] => true
    | f::fs' => match f with TE_Fun _ _ _ _ _ _ => all_funs fs' | _ => false end
    end.

  Definition type_is_callable (t:TypeExpr) : bool :=
    match t with
    | TE_Fun _ _ _ _ _ _ => true
    | TE_Overload fs => andb (negb (Nat.eqb (length fs) 0)) (all_funs fs)
    | _ => false
    end.

End TypeSystem.
