(*
  TYPE_CORE.v  — ParamRows & ClosedRows version
  Core type definitions; structural equality (order-sensitive);
  canonicalization (axiomatized, order-insensitive where appropriate);
  well-formedness; and row operations.
*)

From Coq Require Import String List Bool Arith PeanoNat ZArith Lia.
From Coq Require Import Permutation.
Import ListNotations.

Set Implicit Arguments.

Module TypeCore.

Fixpoint inb {A} (eqb: A -> A -> bool) (x:A) (xs:list A) : bool :=
  match xs with
  | [] => false
  | y::ys => if eqb x y then true else inb eqb x ys
  end.

Definition option_map {A B} (f:A->B) (o:option A) : option B :=
  match o with
  | Some x => Some (f x)
  | None => None
  end.

Definition option_eqb {A} (eqb:A->A->bool) (x y:option A) : bool :=
  match x,y with
  | None, None => true
  | Some a, Some b => eqb a b
  | _, _ => false
  end.

Section Keys.

Inductive KeyTy :=
| KPos  (i:nat)              (* exact positional index *)
| KName (s:string)           (* exact field name *)
| KBoth (i:nat) (s:string).  (* exact pair (pos,name) *)

(* Stored key ≤ query key (stored is more precise or equal). *)
Definition key_subsumption (k_store k_query : KeyTy) : bool :=
  match k_store, k_query with
  | KPos i,    KPos j      => Nat.eqb i j
  | KName s,   KName t     => String.eqb s t
  | KBoth i s, KPos  j     => Nat.eqb i j
  | KBoth i s, KName t     => String.eqb s t
  | KBoth i s, KBoth j t   => andb (Nat.eqb i j) (String.eqb s t)
  | _, _ => false
  end.

Definition key_eqb (k1 k2 : KeyTy) : bool :=
  match k1, k2 with
  | KPos i,    KPos j      => Nat.eqb i j
  | KName s,   KName t     => String.eqb s t
  | KBoth i s, KBoth j t   => andb (Nat.eqb i j) (String.eqb s t)
  | _, _ => false
  end.

(* All keys are concrete in this encoding. *)
Definition concrete_key (_:KeyTy) : bool := true.

(* Specificity rank, useful for deterministic “most specific” selection if desired. *)
Definition key_rank (k:KeyTy) : nat :=
  match k with
  | KBoth _ _ => 2
  | KPos _ | KName _ => 1
  end.

Definition key_more_specific (k1 k2:KeyTy) : bool :=
  Nat.ltb (key_rank k2) (key_rank k1).

(* Do two stored keys admit some query key that matches both?
   (Helps WF: avoid ambiguous same-rank overlaps.) *)
Definition keys_overlap (k1 k2:KeyTy) : bool :=
  match k1, k2 with
  | KPos i,    KPos j       => Nat.eqb i j
  | KName s,   KName t      => String.eqb s t
  | KPos i,    KBoth j _    => Nat.eqb i j
  | KBoth j _, KPos i       => Nat.eqb i j
  | KName s,   KBoth _ t    => String.eqb s t
  | KBoth _ t, KName s      => String.eqb s t
  | KBoth i s, KBoth j t    => orb (Nat.eqb i j) (String.eqb s t)
  | _, _ => false
  end.

(* Same-rank overlap is the real source of ambiguity. *)
Definition keys_overlap_same_rank (k1 k2:KeyTy) : bool :=
  andb (keys_overlap k1 k2) (Nat.eqb (key_rank k1) (key_rank k2)).

End Keys.

(** * Literals *)

Inductive LiteralValue : Type :=
| L_Int    : Z -> LiteralValue
| L_Bool   : bool -> LiteralValue
| L_String : string -> LiteralValue
| L_None   : LiteralValue
| L_Tuple  : list LiteralValue -> LiteralValue
| L_List   : list LiteralValue -> LiteralValue.

Fixpoint literal_eqb (l1 l2:LiteralValue) {struct l1} : bool :=
  let fix list_lit_eqb (xs ys:list LiteralValue) : bool :=
      match xs,ys with
      | [],[] => true
      | x::xs', y::ys' => andb (literal_eqb x y) (list_lit_eqb xs' ys')
      | _,_ => false
      end in
  match l1, l2 with
  | L_Int z1,    L_Int z2    => Z.eqb z1 z2
  | L_Bool b1,   L_Bool b2   => Bool.eqb b1 b2
  | L_String s1, L_String s2 => String.eqb s1 s2
  | L_None,      L_None      => true
  | L_Tuple xs,  L_Tuple ys  => list_lit_eqb xs ys
  | L_List  xs,  L_List  ys  => list_lit_eqb xs ys
  | _, _ => false
  end.

Fixpoint literal_size (l:LiteralValue) : nat :=
  let fix list_lit_size (xs:list LiteralValue) : nat :=
      match xs with [] => 0 | x::xs' => literal_size x + list_lit_size xs' end in
  match l with
  | L_Int _ | L_Bool _ | L_String _ | L_None => 1
  | L_Tuple xs | L_List xs => 1 + list_lit_size xs
  end.

(** * Effects (parametric in the contained type) *)

Record Effect (T : Type) := {
  se_new             : bool;
  se_bound_method    : bool;
  se_update          : option T;
  se_update_indices  : list nat;
  se_points_to_args  : bool
}.

(** * Rows and function parameter rows (parametric) *)

Definition ClosedRow_  (Ty:Type) := (KeyTy * Ty)%type.
Definition ClosedRows_ (Ty:Type) := list (ClosedRow_ Ty).

Record ParamRows_ (Ty:Type) := {
  pr_star   : option Ty;            (* *args: element type *)
  pr_kwstar : option Ty;            (* **kwargs: value type *)
  pr_fixed  : ClosedRows_ Ty        (* fixed concrete keys *)
}.

(** * Types (mutually using ParamRows specialized to TypeExpr) *)

(* We’ll specialize these after TypeExpr is introduced. *)
(* The Effect is already parametric. *)

Inductive TypeExpr : Type :=
| TE_Bot
| TE_Top
| TE_Any
| TE_TVar      : nat -> bool -> TypeExpr                 (* id, is_variadic *)
| TE_Literal   : LiteralValue -> TypeExpr
| TE_Union     : list TypeExpr -> TypeExpr
| TE_Fun       : ParamRows_ TypeExpr                     (* params: ParamRows *)
                -> ClosedRows_ TypeExpr                  (* defaults: ClosedRows *)
                -> TypeExpr                              (* return *)
                -> Effect TypeExpr                       (* effects *)
                -> bool                                  (* is_property *)
                -> list nat                              (* tyvars *)
                -> TypeExpr
| TE_Overload  : list TypeExpr -> TypeExpr
| TE_Class     : string
                -> ClosedRows_ TypeExpr                  (* members *)
                -> list TypeExpr                         (* bases *)
                -> bool                                  (* is_protocol *)
                -> list nat                              (* tyvars *)
                -> TypeExpr
| TE_Module    : string -> ClosedRows_ TypeExpr -> TypeExpr
| TE_Instance  : TypeExpr -> list TypeExpr -> TypeExpr
| TE_Ref       : string -> TypeExpr.

(* Concrete specializations used throughout. *)
Definition ClosedRow  := ClosedRow_  TypeExpr.
Definition ClosedRows := ClosedRows_ TypeExpr.
Definition ParamRows  := ParamRows_  TypeExpr.
Definition SideEffect := Effect TypeExpr.

(* A few constants *)
Definition type_bot : TypeExpr := TE_Bot.
Definition type_top : TypeExpr := TE_Top.
Definition type_any : TypeExpr := TE_Any.

(* Sizes (for future termination measures). *)
Definition effect_size (e : SideEffect) : nat := 1.


Fixpoint size (t : TypeExpr) {struct t} : nat :=
  (* list size: +1 per cons, plus the element's size *)
  let fix list_sz (ts : list TypeExpr) {struct ts} : nat :=
      match ts with
      | [] => 0
      | t' :: ts' => 1 + size t' + list_sz ts'
      end in
  (* rows size: +1 per row, plus the field type's size *)
  let fix rows_sz (rows : ClosedRows) {struct rows} : nat :=
      match rows with
      | [] => 0
      | (_, t') :: rs' => 1 + size t' + rows_sz rs'
      end in
  (* option size: charge 1 even for None, 1 + size for Some *)
  let opt_sz (o : option TypeExpr) : nat :=
      match o with
      | None => 1
      | Some x => 1 + size x
      end in
  match t with
  | TE_Bot | TE_Top | TE_Any | TE_TVar _ _ | TE_Ref _ => 1
  | TE_Literal l => 1 + literal_size l
  | TE_Union ts => 1 + list_sz ts
  | TE_Fun params defaults ret eff _ tvars =>
      1
      + rows_sz (pr_fixed params)
      + opt_sz (pr_star params)
      + opt_sz (pr_kwstar params)
      + rows_sz defaults
      + size ret
      + effect_size eff
      + length tvars
  | TE_Overload fs => 1 + list_sz fs
  | TE_Class _ members bases _ tvars =>
      1 + rows_sz members + list_sz bases + length tvars
  | TE_Module _ members =>
      1 + rows_sz members
  | TE_Instance g args =>
      1 + size g + list_sz args
  end.

Fixpoint rows_size (rows : ClosedRows) : nat :=
  match rows with
  | [] => 0
  | (_, t) :: rs => 1 + size t + rows_size rs
  end.

Fixpoint list_size (ts : list TypeExpr) : nat :=
  match ts with
  | [] => 0
  | t :: ts' => 1 + size t + list_size ts'
  end.
  
Lemma list_size_cons_le :
  forall (x:TypeExpr) xs, size x <= list_size (x::xs).
Proof. simpl; lia. Qed.


(** * Structural equality (order-sensitive on syntax) *)

Fixpoint type_eqb_lin (t1 t2 : TypeExpr) {struct t1} : bool :=
  let fix list_eqb_ty (xs ys : list TypeExpr) {struct xs} : bool :=
    match xs, ys with
    | [], [] => true
    | x::xs', y::ys' => andb (type_eqb_lin x y) (list_eqb_ty xs' ys')
    | _, _ => false
    end in
  let fix list_eqb_row (xs ys : list ClosedRow) {struct xs} : bool :=
    match xs, ys with
    | [], [] => true
    | (k1,t1')::xs', (k2,t2')::ys' =>
        andb (key_eqb k1 k2)
             (andb (type_eqb_lin t1' t2') (list_eqb_row xs' ys'))
    | _, _ => false
    end in
  let fix list_eqb_nat (xs ys : list nat) {struct xs} : bool :=
    match xs, ys with
    | [], [] => true
    | n::xs', m::ys' => andb (Nat.eqb n m) (list_eqb_nat xs' ys')
    | _, _ => false
    end in
  let effect_eqb_lin (e1 e2 : SideEffect) : bool :=
    andb (Bool.eqb (se_new e1) (se_new e2))
      (andb (Bool.eqb (se_bound_method e1) (se_bound_method e2))
        (andb (match se_update e1, se_update e2 with
               | None, None => true
               | Some x, Some y => type_eqb_lin x y
               | _, _ => false
               end)
              (andb (list_eqb_nat (se_update_indices e1) (se_update_indices e2))
                    (Bool.eqb (se_points_to_args e1) (se_points_to_args e2))))) in
  let param_rows_eqb (p1 p2:ParamRows) : bool :=
    andb (option_eqb type_eqb_lin (pr_star p1) (pr_star p2))
      (andb (option_eqb type_eqb_lin (pr_kwstar p1) (pr_kwstar p2))
            (list_eqb_row (pr_fixed p1) (pr_fixed p2))) in
  match t1, t2 with
  | TE_Bot, TE_Bot => true
  | TE_Top, TE_Top => true
  | TE_Any, TE_Any => true
  | TE_TVar x1 v1, TE_TVar x2 v2 => andb (Nat.eqb x1 x2) (Bool.eqb v1 v2)
  | TE_Ref s1, TE_Ref s2 => String.eqb s1 s2
  | TE_Literal l1, TE_Literal l2 => literal_eqb l1 l2
  | TE_Union ts1,    TE_Union ts2    => list_eqb_ty  ts1 ts2
  | TE_Fun p1 d1 r1 e1 ip1 tv1, TE_Fun p2 d2 r2 e2 ip2 tv2 =>
      andb (param_rows_eqb p1 p2)
        (andb (list_eqb_row d1 d2)
        (andb (type_eqb_lin r1 r2)
        (andb (effect_eqb_lin e1 e2)
              (andb (Bool.eqb ip1 ip2) (list_eqb_nat tv1 tv2)))))
  | TE_Overload fs1, TE_Overload fs2 => list_eqb_ty fs1 fs2
  | TE_Class n1 m1 b1 pr1 tv1, TE_Class n2 m2 b2 pr2 tv2 =>
      andb (String.eqb n1 n2)
        (andb (list_eqb_row m1 m2)
              (andb (list_eqb_ty b1 b2)
                    (andb (Bool.eqb pr1 pr2) (list_eqb_nat tv1 tv2))))
  | TE_Module n1 m1, TE_Module n2 m2 =>
      andb (String.eqb n1 n2) (list_eqb_row m1 m2)
  | TE_Instance g1 a1, TE_Instance g2 a2 =>
      andb (type_eqb_lin g1 g2) (list_eqb_ty a1 a2)
  | _, _ => false
  end.

(** * Canonicalization (axiomatized) *)

Parameter normalize_type : TypeExpr -> TypeExpr.

Definition mk_union (ts : list TypeExpr) : TypeExpr :=
  normalize_type (TE_Union ts).

Definition mk_overload (fs : list TypeExpr) : TypeExpr :=
  normalize_type (TE_Overload fs).

Definition mk_fun
  (ps : ParamRows) (ds : ClosedRows) (ret : TypeExpr) (eff : SideEffect)
  (is_prop : bool) (tvs : list nat) : TypeExpr :=
  normalize_type (TE_Fun ps ds ret eff is_prop tvs).

Definition type_eqb (t1 t2 : TypeExpr) : bool :=
  type_eqb_lin (normalize_type t1) (normalize_type t2).

Definition rowpair_eqb (r1 r2 : ClosedRow) : bool :=
  match r1, r2 with
  | (k1,t1), (k2,t2) => andb (key_eqb k1 k2) (type_eqb t1 t2)
  end.

(* --- Algebraic laws for normalization --- *)

Axiom normalize_idem :
  forall t, normalize_type (normalize_type t) = normalize_type t.

Axiom normalize_Bot  : normalize_type TE_Bot = TE_Bot.
Axiom normalize_Top  : normalize_type TE_Top = TE_Top.
Axiom normalize_Any  : normalize_type TE_Any = TE_Any.
Axiom normalize_TVar : forall n v, normalize_type (TE_TVar n v) = TE_TVar n v.
Axiom normalize_Ref  : forall s,   normalize_type (TE_Ref s)   = TE_Ref s.
Axiom normalize_Lit  : forall l,   normalize_type (TE_Literal l) = TE_Literal l.

Axiom norm_union_perm :
  forall ts us,
    Permutation ts us ->
    normalize_type (TE_Union ts) = normalize_type (TE_Union us).

Axiom norm_overload_perm :
  forall fs gs,
    Permutation fs gs ->
    normalize_type (TE_Overload fs) = normalize_type (TE_Overload gs).

Axiom norm_union_idemp :
  forall ts, normalize_type (TE_Union (ts ++ ts)) = normalize_type (TE_Union ts).

Axiom norm_union_flat :
  forall xs ys,
    normalize_type (TE_Union (TE_Union xs :: ys))
    = normalize_type (TE_Union (xs ++ ys)).

Axiom norm_union_unit0 :
  normalize_type (TE_Union []) = TE_Bot.

Axiom norm_union_single :
  forall t, normalize_type (TE_Union [t]) = normalize_type t.

Axiom norm_union_map :
  forall ts,
    normalize_type (TE_Union (map normalize_type ts))
    = normalize_type (TE_Union ts).

Axiom norm_over_idemp :
  forall fs, normalize_type (TE_Overload (fs ++ fs)) = normalize_type (TE_Overload fs).

Axiom norm_over_flat :
  forall xs ys,
    normalize_type (TE_Overload (TE_Overload xs :: ys))
    = normalize_type (TE_Overload (xs ++ ys)).

Axiom norm_over_filter :
  forall fs,
    normalize_type (TE_Overload fs)
    = normalize_type (TE_Overload
         (filter (fun t => match t with TE_Fun _ _ _ _ _ _ => true | _ => false end) fs)).

Axiom norm_over_unit0 :
  normalize_type (TE_Overload []) = TE_Overload [].

Axiom norm_over_map :
  forall fs,
    normalize_type (TE_Overload (map normalize_type fs))
    = normalize_type (TE_Overload fs).

Axiom norm_instance_cong :
  forall g args,
    normalize_type (TE_Instance g args)
    = normalize_type (TE_Instance (normalize_type g) (map normalize_type args)).

Axiom type_eqb_normalize :
  forall t1 t2, type_eqb t1 t2 = true <-> normalize_type t1 = normalize_type t2.

(** * Row canonicalizer (closed rows) *)

Parameter rows_canon : ClosedRows -> ClosedRows.

Axiom rows_canon_wf   : forall (rs: ClosedRows), True -> True.  (* wf proof obligations are given below and referred to here *)
Axiom rows_canon_idem : forall rs, rows_canon (rows_canon rs) = rows_canon rs.

Axiom rows_canon_sound :
  forall rs k t,
    inb rowpair_eqb (k,t) (rows_canon rs) = true ->
    exists t0, inb rowpair_eqb (k,t0) rs = true /\ type_eqb t t0 = true.

Axiom rows_canon_complete :
  forall rs k t,
    inb rowpair_eqb (k,t) rs = true ->
    exists t', inb rowpair_eqb (k,t') (rows_canon rs) = true /\ type_eqb t t' = true.

(* Normalize types inside rows; leave keys intact. *)
Definition map_row_norm (rs:ClosedRows) : ClosedRows :=
  map (fun '(k,t) => (k, normalize_type t)) rs.

(* Normalize inside ParamRows. *)
Definition map_paramrows_norm (p:ParamRows) : ParamRows :=
  {| pr_star   := option_map normalize_type (pr_star p);
     pr_kwstar := option_map normalize_type (pr_kwstar p);
     pr_fixed  := rows_canon (map_row_norm (pr_fixed p)) |}.

(* Functions: normalize children, canonicalize rows, preserve ip. *)
Axiom norm_fun_cong :
  forall ps ds r eff ip tvs,
    exists ps' ds' r' eff',
      normalize_type (TE_Fun ps ds r eff ip tvs)
      = TE_Fun ps' ds' r' eff' ip tvs
      /\ ps' = map_paramrows_norm ps
      /\ ds' = rows_canon (map_row_norm ds)
      /\ r'  = normalize_type r
      /\ se_new eff'              = se_new eff
      /\ se_bound_method eff'     = se_bound_method eff
      /\ se_update_indices eff'   = se_update_indices eff
      /\ se_points_to_args eff'   = se_points_to_args eff
      /\ se_update eff'           = option_map normalize_type (se_update eff).

(* Classes: normalize children and rows, canonicalize rows, preserve name/protocol. *)
Axiom norm_class_cong :
  forall n rs bs pr tvs,
    exists ms' bs' tvs',
      normalize_type (TE_Class n rs bs pr tvs)
      = TE_Class n ms' bs' pr tvs'
      /\ ms' = rows_canon (map_row_norm rs)
      /\ bs' = map normalize_type bs.

(* Modules: normalize members, canonicalize rows, preserve name. *)
Axiom norm_module_cong :
  forall n rs,
    exists ms',
      normalize_type (TE_Module n rs)
      = TE_Module n ms'
      /\ ms' = rows_canon (map_row_norm rs).

(** * Utilities over closed rows and param rows *)

Definition rows_to_types (rows:ClosedRows) : list TypeExpr := map snd rows.

Definition types_to_rows (ts:list TypeExpr) : ClosedRows :=
  combine (map KPos (seq 0 (length ts))) ts.

Definition make_row (n:nat) (name:option string) (t:TypeExpr) : ClosedRow :=
  match name with
  | Some s => (KBoth n s, t)
  | None   => (KPos n,    t)
  end.

(* ClosedRows ops *)
Fixpoint row_first_match (rows:ClosedRows) (kq:KeyTy) : option TypeExpr :=
  match rows with
  | [] => None
  | (ks,t)::rs => if key_subsumption ks kq then Some t else row_first_match rs kq
  end.

Fixpoint row_lookup_all (rows:ClosedRows) (kq:KeyTy) : list TypeExpr :=
  match rows with
  | [] => []
  | (ks,t)::rs =>
      if key_subsumption ks kq then t :: row_lookup_all rs kq
      else row_lookup_all rs kq
  end.

Definition row_has_key (rows:ClosedRows) (kq:KeyTy) : bool :=
  match row_first_match rows kq with Some _ => true | None => false end.

Fixpoint row_domain (rows:ClosedRows) : list KeyTy :=
  match rows with [] => [] | (k,_)::rs => k :: row_domain rs end.

Fixpoint row_remove (rows:ClosedRows) (k:KeyTy) : ClosedRows :=
  match rows with
  | [] => []
  | (k',t)::rs => if key_eqb k k' then row_remove rs k else (k',t)::row_remove rs k
  end.

Definition row_add (rows:ClosedRows) (k:KeyTy) (t:TypeExpr) : ClosedRows :=
  (k,t) :: row_remove rows k.

Definition row_update (rows:ClosedRows) (k:KeyTy) (t:TypeExpr) : ClosedRows :=
  row_add rows k t.

(* ParamRows lookup: try fixed first; fall back to appropriate tail. *)
Definition param_lookup (ps:ParamRows) (kq:KeyTy) : option TypeExpr :=
  match row_first_match (pr_fixed ps) kq with
  | Some t => Some t
  | None =>
    match kq with
    | KPos _    => pr_star ps
    | KName _   => pr_kwstar ps
    | KBoth _ _ => pr_kwstar ps  (* names dominate in mixed queries *)
    end
  end.

Definition param_has_key (ps:ParamRows) (kq:KeyTy) : bool :=
  match param_lookup ps kq with Some _ => true | None => false end.

(** * Well-formedness (boolean) *)

(* No exact duplicate keys in a closed row (by key_eqb). *)
Fixpoint wf_rows_no_dup_keys_aux (seen:list KeyTy) (rows:ClosedRows) : bool :=
  match rows with
  | [] => true
  | (k,_)::rs =>
      if inb key_eqb k seen
      then false
      else wf_rows_no_dup_keys_aux (k::seen) rs
  end.

Definition wf_rows_no_dup_keys (rows:ClosedRows) : bool :=
  wf_rows_no_dup_keys_aux [] rows.

(* No ambiguous same-rank overlaps among stored keys. *)
Fixpoint wf_rows_no_overlap_same_rank (rows:ClosedRows) : bool :=
  match rows with
  | [] => true
  | (k,_)::rs =>
      andb (forallb (fun '(k',_) => negb (keys_overlap_same_rank k k')) rs)
           (wf_rows_no_overlap_same_rank rs)
  end.

(* Store rows are closed & concrete; in this encoding all keys are concrete. *)
Definition wf_rows_store (rows:ClosedRows) : bool :=
  andb (wf_rows_no_dup_keys rows) (wf_rows_no_overlap_same_rank rows).

(* Types-only check on rows. *)
Definition keys_subset (xs ys:list KeyTy) : bool :=
  let fix go xs :=
      match xs with
      | [] => true
      | k::ks => if inb key_eqb k ys then go ks else false
      end in go xs.

(* Defaults ⊆ params (by key) *)
Definition rows_keys (rows:ClosedRows) : list KeyTy := map fst rows.
Fixpoint wf_type (t:TypeExpr) {struct t} : bool :=
  match t with
  | TE_Bot | TE_Top | TE_Any | TE_TVar _ _ | TE_Ref _ => true
  | TE_Literal _ => true

  | TE_Union ts =>
      let fix go (xs:list TypeExpr) :=
        match xs with
        | [] => true
        | x::xs' => andb (wf_type x) (go xs')
        end in
      go ts

  | TE_Fun ps ds r _ _ _ =>
      (* shape checks *)
      let pr_ok :=
        andb (wf_rows_store (pr_fixed ps))
             (andb (match pr_star ps   with None => true | Some t0 => wf_type t0 end)
                   (match pr_kwstar ps with None => true | Some t0 => wf_type t0 end)) in
      let ds_shape_ok :=
        andb (wf_rows_store ds)
             (keys_subset (rows_keys ds) (rows_keys (pr_fixed ps))) in
      (* types-inside checks, done via local recursion over rows *)
      let fix rows_types (rs:ClosedRows) :=
        match rs with
        | [] => true
        | (_,ty)::rs' => andb (wf_type ty) (rows_types rs')
        end in
      andb (andb pr_ok ds_shape_ok)
           (andb (rows_types (pr_fixed ps))
                 (andb (rows_types ds) (wf_type r)))

  | TE_Overload fs =>
      let fix go (xs:list TypeExpr) :=
        match xs with
        | [] => true
        | x::xs' => andb (wf_type x) (go xs')
        end in
      go fs

  | TE_Class _ ms bs _ _ =>
      let fix rows_types (rs:ClosedRows) :=
        match rs with
        | [] => true
        | (_,ty)::rs' => andb (wf_type ty) (rows_types rs')
        end in
      andb (andb (wf_rows_store ms) (rows_types ms))
           (let fix go (xs:list TypeExpr) :=
              match xs with
              | [] => true
              | x::xs' => andb (wf_type x) (go xs')
              end in
            go bs)

  | TE_Module _ ms =>
      let fix rows_types (rs:ClosedRows) :=
        match rs with
        | [] => true
        | (_,ty)::rs' => andb (wf_type ty) (rows_types rs')
        end in
      andb (wf_rows_store ms) (rows_types ms)

  | TE_Instance g as' =>
      let fix go (xs:list TypeExpr) :=
        match xs with
        | [] => true
        | x::xs' => andb (wf_type x) (go xs')
        end in
      andb (wf_type g) (go as')
  end.


Definition wf_param_rows (ps:ParamRows) : bool :=
  andb (wf_rows_store (pr_fixed ps))
       (andb (match pr_star ps with None => true | Some t => wf_type t end)
             (match pr_kwstar ps with None => true | Some t => wf_type t end)).

Definition wf_fun (ps:ParamRows) (ds:ClosedRows) : bool :=
  andb (wf_param_rows ps)
       (andb (wf_rows_store ds)
             (keys_subset (rows_keys ds) (rows_keys (pr_fixed ps)))).

(** * Coarser "shape" facts (axioms) *)

Axiom norm_fun_shape :
  forall ps ds r eff ip tvs,
    match normalize_type (TE_Fun ps ds r eff ip tvs) with
    | TE_Fun ps' ds' r' eff' ip' tvs' =>
        wf_rows_store (pr_fixed ps') = true /\
        wf_rows_store ds' = true /\
        keys_subset (rows_keys ds') (rows_keys (pr_fixed ps')) = true /\
        ip' = ip
    | _ => False
    end.

Axiom norm_class_shape :
  forall n rs b pr tvs,
    match normalize_type (TE_Class n rs b pr tvs) with
    | TE_Class n' ms' b' pr' tvs' =>
        n' = n /\ pr' = pr /\ wf_rows_store ms' = true
    | _ => False
    end.

Axiom norm_module_shape :
  forall n rs,
    match normalize_type (TE_Module n rs) with
    | TE_Module n' ms' =>
        n' = n /\ wf_rows_store ms' = true
    | _ => False
    end.

(** * Predicates (shape) *)

Definition is_function (t:TypeExpr) : bool :=
  match t with TE_Fun _ _ _ _ _ _ => true | _ => false end.

Definition is_overloaded (t:TypeExpr) : bool :=
  match t with TE_Overload _ => true | _ => false end.

Definition is_class (t:TypeExpr) : bool :=
  match t with TE_Class _ _ _ _ _ => true | _ => false end.

Definition is_module (t:TypeExpr) : bool :=
  match t with TE_Module _ _ => true | _ => false end.

Definition is_protocol (t:TypeExpr) : bool :=
  match t with TE_Class _ _ _ true _ => true | _ => false end.

(** * Defaults for effects *)

Definition empty_effect : SideEffect := {|
  se_new := false;
  se_bound_method := false;
  se_update := None;
  se_update_indices := [];
  se_points_to_args := false
|}.

End TypeCore.
