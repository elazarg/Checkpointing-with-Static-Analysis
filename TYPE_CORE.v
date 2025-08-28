(*
  TYPE_CORE.v
  Core type definitions; structural equality (order-sensitive);
  canonicalization (axiomatized, order-insensitive where appropriate);
  well-formedness;
  and row operations.
*)
From Coq Require Import String List Bool Arith PeanoNat ZArith.
From Coq Require Import Permutation.
Import ListNotations.

Set Implicit Arguments.

Module TypeCore.

(* Small helper the rest of the file uses once or twice. *)
Fixpoint inb {A} (eqb: A -> A -> bool) (x:A) (xs:list A) : bool :=
  match xs with
  | [] => false
  | y::ys => if eqb x y then true else inb eqb x ys
  end.

(* Total, self-contained option_map (avoids relying on Coq version). *)
Definition option_map {A B} (f:A->B) (o:option A) : option B :=
  match o with
  | Some x => Some (f x)
  | None => None
  end.

(* --------------------------------------------------------------- *)
(** * Keys / Rows / Effects / Types *)
(* --------------------------------------------------------------- *)

(** ** Keys *)

Inductive KeyTy :=
| KPos  (i:nat)              (* exact positional index *)
| KName (s:string)           (* exact field name *)
| KBoth (i:nat) (s:string)   (* exact pair (pos,name) *)
| KAnyPos                    (* unknown nat: matches any positional key *)
| KAnyName.                  (* unknown string: matches any name key *)

(* Stored key ≤ query key (stored is more precise or equal). *)
Definition key_subsumption (k_store k_query : KeyTy) : bool :=
  match k_store, k_query with
  | KPos i,    KPos j      => Nat.eqb i j
  | KPos _,    KAnyPos     => true
  | KName s,   KName t     => String.eqb s t
  | KName _,   KAnyName    => true
  | KBoth i s, KPos  j     => Nat.eqb i j
  | KBoth i s, KName t     => String.eqb s t
  | KBoth i s, KBoth j t   => andb (Nat.eqb i j) (String.eqb s t)
  | KBoth _ _, KAnyPos     => true
  | KBoth _ _, KAnyName    => true
  | _, _ => false
  end.

Definition key_eqb (k1 k2 : KeyTy) : bool :=
  match k1, k2 with
  | KPos i,    KPos j      => Nat.eqb i j
  | KName s,   KName t     => String.eqb s t
  | KBoth i s, KBoth j t   => andb (Nat.eqb i j) (String.eqb s t)
  | KAnyPos,   KAnyPos     => true
  | KAnyName,  KAnyName    => true
  | _, _ => false
  end.

Definition concrete_key (k:KeyTy) : bool :=
  match k with KAnyPos | KAnyName => false | _ => true end.

(** ** Literals *)

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

(** ** Effects *)

Record Effect (T : Type) := {
  se_new             : bool;
  se_bound_method    : bool;
  se_update          : option T;
  se_update_indices  : list nat;
  se_points_to_args  : bool
}.

Definition empty_effect : SideEffect := {|
  se_new := false;
  se_bound_method := false;
  se_update := None;
  se_update_indices := [];
  se_points_to_args := false
|}.

(** ** Types *)

Inductive TypeExpr : Type :=
| TE_Bot
| TE_Top
| TE_Any
| TE_TVar      : nat -> bool -> TypeExpr                 (* id, is_variadic *)
| TE_Literal   : LiteralValue -> TypeExpr
| TE_Union     : list TypeExpr -> TypeExpr               (* canonicalized by mk_union *)
| TE_Fun       : list (KeyTy * TypeExpr)                 (* params *)
                -> list (KeyTy * TypeExpr)               (* defaults *)
                -> TypeExpr                              (* return *)
                -> Effect TypeExpr                       (* effects *)
                -> bool                                  (* is_property *)
                -> list nat                              (* tyvars *)
                -> TypeExpr
| TE_Overload  : list TypeExpr -> TypeExpr               (* invariant: all TE_Fun; canonical by mk_overload *)
| TE_Class     : string
                -> list (KeyTy * TypeExpr)               (* members *)
                -> list TypeExpr                         (* bases *)
                -> bool                                  (* is_protocol *)
                -> list nat                              (* tyvars *)
                -> TypeExpr
| TE_Module    : string -> list (KeyTy * TypeExpr) -> TypeExpr
| TE_Instance  : TypeExpr -> list TypeExpr -> TypeExpr
| TE_Ref       : string -> TypeExpr.

Definition Row  := (KeyTy * TypeExpr)%type.
Definition Rows := list Row.
Definition SideEffect := Effect TypeExpr.

(* A few constants *)
Definition type_bot : TypeExpr := TE_Bot.
Definition type_top : TypeExpr := TE_Top.
Definition type_any : TypeExpr := TE_Any.

(* Sizes for future termination arguments. *)
Definition effect_size (e : SideEffect) : nat := 1.

Fixpoint size (t : TypeExpr) {struct t} : nat :=
  let fix list_sz (ts : list TypeExpr) : nat :=
      match ts with
      | [] => 0
      | t' :: ts' => size t' + list_sz ts'
      end in
  let fix rows_sz (rows : Rows) : nat :=
      match rows with
      | [] => 0
      | (_, t') :: rs' => 1 + size t' + rows_sz rs'
      end in
  match t with
  | TE_Bot | TE_Top | TE_Any | TE_TVar _ _ | TE_Ref _ => 1
  | TE_Literal l => 1 + literal_size l
  | TE_Union ts => 1 + list_sz ts
  | TE_Fun params defaults ret eff _ tvars =>
      1 + rows_sz params + rows_sz defaults + size ret + effect_size eff + length tvars
  | TE_Overload fs => 1 + list_sz fs
  | TE_Class _ members bases _ tvars =>
      1 + rows_sz members + list_sz bases + length tvars
  | TE_Module _ members => 1 + rows_sz members
  | TE_Instance g args => 1 + size g + list_sz args
  end.

(** * Structural equality (order-sensitive on syntax) *)

Fixpoint type_eqb_lin (t1 t2 : TypeExpr) {struct t1} : bool :=
  let fix list_eqb_ty (xs ys : list TypeExpr) {struct xs} : bool :=
    match xs, ys with
    | [], [] => true
    | x::xs', y::ys' => andb (type_eqb_lin x y) (list_eqb_ty xs' ys')
    | _, _ => false
    end in
  let fix list_eqb_row (xs ys : list Row) {struct xs} : bool :=
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
  match t1, t2 with
  | TE_Bot, TE_Bot => true
  | TE_Top, TE_Top => true
  | TE_Any, TE_Any => true
  | TE_TVar x1 v1, TE_TVar x2 v2 => andb (Nat.eqb x1 x2) (Bool.eqb v1 v2)
  | TE_Ref s1, TE_Ref s2 => String.eqb s1 s2
  | TE_Literal l1, TE_Literal l2 => literal_eqb l1 l2
  | TE_Union ts1,    TE_Union ts2    => list_eqb_ty  ts1 ts2
  | TE_Fun p1 d1 r1 e1 ip1 tv1, TE_Fun p2 d2 r2 e2 ip2 tv2 =>
      andb (list_eqb_row p1 p2)
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

(* Implementation note: normalize_type must:
   - Flatten nested unions/overloads
   - Remove duplicates (by type_eqb_lin)
   - Sort for canonical order (optional but helpful)
   - Preserve single-element unwrapping
   
   A simple implementation would:
   1. Recursively normalize children
   2. Flatten same-constructor nesting  
   3. Sort and deduplicate
*)

(* Normalization to canonical form (abstract). *)
Parameter normalize_type : TypeExpr -> TypeExpr.

(* Canonical builders. *)
Definition mk_union (ts : list TypeExpr) : TypeExpr :=
  normalize_type (TE_Union ts).

Definition mk_overload (fs : list TypeExpr) : TypeExpr :=
  normalize_type (TE_Overload fs).

Definition mk_fun
  (ps ds : Rows) (ret : TypeExpr) (eff : SideEffect)
  (is_prop : bool) (tvs : list nat) : TypeExpr :=
  normalize_type (TE_Fun ps ds ret eff is_prop tvs).

(* Extensional equality is structural equality on normalized forms. *)
Definition type_eqb (t1 t2 : TypeExpr) : bool :=
  type_eqb_lin (normalize_type t1) (normalize_type t2).

(* Row pair equality that respects type normalization. *)
Definition rowpair_eqb (r1 r2 : Row) : bool :=
  match r1, r2 with
  | (k1,t1), (k2,t2) => andb (key_eqb k1 k2) (type_eqb t1 t2)
  end.

(* --- Algebraic laws for normalization --- *)

(* Idempotence *)
Axiom normalize_idem :
  forall t, normalize_type (normalize_type t) = normalize_type t.

(* Stability on base constructors *)
Axiom normalize_Bot  : normalize_type TE_Bot = TE_Bot.
Axiom normalize_Top  : normalize_type TE_Top = TE_Top.
Axiom normalize_Any  : normalize_type TE_Any = TE_Any.
Axiom normalize_TVar : forall n v, normalize_type (TE_TVar n v) = TE_TVar n v.
Axiom normalize_Ref  : forall s,   normalize_type (TE_Ref s)   = TE_Ref s.
Axiom normalize_Lit  : forall l,   normalize_type (TE_Literal l) = TE_Literal l.

(* Unions behave like finite sets (comm/assoc/idemp; flattening; unit; map). *)
Axiom norm_union_perm :
  forall ts us,
    Permutation ts us ->
    normalize_type (TE_Union ts) = normalize_type (TE_Union us).
    
(* Overloads behave like finite intersections of functions
   (comm/assoc/idemp; flattening; functions-only; chosen unit; map). *)
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

(* Drop non-functions from overloads. *)
Axiom norm_over_filter :
  forall fs,
    normalize_type (TE_Overload fs)
    = normalize_type (TE_Overload
         (filter (fun t => match t with TE_Fun _ _ _ _ _ _ => true | _ => false end) fs)).

(* Empty overload is the designated top-callable. *)
Axiom norm_over_unit0 :
  normalize_type (TE_Overload []) = TE_Overload [].

Axiom norm_over_map :
  forall fs,
    normalize_type (TE_Overload (map normalize_type fs))
    = normalize_type (TE_Overload fs).

(* Instances: normalize under the constructor. *)
Axiom norm_instance_cong :
  forall g args,
    normalize_type (TE_Instance g args)
    = normalize_type (TE_Instance (normalize_type g) (map normalize_type args)).

(* Extensional equality ↔ normalized-form equality. *)
Axiom type_eqb_normalize :
  forall t1 t2, type_eqb t1 t2 = true <-> normalize_type t1 = normalize_type t2.


(* No exact duplicate keys in a row (by key_eqb). *)
Fixpoint wf_rows_no_dup_keys_aux (seen:list KeyTy) (rows:Rows) : bool :=
  match rows with
  | [] => true
  | (k,_)::rs =>
      if inb key_eqb k seen
      then false
      else wf_rows_no_dup_keys_aux (k::seen) rs
  end.

Definition wf_rows_no_dup_keys (rows:Rows) : bool :=
  wf_rows_no_dup_keys_aux [] rows.


(* Keys stored in rows must be concrete (no KAny). *)
Definition wf_key_store (k:KeyTy) : bool :=
  match k with KAnyPos | KAnyName => false | _ => true end.

Fixpoint wf_rows_concrete (rows:Rows) : bool :=
  match rows with
  | [] => true
  | (k,_)::rs => andb (wf_key_store k) (wf_rows_concrete rs)
  end.

Definition wf_rows_store (rows:Rows) : bool :=
  andb (wf_rows_concrete rows) (wf_rows_no_dup_keys rows).

(* --------------------------------------------------------------- *)
(** * Row canonicalizer (abstract) and congruence axioms *)
(* --------------------------------------------------------------- *)

(* Canonicalizer for rows (dedup/filter/order as you like). *)
Parameter rows_canon : Rows -> Rows.

Axiom rows_canon_wf   : forall rs, wf_rows_store rs = true -> wf_rows_store (rows_canon rs) = true.
Axiom rows_canon_idem : forall rs, rows_canon (rows_canon rs) = rows_canon rs.

(* Sound/complete wrt membership up to type normalization. *)
Axiom rows_canon_sound :
  forall rs k t,
    inb rowpair_eqb (k,t) (rows_canon rs) = true ->
    exists t0, inb rowpair_eqb (k,t0) rs = true /\ type_eqb t t0 = true.

Axiom rows_canon_complete :
  forall rs k t,
    inb rowpair_eqb (k,t) rs = true ->
    exists t', inb rowpair_eqb (k,t') (rows_canon rs) = true /\ type_eqb t t' = true.

(* Helper: normalize the types inside rows, leave keys intact. *)
Definition map_row_norm (rs:Rows) : Rows :=
  map (fun '(k,t) => (k, normalize_type t)) rs.

(* Functions: normalize children and rows, drop KAny*, canonicalize rows, preserve ip. *)
Axiom norm_fun_cong :
  forall ps ds r eff ip tvs,
    exists ps' ds' r' eff',
      normalize_type (TE_Fun ps ds r eff ip tvs)
      = TE_Fun ps' ds' r' eff' ip tvs
      /\ ps' = rows_canon (map_row_norm (filter (fun '(k,_) => concrete_key k) ps))
      /\ ds' = rows_canon (map_row_norm (filter (fun '(k,_) => concrete_key k) ds))
      /\ r'  = normalize_type r
      /\ se_new eff'              = se_new eff
      /\ se_bound_method eff'     = se_bound_method eff
      /\ se_update_indices eff'   = se_update_indices eff
      /\ se_points_to_args eff'   = se_points_to_args eff
      /\ se_update eff'           = option_map normalize_type (se_update eff).

(* Classes: normalize children and rows, drop KAny*, canonicalize rows, preserve name/protocol. *)
Axiom norm_class_cong :
  forall n rs bs pr tvs,
    exists ms' bs' tvs',
      normalize_type (TE_Class n rs bs pr tvs)
      = TE_Class n ms' bs' pr tvs'
      /\ ms' = rows_canon (map_row_norm (filter (fun '(k,_) => concrete_key k) rs))
      /\ bs' = map normalize_type bs.

(* Modules: normalize members, drop KAny*, canonicalize rows, preserve name. *)
Axiom norm_module_cong :
  forall n rs,
    exists ms',
      normalize_type (TE_Module n rs)
      = TE_Module n ms'
      /\ ms' = rows_canon (map_row_norm (filter (fun '(k,_) => concrete_key k) rs)).

Definition keys_subset (xs ys:list KeyTy) : bool :=
  let fix go xs :=
      match xs with
      | [] => true
      | k::ks => if inb key_eqb k ys then go ks else false
      end in go xs.

(* Defaults ⊆ params (by key). *)
Definition rows_keys (rows:Rows) : list KeyTy := map fst rows.

(* Coarser shape facts (derivable from the congruence axioms), left as axioms for convenience. *)
Axiom norm_fun_shape :
  forall ps ds r eff ip tvs,
    match normalize_type (TE_Fun ps ds r eff ip tvs) with
    | TE_Fun ps' ds' r' eff' ip' tvs' =>
        wf_rows_store ps' = true /\
        wf_rows_store ds' = true /\
        keys_subset (rows_keys ds') (rows_keys ps') = true /\
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

(** * Row operations *)

(* Directional lookup using key_subsumption. *)
Fixpoint row_first_match (rows:Rows) (kq:KeyTy) : option TypeExpr :=
  match rows with
  | [] => None
  | (ks,t)::rs => if key_subsumption ks kq then Some t else row_first_match rs kq
  end.

Fixpoint row_lookup_all (rows:Rows) (kq:KeyTy) : list TypeExpr :=
  match rows with
  | [] => []
  | (ks,t)::rs =>
      if key_subsumption ks kq then t :: row_lookup_all rs kq
      else row_lookup_all rs kq
  end.

Definition row_has_key (rows:Rows) (kq:KeyTy) : bool :=
  match row_first_match rows kq with Some _ => true | None => false end.

Fixpoint row_domain (rows:Rows) : list KeyTy :=
  match rows with [] => [] | (k,_)::rs => k :: row_domain rs end.

(* Exact-key replacement (conservative). *)
Fixpoint row_remove (rows:Rows) (k:KeyTy) : Rows :=
  match rows with
  | [] => []
  | (k',t)::rs => if key_eqb k k' then row_remove rs k else (k',t)::row_remove rs k
  end.

Definition row_add (rows:Rows) (k:KeyTy) (t:TypeExpr) : Rows :=
  (k,t) :: row_remove rows k.

Definition row_update (rows:Rows) (k:KeyTy) (t:TypeExpr) : Rows :=
  row_add rows k t.

Definition empty_row : Rows := [].

(* Conversions *)
Definition rows_to_types (rows:Rows) : list TypeExpr := map snd rows.

Definition types_to_rows (ts:list TypeExpr) : Rows :=
  combine (map KPos (seq 0 (length ts))) ts.

Definition make_row (n:nat) (name:option string) (t:TypeExpr) : Row :=
  match name with
  | Some s => (KBoth n s, t)
  | None   => (KPos n,    t)
  end.

(** * Well-formedness (boolean) *)

Definition wf_fun (ps ds:Rows) : bool :=
  andb (wf_rows_store ps)
  (andb (wf_rows_store ds)
        (keys_subset (rows_keys ds) (rows_keys ps))).

Definition wf_overload (fs:list TypeExpr) : bool :=
  let fix all_funs (xs:list TypeExpr) : bool :=
      match xs with
      | [] => true
      | TE_Fun _ _ _ _ _ _ :: xs' => all_funs xs'
      | _ :: _ => false
      end in all_funs fs.

Fixpoint wf_type (t:TypeExpr) : bool :=
  let fix wf_rows (rs:Rows) : bool :=
      andb (wf_rows_store rs)
           (let fix go rs :=
                match rs with
                | [] => true
                | (_,ty)::rs' => andb (wf_type ty) (go rs')
                end in go rs) in
  match t with
  | TE_Bot | TE_Top | TE_Any | TE_TVar _ _ | TE_Ref _ => true
  | TE_Literal _ => true
  | TE_Union ts =>
      let fix go xs := match xs with [] => true | x::xs' => andb (wf_type x) (go xs') end
      in go ts
  | TE_Fun ps ds r _ _ _ =>
      andb (wf_fun ps ds)
           (andb (wf_rows ps)
                 (andb (wf_rows ds) (wf_type r)))
  | TE_Overload fs =>
      andb (wf_overload fs)
           (let fix go xs := match xs with [] => true | x::xs' => andb (wf_type x) (go xs') end
            in go fs)
  | TE_Class _ ms bs _ _ =>
      andb (wf_rows ms)
           (let fix go xs := match xs with [] => true | x::xs' => andb (wf_type x) (go xs') end
            in go bs)
  | TE_Module _ ms => wf_rows ms
  | TE_Instance g as' =>
      andb (wf_type g)
           (let fix go xs := match xs with [] => true | x::xs' => andb (wf_type x) (go xs') end
            in go as')
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

End TypeCore.
