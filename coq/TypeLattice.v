(*
  TYPE_LATTICE.v
  Subtyping and Lattice Operations for ParamRows/ClosedRows
  - No mutual Program Fixpoints
  - No forward references (row merges are parameterized)
*)

From Stdlib Require Import String List Bool Arith PeanoNat Lia Program.Wf.
From Stdlib Require Import Permutation.
Require Import Program.Tactics.
Import ListNotations.

From Spyte Require Import TypeCore.
Import TypeCore.

Set Implicit Arguments.

Module TypeLattice.

Obligation Tactic := try (simpl; lia).

(* ---------- Sizes & helpers ---------- *)


Lemma size_pos : forall t, 0 < size t.
  destruct t; simpl; lia.
Qed.

Lemma rows_lookup_decreases : forall rows k t,
  row_first_match rows k = Some t -> size t < 1 + rows_size rows.
Proof.
  induction rows as [| [k' t'] rs IH]; intros k t H.
  - (* rows = [] *) simpl in H. discriminate H.
  - simpl in H. destruct (key_subsumption k' k) eqn:Heq.
    + inversion H; subst. simpl. lia.
    + apply IH in H. simpl. lia.
Qed.

Lemma list_size_tail : forall t ts,
  list_size ts < list_size (t :: ts).
Proof.
  intros. simpl. pose (size_pos t). lia.
Qed.

Fixpoint list_eqb_nat (xs ys : list nat) : bool :=
  match xs, ys with
  | [], [] => true
  | n::xs', m::ys' => andb (Nat.eqb n m) (list_eqb_nat xs' ys')
  | _, _ => false
  end.

Definition effect_compatible (e1 e2 : SideEffect) : bool :=
  andb (Bool.eqb (se_new e1) (se_new e2))
    (andb (Bool.eqb (se_bound_method e1) (se_bound_method e2))
      (andb (match se_update e1, se_update e2 with
             | None, None => true
             | Some x, Some y => type_eqb x y
             | _, _ => false
             end)
            (andb (list_eqb_nat (se_update_indices e1) (se_update_indices e2))
                  (Bool.eqb (se_points_to_args e1) (se_points_to_args e2))))).

Definition get_class_members (t : TypeExpr) : ClosedRows :=
  match t with
  | TE_Class _ members _ _ _ => members
  | _ => []
  end.

Fixpoint filter_map {A B} (f : A -> option B) (xs : list A) : list B :=
  match xs with
  | [] => []
  | x :: xs' =>
      match f x with
      | Some y => y :: filter_map f xs'
      | None => filter_map f xs'
      end
  end.

(* ---------- Row merges (parameterized to avoid forward refs) ---------- *)

Section RowMerges.
  Variable OP : TypeExpr -> TypeExpr -> TypeExpr.

  Definition rows_merge_with (r1 r2 : ClosedRows) : ClosedRows :=
    rows_canon (filter_map (fun '(k, t1) =>
      match row_first_match r2 k with
      | Some t2 => Some (k, normalize_type (OP t1 t2))
      | None => None
      end) r1).

  (* For “join/union of rows”: keep all fields, combine commons with OP *)
  Definition rows_union_with (r1 r2 : ClosedRows) : ClosedRows :=
    let common := filter_map (fun '(k, t1) =>
      match row_first_match r2 k with
      | Some t2 => Some (k, normalize_type (OP t1 t2))
      | None => Some (k, t1)
      end) r1 in
    let only_r2 := filter (fun '(k, _) => negb (row_has_key r1 k)) r2 in
    rows_canon (common ++ only_r2).
End RowMerges.

(* We’ll instantiate with meet/join after they are defined. *)

(* ---------- Pure structural helpers (no WF) ---------- *)

Fixpoint forallb_sub (sub:TypeExpr->TypeExpr->bool) (as' : list TypeExpr) (b : TypeExpr) : bool :=
  match as' with
  | [] => true
  | a::as'' => andb (sub a b) (forallb_sub sub as'' b)
  end.

(* Overload rule: ∀ g∈gs. ∃ f∈fs. sub f g *)
Fixpoint overload_forall_exists
        (sub:TypeExpr->TypeExpr->bool)
        (fs gs:list TypeExpr) : bool :=
  match gs with
  | [] => true
  | g::gs' =>
      andb (existsb (fun f => sub f g) fs)
           (overload_forall_exists sub fs gs')
  end.

Fixpoint rows_sub_with
        (sub:TypeExpr->TypeExpr->bool)
        (rsub rsup : ClosedRows) : bool :=
  match rsup with
  | [] => true
  | (k,treq)::rsup' =>
      match row_first_match rsub k with
      | Some tprov => andb (sub tprov treq) (rows_sub_with sub rsub rsup')
      | None => false
      end
  end.

Fixpoint lists_sub_with
        (sub:TypeExpr->TypeExpr->bool)
        (ts1 ts2 : list TypeExpr) : bool :=
  match ts1, ts2 with
  | [], [] => true
  | t1::xs1, t2::xs2 => andb (sub t1 t2) (lists_sub_with sub xs1 xs2)
  | _, _ => false
  end.

Fixpoint params_accept_reqs
        (sub:TypeExpr->TypeExpr->bool)
        (pa:ParamRows) (reqs:ClosedRows) : bool :=
  match reqs with
  | [] => true
  | (k,treq)::rs =>
      match param_lookup pa k with
      | Some tacc => andb (sub treq tacc) (params_accept_reqs sub pa rs)
      | None => false
      end
  end.

Fixpoint flat_map {A B} (f:A->list B) (xs:list A) : list B :=
  match xs with
  | [] => []
  | x::xs' => f x ++ flat_map f xs'
  end.

Fixpoint zip_with (f:TypeExpr->TypeExpr->TypeExpr) (xs ys:list TypeExpr) : list TypeExpr :=
  match xs, ys with
  | [], [] => []
  | x::xs', y::ys' => f x y :: zip_with f xs' ys'
  | _, _ => []
  end.
  
(* --------- Size helpers (lists/rows) --------- *)


Lemma list_size_cons_ge x xs : size x <= list_size (x::xs).
Proof. simpl; lia. Qed.

Lemma list_size_app (xs ys : list TypeExpr) :
  list_size (xs ++ ys) = list_size xs + list_size ys.
Proof. induction xs; simpl; lia. Qed.

Lemma list_size_app_ge_r xs ys : list_size ys <= list_size (xs ++ ys).
Proof. rewrite list_size_app; lia. Qed.

(* --------- ParamRows lookup bound --------- *)

Definition opt_size (o:option TypeExpr) : nat :=
    match o with None => 0 | Some t => size t end.
    
Lemma param_lookup_bound :
  forall (ps:ParamRows) k t,
    param_lookup ps k = Some t ->
    size t <= rows_size (pr_fixed ps) + opt_size (pr_star ps) + opt_size (pr_kwstar ps).
Proof.
  intros ps k t H.
  unfold param_lookup in H.
  destruct (row_first_match (pr_fixed ps) k) eqn:RF.
  - inversion H; subst. simpl. apply rows_lookup_decreases in RF. lia.
  - destruct k as [i|s|i s].
    all: destruct (pr_star ps) eqn:S; destruct (pr_kwstar ps) eqn:K;
         inversion H; subst; simpl; lia.
Qed.

Lemma rows_lookup_decrease : forall (rs: ClosedRows) k t,
  row_first_match rs k = Some t ->
  size t <= rows_size rs.
Proof.
  induction rs as [|[k' u] rs IH]; simpl; intros k t H.
  - inversion H.
  - destruct (key_subsumption k' k) in H. 
    + inversion H. subst. lia.
    + apply IH in H. lia.
Qed.
(* The local fixpoint that occurs when [size] is cbn’d in the TE_Fun case
   is pointwise ≥ rows_size (it adds a +1 per entry). *)
Lemma rows_size_le_localfix :
  forall rs,
    rows_size rs <=
    (fix rows_sz (rows : ClosedRows) : nat :=
       match rows with
       | [] => 0
       | (_, t') :: rs' => 1 + size t' + rows_sz rs'
       end) rs.
Proof.
  induction rs as [|[k t] rs IH].
  - constructor.
  - cbn [rows_size]. lia.
Qed.

(* A clean lower bound for the function type’s size that’s easy to reuse. *)
Lemma fun_size_ge_fixed :
  forall pa da ra effa ipa tva,
    1 + rows_size (pr_fixed pa) <= size (TE_Fun pa da ra effa ipa tva).
Proof.
  intros. cbn [size].
  (* Abstract other summands too, just to keep the goal readable. *)
  set (t1 := match pr_star   pa with Some t => size t | None => 0 end).
  set (t2 := match pr_kwstar pa with Some t => size t | None => 0 end).
  set (t4 := size ra).
  set (t5 := effect_size effa).
  set (t6 := length tva).
  set (F := fix rows_sz (rows : ClosedRows) : nat :=
               match rows with
               | [] => 0
               | (_, t') :: rs' => 1 + size t' + rows_sz rs'
               end).
  (* Step 1: 1 + rows_size (pr_fixed pa) ≤ 1 + F (pr_fixed pa). *)
  specialize (rows_size_le_localfix (pr_fixed pa)) as Hfix.
  simpl. apply le_n_S. 
  (* Step 2: monotonicity by adding non-negative extras on the RHS. *)
  eapply Nat.le_trans; [exact Hfix|].  
  change ((fix rows_sz (rows : ClosedRows) : nat := match rows with
          | [] => 0
          | (_, t') :: rs' =>
              1 + size t' + rows_sz rs'
          end) (pr_fixed pa))
  with (F (pr_fixed pa)). lia.
Qed.

(* Now your original component→whole lemma becomes trivial. *)
Lemma fixed_lookup_lt_fun_size :
  forall pa da ra effa ipa tva k t,
    row_first_match (pr_fixed pa) k = Some t ->
    size t < size (TE_Fun pa da ra effa ipa tva).
Proof.
  intros pa da ra effa ipa tva k t Hm.
  (* you said you already have this shape; if it’s ≤, the next line fixes it *)
  (* rows_lookup_decreases : size t <= rows_size (pr_fixed pa) *)
  apply rows_lookup_decreases in Hm.
  eapply Nat.lt_le_trans.
  - exact Hm.
  - apply fun_size_ge_fixed.                            (* 1 + rows_size … ≤ size (TE_Fun …) *)
Qed.

Lemma star_lt_fun_size :
  forall pa da ra effa ipa tva t,
    pr_star pa = Some t ->
    size t < size (TE_Fun pa da ra effa ipa tva).
Proof.
  intros pa da ra effa ipa tva t H.
  cbn [size]. rewrite H. destruct (pr_kwstar pa); lia.
Qed.

Lemma kwstar_lt_fun_size :
  forall pa da ra effa ipa tva t,
    pr_kwstar pa = Some t ->
    size t < size (TE_Fun pa da ra effa ipa tva).
Proof.
  intros pa da ra effa ipa tva t H.
  cbn [size]. rewrite H. destruct (pr_star pa); lia.
Qed.


(* Any member’s size is ≤ the sum of sizes. *)
Lemma in_rows_le_rows_size :
  forall rs k t, In (k,t) rs -> size t <= rows_size rs.
Proof.
  induction rs as [|[k' t'] rs IH]; simpl; intros k t Hin.
  - inversion Hin.
  - inversion Hin.
    + inversion H.
      subst; simpl; lia.
    + apply IH in H. lia.
Qed.

(* If row_first_match finds Some t, then that (k',t) appears in the list. *)
Lemma row_first_match_in :
  forall rs k t, row_first_match rs k = Some t -> exists k', In (k',t) rs.
Proof.
  induction rs as [|[ks u] rs IH]; simpl; intros k t H; try discriminate.
  destruct (key_subsumption ks k) eqn:E; inversion H; subst.
  + exists ks. left. reflexivity.
  + apply IH in H. inversion H. exists x. right. assumption.
Qed.

(* Put the three together for param_lookup. *)
Lemma param_lookup_lt_fun_size :
  forall pa da ra effa ipa tva k t,
    param_lookup pa k = Some t ->
    size t < size (TE_Fun pa da ra effa ipa tva).
Proof.
  intros pa da ra effa ipa tva k t H.
  unfold param_lookup in H.
  destruct (row_first_match (pr_fixed pa) k) as [tf|] eqn:Hfix; [inversion H; subst; eauto using fixed_lookup_lt_fun_size|].
  destruct k as [i|s|i s]; cbn in H; inversion H; subst; eauto using star_lt_fun_size, kwstar_lt_fun_size.
Qed.


Lemma class_size_gt_rows_size :
  forall n ms bases tvs,
    rows_size ms < size (TE_Class n ms bases true tvs).
Proof.
  intros. cbn [size].
  specialize (rows_size_le_localfix ms) as Hle.
  lia.
Qed.

(* If you prefer a lookup lemma with strict bound: *)
Lemma row_first_match_lt_rows_size :
  forall ms k t, row_first_match ms k = Some t -> size t < 1 + rows_size ms.
Proof.
  induction ms as [| [k' u] rs IH]; intros k t H; simpl in *.
  - discriminate H.
  - destruct (key_subsumption k' k) eqn:E.
    + inversion H; subst. simpl. lia.
    + apply IH in H. simpl. lia.
Qed.

Lemma lookup_lt_class_size :
  forall n ms bases tvs k t,
    row_first_match ms k = Some t ->
    size t < size (TE_Class n ms bases true tvs).
Proof.
  intros n ms bases tvs k t H.
  cbn [size].
  specialize (row_first_match_lt_rows_size _ _ H) as Hlt.
  specialize (rows_size_le_localfix ms) as Hle.
  lia.
Qed.

(* sum-of-sizes along concatenation *)
Lemma rows_size_app :
  forall xs ys, rows_size (xs ++ ys) = rows_size xs + rows_size ys.
Proof.
  induction xs as [|[k t] xs IH]; cbn; intro ys; [reflexivity|].
  rewrite IH. rewrite Nat.add_assoc. reflexivity.
Qed.

(* the head's size is bounded by the row’s size *)
Lemma head_size_le_rows_size :
  forall k t rs, size t <= rows_size ((k,t)::rs).
Proof. intros; cbn; lia. Qed.

(* function size dominates its fixed-rows size (pb version) *)
Lemma fun_size_ge_rows_size_fixed :
  forall pb db rb effb ipb tvb,
    rows_size (pr_fixed pb) <= size (TE_Fun pb db rb effb ipb tvb).
Proof. intros. cbn [size]. pose (rows_size_le_localfix (pr_fixed pb)). lia. Qed.


Lemma size_in_list_size :
  forall t ts, In t ts -> size t <= list_size ts.
Proof.
  induction ts as [|u us IH]; simpl; intros H.
  - contradiction.
  - destruct H as [<-|H].
    + lia.
    + specialize (IH H). lia.
Qed.

Program Fixpoint subtype (a b : TypeExpr)
  {measure (size a + size b)} : bool :=

  if type_eqb a b then true else

  match a, b with
  (* extremes / gradual-any *)
  | _, TE_Top => true
  | TE_Bot, _ => true
  | TE_Any, _ => true
  | _, TE_Any => true

  (* atomics *)
  | TE_Literal l1, TE_Literal l2 => literal_eqb l1 l2
  | TE_TVar x1 v1, TE_TVar x2 v2 => andb (Nat.eqb x1 x2) (Bool.eqb v1 v2)
  | TE_Ref s1, TE_Ref s2 => String.eqb s1 s2

  (* a ≤ (∨ bs) ⇔ a ≤ some b∈bs  — consume bs head/tail explicitly *)
  | _, TE_Union bs =>
      match bs with
      | [] => false
      | y :: ys' =>
          orb (subtype a y)
              (subtype a (TE_Union ys'))
      end

  (* (∨ as) ≤ b ⇔ ∀ a∈as, a ≤ b — consume as head/tail explicitly *)
  | TE_Union as', _ =>
      match as' with
      | [] => true
      | x :: xs' =>
          andb (subtype x b)
               (subtype (TE_Union xs') b)
      end

  (* overloads *)
  (* ∧fs ≤ ∧(g::gs')  ⇔  (∧fs ≤ g) ∧ (∧fs ≤ ∧gs') *)
  | TE_Overload fs, TE_Overload gs =>
      match gs with
      | [] => true
      | g :: gs' =>
          andb (subtype (TE_Overload fs) g)
               (subtype (TE_Overload fs) (TE_Overload gs'))
      end

  (* ∧(f::fs') ≤ t  ⇔  (f ≤ t) ∨ (∧fs' ≤ t) *)
  | TE_Overload fs, _ =>
      match fs with
      | [] => false
      | f :: fs' =>
          orb (subtype f b)
              (subtype (TE_Overload fs') b)
      end

  (* t ≤ ∧(g::gs')  ⇔  (t ≤ g) ∧ (t ≤ ∧gs') *)
  | _, TE_Overload gs =>
      match gs with
      | [] => true
      | g :: gs' =>
          andb (subtype a g)
               (subtype a (TE_Overload gs'))
      end

  (* functions: ip equal; effects equal; params contravariant; return covariant *)
  | TE_Fun pa da ra effa ipa tva, TE_Fun pb db rb effb ipb tvb =>
      andb (Bool.eqb ipa ipb)
      (andb (effect_compatible effa effb)
        (andb
          (* params: pb ≤ pa (width+depth+tails). We scan required fixed keys of pb. *)
          (let P := pr_fixed pb in
           let fix params_ok (pref req : ClosedRows)
                             (Heq : P = pref ++ req) {struct req} : bool :=
             match req with
             | [] =>
                 let ok_star :=
                   match pr_star pb, pr_star pa with
                   | None, _ => true
                   | Some tsup, Some tsub => subtype tsup tsub
                   | Some _, None => false
                   end in
                 let ok_kw :=
                   match pr_kwstar pb, pr_kwstar pa with
                   | None, _ => true
                   | Some vsup, Some vsub => subtype vsup vsub
                   | Some _, None => false
                   end in
                 andb ok_star ok_kw
             | (k,treq) :: req' =>
                 match param_lookup pa k with
                 | None => false
                 | Some tprov =>
                     andb (subtype treq tprov)
                          (* recurse on the tail; keep the invariant P = pref' ++ req' *)
                          (params_ok (pref ++ [(k,treq)]) req'
                             (* Heq : P = pref ++ (k,treq)::req'
                                Convert (k,treq)::req' to [(k,treq)] ++ req', then reassociate. *)
                             (eq_trans Heq
                               (eq_sym (app_assoc pref [(k,treq)] req'))))
                 end
             end in
           params_ok [] P eq_refl)
          (* return: ra ≤ rb *)
          (subtype ra rb)))

  (* classes: nominal for non-protocols *)
  | TE_Class n1 _ _ false _, TE_Class n2 _ _ false _ =>
      String.eqb n1 n2

  (* protocols: structural rows (width+depth) *)
  | TE_Class nA msA bA true tvA, TE_Class nB msB bB true tvB =>
    let P := msB in
    let fix rows_ok (pref req : ClosedRows)
                    (Heq : P = pref ++ req) {struct req} : bool :=
      match req with
      | [] => true
      | (k,treq) :: req' =>
          match row_first_match msA k with
          | None => false
          | Some tprov =>
              andb (subtype tprov treq)
                   (rows_ok (pref ++ [(k,treq)]) req'
                     (* Heq : P = pref ++ (k,treq)::req' *)
                     (eq_trans Heq (eq_sym (app_assoc pref [(k,treq)] req'))))
          end
      end in
    rows_ok [] P eq_refl
    
  (* class implements protocol *)
  | TE_Class nA msA bA false tvA, TE_Class nB msB bB true tvB =>
      let P := msB in
      let fix rows_ok (pref req : ClosedRows)
                      (Heq : P = pref ++ req) {struct req} : bool :=
        match req with
        | [] => true
        | (k,treq) :: req' =>
            match row_first_match msA k with
            | Some tprov =>
                andb (subtype tprov treq)
                     (rows_ok (pref ++ [(k,treq)]) req'
                        (* Heq : P = pref ++ (k,treq)::req' *)
                        (eq_trans Heq
                          (eq_sym (app_assoc pref [(k,treq)] req'))))
            | None => false
            end
        end in
      rows_ok [] P eq_refl


  (* modules: nominal *)
  | TE_Module n1 _, TE_Module n2 _ => String.eqb n1 n2

  (* instances: generator + args pointwise (assume covariance of args) *)
  | TE_Instance g1 as1, TE_Instance g2 as2 =>
      andb (subtype g1 g2)
           (let P1 := as1 in
            let P2 := as2 in
            let fix args_ok (pref1 xs pref2 ys : list TypeExpr)
                            (Heq1 : P1 = pref1 ++ xs)
                            (Heq2 : P2 = pref2 ++ ys)
                            {struct xs} : bool :=
                match xs, ys with
                | [], [] => true
                | u::us, v::vs =>
                    andb (subtype u v)
                         (args_ok (pref1 ++ [u]) us (pref2 ++ [v]) vs
                                  (eq_trans Heq1 (eq_sym (app_assoc pref1 [u] us)))
                                  (eq_trans Heq2 (eq_sym (app_assoc pref2 [v] vs))))
                | _, _ => false
                end
            in args_ok [] as1 [] as2 eq_refl eq_refl)


  (* default: no relation *)
  | _, _ => false
  end.


Next Obligation.
  intros; subst.
  cbn [size]. lia.
Qed.

Next Obligation.
  intros; subst. clear a0 subtype.
  rewrite <- Nat.add_lt_mono_l. cbn [size]. fold list_size. 
  simpl. assert (size y > 0) by apply size_pos. lia.
Qed.

Next Obligation.
  intros; subst. clear a0 subtype.
  rewrite <- Nat.add_lt_mono_r. cbn [size]. fold list_size. 
  simpl. assert (size x > 0) by apply size_pos. lia.
Qed.

Next Obligation.
  intros; subst. clear a0 subtype.
  rewrite <- Nat.add_lt_mono_r. cbn [size]. fold list_size. 
  assert (size x > 0) by apply size_pos.
  lia.
Qed.

Next Obligation.
  intros; subst. clear subtype.
  rewrite <- Nat.add_lt_mono_l. cbn [size]. fold list_size. 
  assert (size g > 0) by apply size_pos.
  lia.
Qed.

Next Obligation.
  intros; subst. clear subtype.
  rewrite <- Nat.add_lt_mono_l. cbn [size]. fold list_size. 
  assert (size g > 0) by apply size_pos.
  lia.
Qed.

Next Obligation.
  intros; subst. clear subtype a0.
  rewrite <- Nat.add_lt_mono_r. cbn [size]. fold list_size. 
  assert (size f > 0) by apply size_pos.
  lia.
Qed.

Next Obligation.
  intros; subst. clear subtype a0.
  rewrite <- Nat.add_lt_mono_r. cbn [size]. fold list_size. 
  assert (size f > 0) by apply size_pos.
  lia.
Qed.
Next Obligation.
  intros; subst. clear subtype a0.
  rewrite <- Nat.add_lt_mono_l. cbn [size]. fold list_size. 
  assert (size g > 0) by apply size_pos.
  lia.
Qed.

Next Obligation.
  intros; subst. clear subtype a0.
  rewrite <- Nat.add_lt_mono_l. cbn [size]. fold list_size. 
  assert (size g > 0) by apply size_pos.
  lia.
Qed.


Next Obligation.
  intros; subst. clear subtype.
  remember (filtered_var) as o_sup eqn:Ho_sup.
  remember (filtered_var0) as o_sub eqn:Ho_sub.
  inversion Heq_anonymous; subst; clear Heq_anonymous.
  inversion Heq_anonymous0; subst; clear Heq_anonymous0.
  unfold filtered_var in H.
  unfold filtered_var0 in H1.
  clear filtered_var filtered_var0.
  symmetry in H, H1.
  apply star_lt_fun_size with (da:=da) (ra:=ra) (effa:=effa) (ipa:=ipa) (tva:=tva) in H1.
  apply star_lt_fun_size with (da:=db) (ra:=rb) (effa:=effb) (ipa:=ipb) (tva:=tvb) in H.
  rewrite <- Nat.add_comm.
  apply Nat.add_lt_mono; assumption.
Qed.

Next Obligation.
  intros; subst. clear ok_star subtype.
  remember (filtered_var) as o_sup eqn:Ho_sup.
  remember (filtered_var0) as o_sub eqn:Ho_sub.
  inversion Heq_anonymous; subst; clear Heq_anonymous.
  inversion Heq_anonymous0; subst; clear Heq_anonymous0.
  (* Now use Ho_sup/Ho_sub with the chosen bridge lemma *)

  (* Bridge filtered → raw star. If filtered_varpr_star is just pr_star,
     this is immediate after [unfold]. If it’s a wrapper, add a tiny lemma: *)
  unfold filtered_var in H.
  unfold filtered_var0 in H1.
  clear filtered_var filtered_var0.
  symmetry in H, H1.
  apply kwstar_lt_fun_size with (da:=da) (ra:=ra) (effa:=effa) (ipa:=ipa) (tva:=tva) in H1.
  apply kwstar_lt_fun_size with (da:=db) (ra:=rb) (effa:=effb) (ipa:=ipb) (tva:=tvb) in H.
  rewrite <- Nat.add_comm.
  apply Nat.add_lt_mono; assumption.
Qed.


Next Obligation.
  intros; subst. clear subtype.
  remember (filtered_var) as o_sup eqn:Ho_sup.
  inversion Heq_anonymous; subst; clear Heq_anonymous.
  unfold filtered_var in H.
  clear filtered_var.
  symmetry in H.
  pose proof (param_lookup_lt_fun_size pa da ra effa ipa tva k H) as Hprov.
  enough (size treq <= size (TE_Fun pb db rb effb ipb tvb)) by lia.
  clear Hprov pa da ra effa ipa tva H. 
  subst P.
  assert (Hhead : size treq <= rows_size ((k,treq)::req')).
  { apply head_size_le_rows_size. }
  assert (Htail : rows_size ((k,treq)::req') <= rows_size (pr_fixed pb)).
  { rewrite Heq, rows_size_app. simpl. lia. }
  assert (Hfun : rows_size (pr_fixed pb) <= size (TE_Fun pb db rb effb ipb tvb)).
  { apply fun_size_ge_rows_size_fixed. }
  eapply  Nat.le_trans; [ eapply  Nat.le_trans; [ exact Hhead | exact Htail ] | exact Hfun ].
Qed.

Next Obligation.
  intros. subst.
  rewrite <- app_assoc.
  reflexivity.
Qed.

Next Obligation.
  intros. subst.
  rewrite <- app_assoc.
  reflexivity.
Qed.
 
Next Obligation.
  intros. subst. clear subtype.
  assert (size ra < size (TE_Fun pa da ra effa ipa tva)) by (cbn [size]; lia).
  assert (size rb < size (TE_Fun pb db rb effb ipb tvb)) by (cbn [size]; lia).
  lia.
Qed.

Next Obligation.
  intros. subst. clear subtype.
  remember (filtered_var) as o_sup eqn:Ho_sup.
  inversion Heq_anonymous; subst; clear Heq_anonymous.
  unfold filtered_var in H.
  clear filtered_var.
  symmetry in H.
  subst P.

  enough ((size treq) < size (TE_Class nB msB bB true tvB)).
  enough ((size tprov) < size (TE_Class nA msA bA true tvA)).
  lia.
  + exact (lookup_lt_class_size  nA msA bA tvA k  H).
  +
    (* 1. the head is bounded by its suffix *)
    assert (Hhead : size treq <= rows_size ((k,treq)::req'))
      by apply head_size_le_rows_size.

    (* 2. suffix is bounded by the whole msB via Heq *)
    assert (Htail : rows_size ((k,treq)::req') <= rows_size msB).
    { rewrite Heq, rows_size_app. simpl. lia. }

    (* 3. msB’s rows_size is strictly below the class size *)
    assert (Hclass : rows_size msB < size (TE_Class nB msB bB true tvB))
      by apply class_size_gt_rows_size.

    (* 4. chain them *)
    eapply Nat.le_lt_trans; [ eapply Nat.le_trans; [ exact Hhead | exact Htail ] | exact Hclass ].
Qed.


Next Obligation.
  intros. subst.
  rewrite <- app_assoc.
  reflexivity.
Qed.

Next Obligation.
  intros. subst.
  rewrite <- app_assoc.
  reflexivity.
Qed.


Next Obligation.
  intros. subst. clear subtype.
  remember (filtered_var) as o_sup eqn:Ho_sup.
  inversion Heq_anonymous; subst; clear Heq_anonymous.
  unfold filtered_var in H.
  clear filtered_var.
  symmetry in H.
  subst P.

  enough ((size treq) < size (TE_Class nB msB bB true tvB)).
  enough ((size tprov) < size (TE_Class nA msA bA false tvA)).
  lia.
  + exact (lookup_lt_class_size  nA msA bA tvA k  H).
  +
    (* 1. the head is bounded by its suffix *)
    assert (Hhead : size treq <= rows_size ((k,treq)::req'))
      by apply head_size_le_rows_size.

    (* 2. suffix is bounded by the whole msB via Heq *)
    assert (Htail : rows_size ((k,treq)::req') <= rows_size msB).
    { rewrite Heq, rows_size_app. simpl. lia. }

    (* 3. msB’s rows_size is strictly below the class size *)
    assert (Hclass : rows_size msB < size (TE_Class nB msB bB true tvB))
      by apply class_size_gt_rows_size.

    (* 4. chain them *)
    eapply Nat.le_lt_trans; [ eapply Nat.le_trans; [ exact Hhead | exact Htail ] | exact Hclass ].
Qed.

Next Obligation.
  intros. subst.
  rewrite <- app_assoc.
  reflexivity.
Qed.

Next Obligation.
  intros. subst.
  rewrite <- app_assoc.
  reflexivity.
Qed.

Next Obligation.
  intros; subst. cbn [size]. lia.
Qed.


Next Obligation.
  intros; subst; clear subtype args_ok.
  cbn [size].
  (* make the list-size fixpoints readable to lia *)
  fold list_size.
  inversion Heq1  ; subst; clear Heq1.
  inversion Heq2 ; subst; clear Heq2.

  subst P1 P2.
  (* bound heads by whole lists using the prefix/suffix equalities *)
  assert (Hu : size u <= list_size as1) by (subst; rewrite list_size_app; simpl; lia).
  assert (Hv : size v <= list_size as2) by (subst; rewrite list_size_app; simpl; lia).

  (* step 1: LHS ≤ list_size as1 + list_size as2 *)
  eapply Nat.le_lt_trans.
  { apply Nat.add_le_mono. apply Hu. apply Hv. }

  pose proof (size_pos g1) as Hg1.
  pose proof (size_pos g2) as Hg2.
  (* step 2: strictly less than RHS thanks to the two outer S's *)
  assert (Heq :
      1 + size g1 + list_size as1 + (1 + size g2 + list_size as2)
      = (list_size as1 + list_size as2) + (1 + size g1 + (1 + size g2))) by lia.
  rewrite Heq.
  lia.
Qed.

Next Obligation.
  intros; subst; rewrite <- app_assoc; reflexivity.
Qed.

Next Obligation.
  intros; subst; rewrite <- app_assoc; reflexivity.
Qed.

Next Obligation.
  intros; subst; rewrite <- app_assoc; reflexivity.
Qed.

Next Obligation.
  intros; subst; rewrite <- app_assoc; reflexivity.
Qed.

Next Obligation.
  intros.
  subst.
  clear program_branch_0 program_branch_1 program_branch_2 subtype args_ok.
  subst wildcard' wildcard'0 P1 P2 as1 as2.
  unfold not.
  split; intros; destruct H; congruence.
Qed.

Next Obligation.
  intros.
  subst.
  clear program_branch_0 program_branch_1 program_branch_2 subtype args_ok.
  subst wildcard' wildcard'0 P1 P2 as1 as2.
  unfold not.
  split; intros; destruct H; congruence.
Qed.
(* 

Definition satisfies_protocol (t proto:TypeExpr) : bool :=
    match proto with
    | TE_Class _ proto_members _ true _ =>
        let t_members := match t with
                         | TE_Class _ ms _ _ _ => ms
                         | TE_Module _ ms => ms
                         | _ => [] end in
        forallb (fun pr => let '(pk,pt) := pr in
                 match row_first_match t_members pk with
                 | Some tt => TypeLattice.subtype tt pt
                 | None => false
                 end) proto_members
    | _ => false
    end. *)
