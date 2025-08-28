(*
  TYPE_LATTICE.v
  Subtyping and Lattice Operations
*)
From Coq Require Import String List Bool Arith PeanoNat Lia Program.Wf.
Import ListNotations.

Require Import TYPE_CORE.
Import TypeCore.

Module TypeLattice.

  (* ===== Subtyping with proper termination ===== *)
  
  Section Subsumption.
    
    (* Helper lemmas from the Coq file *)
    Lemma size_ge_1 t : 1 <= size t.
    Proof. 
      destruct (uncast t); simpl; try lia.
      unfold size. simpl. lia.
    Qed.

    Lemma row_lookup_size_bound :
      forall (rows : Rows) (k : FieldKey) (tv : TypeExpr),
        row_lookup rows k = Some tv -> 1 + size tv <= rows_size rows.
    Proof.
      induction rows as [|[k' v] rows IH]; intros k tv H.
      - discriminate H.
      - simpl in H.
        destruct (key_matches k k'); simpl.
        + inversion H; subst tv. simpl. lia.
        + apply IH in H. simpl. lia.
    Qed.
    
    Lemma rows_size_tail_le k tv rows :
      rows_size rows <= rows_size ((k,tv)::rows).
    Proof. simpl; lia. Qed.

    (* Main subtyping function with proof-carrying style *)
    Program Fixpoint type_is_subtype (a b : TypeExpr)
      {measure (size a + size b)} : bool :=
      match uncast a, uncast b with
      | _, TE_Top => true
      | TE_Bot, _ => true
      | TE_Any, _ => true
      | _, TE_Any => true
      
      (* Row subtyping: a ≤ b if a has all fields of b *)
      | TE_Row rows_a, TE_Row rows_b =>
          let fix check_fields (rb : Rows)
                               (Hle : rows_size rb <= rows_size rows_b) : bool :=
            match rb as rb' return (rb = rb' -> bool) with
            | [] => fun _ => true
            | (k, tv_b) :: rb' => fun Heq =>
                match row_lookup rows_a k with
                | Some tv_a => 
                    andb (type_is_subtype tv_a tv_b)
                         (check_fields rb' _)
                | None => false
                end
            end eq_refl
          in check_fields rows_b (le_refl _)
      
      (* Function subtyping: contravariant params, covariant return *)
      | TE_Fun params_a ret_a eff_a prop_a _, TE_Fun params_b ret_b eff_b prop_b _ =>
          if andb (Bool.eqb prop_a prop_b) (effect_eqb eff_a eff_b) then
            andb (type_is_subtype (cast (TE_Row params_b)) (cast (TE_Row params_a)))
                 (type_is_subtype ret_a ret_b)
          else false
      
      (* Overloaded left: all candidates ≤ b *)
      | TE_Overload cs, _ =>
          let fix check_all (xs : list TypeExpr)
                           (Hle : list_size xs <= list_size cs) : bool :=
            match xs as xs' return (xs = xs' -> bool) with
            | [] => fun _ => true
            | x::xs' => fun Heq =>
                andb (type_is_subtype x b)
                     (check_all xs' _)
            end eq_refl
          in check_all cs (le_refl _)
      
      (* Overloaded right: a ≤ some candidate *)
      | _, TE_Overload cs =>
          let fix check_any (xs : list TypeExpr)
                           (Hle : list_size xs <= list_size cs) : bool :=
            match xs as xs' return (xs = xs' -> bool) with
            | [] => fun _ => false
            | x::xs' => fun Heq =>
                orb (type_is_subtype a x)
                    (check_any xs' _)
            end eq_refl
          in check_any cs (le_refl _)
          
      (* Protocol satisfaction *)
      | TE_Class _ _ _ true _, _ => satisfies_protocol b a
      | _, TE_Class _ _ _ true _ => satisfies_protocol a b
      
      | _, _ => type_eqb a b
      end
      
    with satisfies_protocol (t proto : TypeExpr) : bool :=
      match uncast proto with
      | TE_Class _ proto_rows _ true _ =>
          let t_rows := get_rows t in
          forallb (fun '(pk, pt) =>
            match row_lookup t_rows pk with
            | Some tt => type_is_subtype tt pt
            | None => false
            end
          ) proto_rows
      | _ => false
      end
      
    with get_rows (t : TypeExpr) : Rows :=
      match uncast t with
      | TE_Row rows => rows
      | TE_Class _ rows _ _ _ => rows
      | TE_Module _ rows => rows
      | _ => []
      end.

    (* Proof obligations *)
    Next Obligation.
      symmetry in Heq. 
      apply row_lookup_size_bound in Heq.
      simpl in Hle. simpl. lia.
    Qed.

    Next Obligation.
      simpl in Hle. lia.
    Qed.

    Next Obligation. simpl; lia. Qed.
    Next Obligation. simpl; lia. Qed.
    Next Obligation. simpl in Hle; lia. Qed.
    Next Obligation. simpl in Hle; lia. Qed.
    
    Solve All Obligations with (simpl; lia).
    
  End Subsumption.

  (* ===== Join operations ===== *)
  
  Section Join.
    
    (* Helper for meet *)
    Definition meet_by_subsumption (x y : TypeExpr) : option TypeExpr :=
      if type_is_subtype x y then Some x
      else if type_is_subtype y x then Some y
      else None.

    (* Simple union without normalization *)
    Definition union2 (a b : TypeExpr) : TypeExpr :=
      match uncast a, uncast b with
      | TE_Overload xs, _ => cast (TE_Overload (b :: xs))
      | _, TE_Overload ys => cast (TE_Overload (a :: ys))
      | _, _ => cast (TE_Overload [a; b])
      end.

    (* Main join function with proper termination *)
    Program Fixpoint type_join (a b : TypeExpr)
      {measure (size a + size b)} : TypeExpr :=
      if type_is_subtype a b then b else
      if type_is_subtype b a then a else
      match uncast a, uncast b with
      | TE_Bot, _ => b
      | _, TE_Bot => a
      | TE_Top, _ | _, TE_Top => type_top
      
      (* Row join: keep only common fields *)
      | TE_Row rows_a, TE_Row rows_b =>
          let fix build (rb : Rows) (pf : rows_size rb <= rows_size rows_b) : Rows :=
            match rb with
            | [] => []
            | (k, tbk) :: rb' => 
                match row_lookup rows_a k with
                | Some tak => 
                    let jk := type_join tak tbk in
                    (k, jk) :: build rb' (le_trans _ _ _ (rows_size_tail_le k tbk rb') pf)
                | None => 
                    build rb' (le_trans _ _ _ (rows_size_tail_le k tbk rb') pf)
                end
            end
          in cast (TE_Row (build rows_b (le_refl _)))
      
      (* Function join *)
      | TE_Fun pa ra effa ipa _, TE_Fun pb rb effb ipb _ =>
          if andb (Nat.eqb (length pa) (length pb)) (Bool.eqb ipa ipb) then
            let fix meet_params (xs ys : list TypeExpr) : option (list TypeExpr) :=
              match xs, ys with
              | [], [] => Some []
              | x::xs', y::ys' =>
                  match meet_by_subsumption x y, meet_params xs' ys' with
                  | Some m, Some ms => Some (m::ms)
                  | _, _ => None
                  end
              | _, _ => None
              end in
            match meet_params (rows_to_types pa) (rows_to_types pb) with
            | Some ps => 
                cast (TE_Fun (types_to_rows ps) (type_join ra rb) effa ipa [])
            | None => union2 a b
            end
          else union2 a b
      
      | _, _ => union2 a b
      end
      
    with rows_to_types (rows : Rows) : list TypeExpr :=
      map snd rows
      
    with types_to_rows (ts : list TypeExpr) : Rows :=
      combine (map FK_Pos (seq 0 (length ts))) ts.

    (* Proof obligations *)
    Next Obligation.
      symmetry in Heq_anonymous.
      apply row_lookup_size_bound in Heq_anonymous.
      simpl in *. lia.
    Qed.
    
    Next Obligation. simpl; lia. Qed.
    
    Solve All Obligations with (simpl; lia).
    
  End Join.

  (* Export main operations *)
  Definition type_is_subtype := type_is_subtype.
  Definition type_join := type_join.
  Definition type_meet (a b : TypeExpr) : TypeExpr :=
    if type_is_subtype a b then a
    else if type_is_subtype b a then b  
    else type_bot.

End TypeLattice.
