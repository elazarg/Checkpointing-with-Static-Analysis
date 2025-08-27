
(*
  TYPE.v
  Implementation of TypeSystemSig
*)
From Coq Require Import String List Bool Arith PeanoNat Lia Program.Wf.
Import ListNotations.

Set Implicit Arguments.
Set Primitive Projections.

Module TypeSystem.

  (* Local Helpers *)
  Definition str_eqb := String.eqb.

  Fixpoint slen (s:string) : nat :=
    match s with
    | EmptyString => 0
    | String _ tl => S (slen tl)
    end.
    
  Record SideEffect (TE : Type) := {
    se_new            : bool;
    se_bound_method   : bool;
    se_update         : option TE;
    se_update_indices : list nat;
    se_points_to_args : bool
  }.
  
  (* Type expressions *)
  Inductive TypeExpr : Type :=
  | TE_Bot
  | TE_Top
  | TE_Imm (h : nat)
  | TE_TVar (x : nat)
  | TE_Row (open : bool) (fs : list (string * TypeExpr)) (tail : option nat)
  | TE_Fun (params : list TypeExpr) (ret : TypeExpr)
           (eff : SideEffect TypeExpr) (is_prop : bool) (is_bound : bool)
  | TE_Overloaded (cands : list TypeExpr)
  | TE_Unknown.

  (* Row utilities *)
  Fixpoint row_lookup (fs:list (string * TypeExpr)) (k:string) : option TypeExpr :=
    match fs with
    | [] => None
    | (k',v)::fs' => if str_eqb k k' then Some v else row_lookup fs' k
    end.

  Fixpoint keys (fs:list (string * TypeExpr)) : list string :=
    match fs with | [] => [] | (k,_)::fs' => k :: keys fs' end.

  Fixpoint mem_key (k:string) (ks:list string) : bool :=
    match ks with
    | [] => false
    | k'::ks' => if str_eqb k k' then true else mem_key k ks'
    end.

  Fixpoint dedup (ks:list string) : list string :=
    match ks with
    | [] => []
    | k::ks' => if mem_key k ks' then dedup ks' else k :: dedup ks'
    end.

  Fixpoint inter_keys (xs ys:list string) : list string :=
    match xs with
    | [] => []
    | x::xs' => if mem_key x ys then x :: inter_keys xs' ys else inter_keys xs' ys
    end.

  Fixpoint subset_keys (xs ys:list string) : bool :=
    match xs with
    | [] => true
    | x::xs' => andb (mem_key x ys) (subset_keys xs' ys)
    end.

  (* Type operations *)
  Axiom get_type_hash: TypeExpr -> nat.

  Definition type_is_immutable (t:TypeExpr) : bool :=
    match t with
    | TE_Imm _ => true
    | TE_Fun _ _ _ _ _ => true
    | _ => false
    end.

  Fixpoint type_eqb (a b:TypeExpr) : bool :=
    match a, b with
    | TE_Bot, TE_Bot => true
    | TE_Top, TE_Top => true
    | TE_Imm h1, TE_Imm h2 => Nat.eqb h1 h2
    | TE_TVar x, TE_TVar y => Nat.eqb x y
    | TE_Unknown, TE_Unknown => true
    | TE_Row o1 f1 t1, TE_Row o2 f2 t2 =>
        andb (Bool.eqb o1 o2)
             (andb (match t1, t2 with
                    | None, None => true
                    | Some x, Some y => Nat.eqb x y
                    | _, _ => false
                    end)
                   (let fix eqfs (x y:list (string * TypeExpr)) : bool :=
                      match x, y with
                      | [], [] => true
                      | (kx,vx)::xs, (ky,vy)::ys =>
                          andb (String.eqb kx ky) (andb (type_eqb vx vy) (eqfs xs ys))
                      | _, _ => false
                      end in eqfs f1 f2))
    | TE_Fun p1 r1 _ ip1 ib1, TE_Fun p2 r2 _ ip2 ib2 =>
        let fix eqps (x y:list TypeExpr) : bool :=
            match x, y with
            | [], [] => true
            | px::xs, py::ys => andb (type_eqb px py) (eqps xs ys)
            | _, _ => false
            end in
        andb (eqps p1 p2)
             (andb (type_eqb r1 r2)
                   (andb (Bool.eqb ip1 ip2) (Bool.eqb ib1 ib2)))
    | TE_Overloaded xs, TE_Overloaded ys =>
        let fix eqs (x y:list TypeExpr) : bool :=
            match x, y with
            | [], [] => true
            | a::xs', b::ys' => andb (type_eqb a b) (eqs xs' ys')
            | _, _ => false
            end in eqs xs ys
    | _, _ => false
    end.

  Definition type_bot : TypeExpr := TE_Bot.
  Definition type_top : TypeExpr := TE_Top.

  Section Subsumption.

  (* ---- Size measures ---- *)
  Fixpoint size (t : TypeExpr) : nat :=
    match t with
    | TE_Bot | TE_Top | TE_Imm _ | TE_TVar _ | TE_Unknown => 1
    | TE_Row _ fs _ =>
        1 + fold_right (fun p acc => 1 + size (snd p) + acc) 0 fs
    | TE_Fun ps r _ _ _ =>
        1 + fold_right (fun u acc => 1 + size u + acc) 0 ps + size r
    | TE_Overloaded cs =>
        1 + fold_right (fun u acc => 1 + size u + acc) 0 cs
    end.

  Definition sum_sizes (xs : list TypeExpr) : nat :=
    fold_right (fun u acc => 1 + size u + acc) 0 xs.

  Definition fields_sum (fs : list (string * TypeExpr)) : nat :=
    fold_right (fun p acc => 1 + size (snd p) + acc) 0 fs.

  (* ---- Helper lemmas ---- *)
  Lemma sum_sizes_cons x xs :
    sum_sizes (x::xs) = 1 + size x + sum_sizes xs.
  Proof. reflexivity. Qed.

  Lemma fields_sum_cons k tv fs :
    fields_sum ((k,tv)::fs) = 1 + size tv + fields_sum fs.  
  Proof. reflexivity. Qed.

  Lemma size_ge_1 t : 1 <= size t.
  Proof. destruct t; simpl; lia. Qed.

  Lemma row_lookup_size_le_fields_sum :
    forall (fa : list (string * TypeExpr)) (k : string) (tv : TypeExpr),
      row_lookup fa k = Some tv -> 1 + size tv <= fields_sum fa.
  Proof.
     induction fa as [|[k' v] fa IH]; intros k tv H.
    - discriminate H.
    - simpl in H. 
      destruct (str_eqb k k'); simpl.
      + inversion H; subst tv.
        lia.
      + 
        apply IH in H.
        simpl in H.
        lia.
  Qed.
  
  
  (* ---- Main subtyping function with simpler inlining ---- *)
  Program Fixpoint type_is_subtype (a b : TypeExpr)
    {measure (size a + size b)} : bool :=
    match a, b with
    | _, TE_Top => true
    | TE_Bot, _ => true
    
    (* Rows: need proof-carrying for fb subset bound *)
    | TE_Row oa fa ta, TE_Row ob fb tb =>
        if subset_keys (keys fb) (keys fa)
        then
          (* We need to track that fb0 is a suffix of fb for size bounds *)
          let fix check_fields (fb0 : list (string * TypeExpr)) 
                               (Hle : fields_sum fb0 <= fields_sum fb) : bool :=
            match fb0 as fb0' return (fb0 = fb0' -> bool) with
            | [] => fun _ => true
            | (k, tv_b) :: fb' => fun Heq =>
                match row_lookup fa k with
                | Some tv_a => 
                    andb (type_is_subtype tv_a tv_b) 
                         (check_fields fb' _)
                | None => false
                end
            end eq_refl
          in check_fields fb (Nat.le_refl _)
        else false
    
    (* Functions: need proof-carrying for parameter bounds *)
    | TE_Fun pa ra _ _ _, TE_Fun pb rb _ _ _ =>
        let fix check_params (xs ys : list TypeExpr) 
                            (Hx : sum_sizes xs <= sum_sizes pa)
                            (Hy : sum_sizes ys <= sum_sizes pb) : bool :=
          match xs as xs', ys as ys' return (xs = xs' -> ys = ys' -> bool) with
          | [], [] => fun _ _ => true
          | xa::xs', yb::ys' => fun Heqx Heqy =>
              andb (type_is_subtype yb xa)
                   (check_params xs' ys' _ _)
          | _, _ => fun _ _ => false
          end eq_refl eq_refl
        in andb (check_params pa pb (Nat.le_refl _) (Nat.le_refl _))
                (type_is_subtype ra rb)
    
    (* Overloaded left: all candidates ≤ b *)
    | TE_Overloaded cs, _ =>
        let fix check_all (xs : list TypeExpr)
                         (Hle : sum_sizes xs <= sum_sizes cs) : bool :=
          match xs as xs' return (xs = xs' -> bool) with
          | [] => fun _ => true
          | x::xs' => fun Heq =>
              andb (type_is_subtype x b)
                   (check_all xs' _)
          end eq_refl
        in check_all cs (Nat.le_refl _)
    
    (* Overloaded right: a ≤ any candidate *)
    | _, TE_Overloaded cs =>
        let fix check_any (xs : list TypeExpr)
                         (Hle : sum_sizes xs <= sum_sizes cs) : bool :=
          match xs as xs' return (xs = xs' -> bool) with
          | [] => fun _ => false
          | x::xs' => fun Heq =>
              orb (type_is_subtype a x)
                  (check_any xs' _)
          end eq_refl
        in check_any cs (Nat.le_refl _)
    
    | _, _ => type_eqb a b
    end.



  (* ---- Streamlined proof obligations with explicit tactics ---- *)
  
  (* Obligation 1: Row field tv_a ≤ tv_b *)
  Next Obligation.
    symmetry in Heq_anonymous.
    apply row_lookup_size_le_fields_sum in Heq_anonymous.
    cbn [size].
    simpl in Hle.
    fold (fields_sum fa) (fields_sum fb).
    lia.
  Qed.

  (* Obligation 2: Function params yb ≤ xa *)
  Next Obligation.
    symmetry in Heq_anonymous.
    apply row_lookup_size_le_fields_sum in Heq_anonymous.
    simpl in Hle.
    lia.
  Qed.

  Next Obligation.
    cbn [size].
    simpl in Hx, Hy.
    fold (sum_sizes pa) (sum_sizes pb).
    lia.
  Qed.

  (* Obligation 4: Function params recursive call *)
  Next Obligation.
    simpl in Hx.
    lia.
  Qed.

  (* Obligation 5: Function params recursive call *)
  Next Obligation.
    simpl in Hy.
    lia.
  Qed.

  (* Obligation 6: Function result ra ≤ rb *)
  Next Obligation.
    cbn [size].
    fold (sum_sizes pa) (sum_sizes pb).
    lia.
  Qed.

  (* Obligation 7: Overloaded left x ≤ b *)
  Next Obligation.
    cbn [size].
    simpl in Hle.
    fold (sum_sizes cs).
    lia.
  Qed.

  (* Obligation 8: Overloaded left recursive call *)
  Next Obligation.
    simpl in Hle.
    lia.
  Qed.

  (* Obligation 9: Overloaded right a ≤ x *)
  Next Obligation.
    cbn [size].
    simpl in Hle.
    fold (sum_sizes cs). lia.
  Qed.

  (* Obligation 10: Overloaded right recursive call *)
  Next Obligation.
    simpl in Hle.
    lia.
  Qed.
    
    
  Solve All Obligations with (now unfold not; repeat split; intros; destruct H; congruence).

  Opaque type_is_subtype_func.

  End Subsumption.
  
  Lemma fields_sum_tail_le k tv fb' :
  fields_sum fb' <= fields_sum ((k,tv)::fb').
Proof. rewrite fields_sum_cons; lia. Qed.

(* meet (GLB) for parameters, by subsumption only *)
Definition meet_by_subsumption (x y : TypeExpr) : option TypeExpr :=
  if type_is_subtype x y then Some x
  else if type_is_subtype y x then Some y
  else None.

(* Append a union without normalization; no recursion into join *)
Definition union2 (a b : TypeExpr) : TypeExpr :=
  match a, b with
  | TE_Overloaded xs, _ => TE_Overloaded (b :: xs)
  | _, TE_Overloaded ys => TE_Overloaded (a :: ys)
  | _, _ => TE_Overloaded [a; b]
  end.

(* ---------- The join (fuel-free, well-founded on size a + size b) ---------- *)

Program Fixpoint type_join (a b : TypeExpr)
  {measure (size a + size b)} : TypeExpr :=
  if type_is_subtype a b then b else
  if type_is_subtype b a then a else
  match a, b with
  | TE_Row oa fa ta, TE_Row ob fb tb =>
      let fix build (fb0 : list (string * TypeExpr)) (pf : fields_sum fb0 <= fields_sum fb) {struct fb0} : list (string * TypeExpr) := 
        match fb0 with
        | [] => []
        | (k, tbk) :: fb' => match row_lookup fa k with
                            | Some tak => let jk := type_join tak tbk in
                                      (k, jk) :: build fb' (Nat.le_trans _ _ _ (fields_sum_tail_le k tbk fb') pf) 
                            | None => (* key not shared: drop it in the LUB (width = intersection) *)
                                      build fb' (Nat.le_trans _ _ _ (fields_sum_tail_le k tbk fb') pf)
                            end
        end
      in
      TE_Row (andb oa ob) (build fb (Nat.le_refl _)) None

  | TE_Fun pa ra effa ipa iba, TE_Fun pb rb effb ipb ibb =>
      if Nat.eqb (length pa) (length pb) then
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
        match meet_params pa pb with
        | Some ps => TE_Fun ps (type_join ra rb) effa ipa iba
        | None    => union2 a b
        end
      else union2 a b

  | TE_Imm h1, TE_Imm h2 => if Nat.eqb h1 h2 then a else union2 a b
  | TE_TVar x, TE_TVar y => if Nat.eqb x y then a else union2 a b
  | _, _ => union2 a b
  end.


  (* ---------- Obligations: strictly decreasing measure ---------- *)

  (* Row field join: type_join tak tbk *)
  Next Obligation.
    symmetry in Heq_anonymous.
    apply row_lookup_size_le_fields_sum in Heq_anonymous.
    cbn [size].
    fold (fields_sum fa) (fields_sum fb).
    simpl in *.
    lia.
  Qed.
  Next Obligation.
  now unfold not; repeat split; intros; destruct H; congruence.
  Qed.
  
  Next Obligation. now unfold not; repeat split; intros; destruct H; congruence. Qed.
  Next Obligation. cbn[size]. fold (sum_sizes pa) (sum_sizes pb). lia. Qed.
  
  Solve All Obligations with (now unfold not; repeat split; intros; destruct H; congruence).
  
  Opaque type_join.
  

  (* Classifiers *)
  Definition is_overloaded (t:TypeExpr) : bool :=
    match t with TE_Overloaded _ => true | _ => false end.

  Definition is_property (t:TypeExpr) : bool :=
    match t with TE_Fun _ _ _ ip _ => ip | _ => false end.

  Definition is_bound_method (t:TypeExpr) : bool :=
    match t with TE_Fun _ _ _ _ ib => ib | _ => false end.

  Definition any_new (t:TypeExpr) : bool :=
    match t with TE_Unknown => true | _ => false end.

  Definition all_new (_:TypeExpr) : bool := false.

  Definition type_is_callable (t:TypeExpr) : bool :=
    match t with TE_Fun _ _ _ _ _ | TE_Overloaded _ => true | _ => false end.

  Fixpoint get_return (t:TypeExpr) : TypeExpr :=
    match t with
    | TE_Fun _ r _ _ _ => r
    | TE_Overloaded cs =>
        let fix fold (xs:list TypeExpr) (acc:TypeExpr) :=
          match xs with
          | [] => acc
          | f::xs' => fold xs' (type_join acc (get_return f))
          end in fold cs TE_Bot
    | _ => type_top
    end.

  Definition effect_join (x y:SideEffect TypeExpr) : SideEffect TypeExpr :=
    {| se_new := orb x.(se_new) y.(se_new);
       se_bound_method := orb x.(se_bound_method) y.(se_bound_method);
       se_update := match x.(se_update), y.(se_update) with
                    | Some tx, Some ty => Some (type_join tx ty)
                    | Some tx, None => Some tx
                    | None, Some ty => Some ty
                    | None, None => None
                    end;
       se_update_indices := x.(se_update_indices) ++ y.(se_update_indices);
       se_points_to_args := orb x.(se_points_to_args) y.(se_points_to_args) |}.

  Definition empty_effect : SideEffect TypeExpr :=
    {| se_new := false; se_bound_method := false; se_update := None;
       se_update_indices := []; se_points_to_args := false |}.

  Fixpoint get_side_effect (t:TypeExpr) : SideEffect TypeExpr :=
    match t with
    | TE_Fun _ _ e _ _ => e
    | TE_Overloaded cs =>
        let fix fold (xs:list TypeExpr) (acc:SideEffect TypeExpr) :=
          match xs with
          | [] => acc
          | f::xs' => fold xs' (effect_join acc (get_side_effect f))
          end in fold cs empty_effect
    | _ => empty_effect
    end.

  Definition ctor_effect_new : SideEffect TypeExpr :=
    {| se_new := true; se_bound_method := false; se_update := None;
       se_update_indices := []; se_points_to_args := false |}.

  Definition ctor_effect_pts : SideEffect TypeExpr :=
    {| se_new := true; se_bound_method := false; se_update := None;
       se_update_indices := []; se_points_to_args := true |}.

  Definition make_list_constructor  : TypeExpr := TE_Fun [] type_top ctor_effect_pts false false.
  Definition make_tuple_constructor : TypeExpr := TE_Fun [] type_top ctor_effect_pts false false.
  Definition make_dict_constructor  : TypeExpr := TE_Fun [] type_top ctor_effect_new false false.
  Definition make_set_constructor   : TypeExpr := TE_Fun [] type_top ctor_effect_new false false.
  Definition make_slice_constructor : TypeExpr := TE_Fun [] type_top ctor_effect_new false false.

  (* Subscription *)
  Fixpoint subscr (base:TypeExpr) (attr:string) : TypeExpr :=
    match base with
    | TE_Row _ fs _ =>
        match row_lookup fs attr with
        | Some t => t
        | None => type_top
        end
    | TE_Fun _ _ _ _ _ => type_top
    | TE_Overloaded cs =>
        let fix fold (xs:list TypeExpr) (acc:TypeExpr) :=
          match xs with
          | [] => acc
          | f::xs' => fold xs' (type_join acc (subscr f attr))
          end in fold cs TE_Bot
    | _ => type_top
    end.

  Definition subscr_index (_base:TypeExpr) (_i:nat) : TypeExpr := type_top.
  Definition get_unop (_:TypeExpr) (_:string) : TypeExpr := type_top.
  Definition partial_binop (_ _ :TypeExpr) (_:string) : TypeExpr := type_top.

  (* Simplified partial - no real unification *)
  Definition partial (f:TypeExpr) (args:list TypeExpr) : TypeExpr :=
    match f with
    | TE_Fun ps r e ip ib =>
        TE_Fun [] r e ip ib
    | TE_Overloaded cs =>
        let fix fold_all (xs:list TypeExpr) (acc:TypeExpr * SideEffect TypeExpr)
          : (TypeExpr * SideEffect TypeExpr) :=
          let '(t, se) := acc in 
          match xs with
          | [] => acc
          | g::xs' => fold_all xs' (type_join t (get_return g),
                                    effect_join se (get_side_effect g))
          end in
        let '(rj, ej) := fold_all cs (TE_Bot, empty_effect) in
        TE_Fun [] rj ej false false
    | _ => type_top
    end.

  (* Dunder API *)
  Inductive DunderInfo :=
  | TDUnOp  (op:UnOpTag)  (arg:TypeExpr)
  | TDBinOp (op:BinOpTag) (lhs rhs:TypeExpr) (mode:Inplace)
  | TDCmpOp (op:CmpOpTag) (lhs rhs:TypeExpr).

  Definition dunder_lookup (_:DunderInfo) : TypeExpr :=
    TE_Fun [] type_top empty_effect false false.

End TypeSystem.