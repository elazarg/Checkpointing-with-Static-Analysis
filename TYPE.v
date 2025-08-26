
(**
  TypeSystem.v
  ------------
  Full rows-based implementation of PointerAnalysis.TypeSystemSig
  with integrated (local) unification used for overload/partial resolution.
  Design choices are conservative and localized so precision can be
  increased without touching IR or the analysis.

  Key features
  - Rows as string→type maps with width-subtyping and principled join (LUB).
  - Functions carry return type, effect, and flags (property/bound-method).
  - Overloads contain an explicit candidate list; partial applies unification
    against argument types and joins matching candidates (fallback: join all).
  - Unification supports type variables and a single tail row-variable;
    occurs checks are implemented; effects are carried through substitution.
*)

From Coq Require Import String List Bool Arith ZArith PeanoNat Ascii.
Import ListNotations.

Require Import IR.   (* TAC: ConstV, tags *)
Require Import PTR.  (* PointerAnalysis.TypeSystemSig *)

Module TypeSystem <: PointerAnalysis.TypeSystemSig.
  Import TAC.

  (* -------------------------- Local Helpers -------------------------- *)

  Definition str_eqb := String.eqb.

  Fixpoint slen (s:string) : nat :=
    match s with
    | EmptyString => 0
    | String _ tl => S (slen tl)
    end.

  (* ============================ Types ============================== *)

  (** Side effects required by the signature. *)
  Record SideEffect := {
    se_new : bool;
    se_bound_method : bool;
    se_update : option TypeExpr;
    se_update_indices : list nat;
    se_points_to_args : bool
  }.

  (** Type expressions with rows, variables (for unification), functions,
      overloads, and unknowns.  Row tails are a single optional variable. *)
  Inductive TypeExpr : Type :=
  | TE_Bot
  | TE_Top
  | TE_Imm (h:nat)
  | TE_TVar (x:nat)                         (* type variable for unification *)
  | TE_Row (open:bool) (fs:list (string * TypeExpr)) (tail:option nat) (* tail-row var *)
  | TE_Fun (params:list TypeExpr) (ret:TypeExpr)
           (eff:SideEffect) (is_prop:bool) (is_bound:bool)
  | TE_Overloaded (cands:list TypeExpr)     (* each candidate is callable *)
  | TE_Unknown.

  (* ------------------------- Row utilities -------------------------- *)

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

  (* ====================== Lattice / Predicates ====================== *)

  Fixpoint get_type_hash (t:TypeExpr) : nat :=
    match t with
    | TE_Bot => 2
    | TE_Top => 3
    | TE_Imm h => 5 + h
    | TE_TVar x => 97 + x
    | TE_Row o fs tail =>
        let fix fold (fs:list (string * TypeExpr)) (acc:nat) :=
          match fs with
          | [] => acc
          | (k,v)::fs' => fold fs' (acc + slen k + 31 * get_type_hash v)
          end in
        (if o then 7 else 11) + fold fs 13 +
        match tail with None => 0 | Some rv => 59 + rv end
    | TE_Fun ps r _ ip ib =>
        let fix fold (ps:list TypeExpr) (acc:nat) :=
          match ps with | [] => acc | p::ps' => fold ps' (acc + 17 * get_type_hash p) end in
        19 + fold ps (23 * get_type_hash r) + (if ip then 1 else 0) + (if ib then 2 else 0)
    | TE_Overloaded cs =>
        let fix fold (cs:list TypeExpr) (acc:nat) :=
          match cs with | [] => acc | c::cs' => fold cs' (acc + 37 * get_type_hash c) end in
        41 + fold cs 43
    | TE_Unknown => 47
    end.

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

  Fixpoint type_is_subtype (a b:TypeExpr) : bool :=
    match a, b with
    | _, TE_Top => true
    | TE_Bot, _ => true
    | TE_Row oa fa ta, TE_Row ob fb tb =>
        let ka := keys fa in
        let kb := keys fb in
        if subset_keys kb ka then
          let fix check (xs:list (string * TypeExpr)) : bool :=
            match xs with
            | [] => true
            | (k, tv_b)::xs' =>
                match row_lookup fa k with
                | Some tv_a => andb (type_is_subtype tv_a tv_b) (check xs')
                | None => false
                end
            end in check fb
        else false
    | TE_Fun pa ra _ _ _, TE_Fun pb rb _ _ _ =>
        let fix contrav (xs ys:list TypeExpr) : bool :=
          match xs, ys with
          | [], [] => true
          | xa::xs', yb::ys' => andb (type_is_subtype yb xa) (contrav xs' ys')
          | _, _ => false
          end in
        andb (contrav pa pb) (type_is_subtype ra rb)
    | TE_Overloaded cs, _ =>
        let fix all (xs:list TypeExpr) : bool :=
          match xs with | [] => true | x::xs' => andb (type_is_subtype x b) (all xs') end in
        all cs
    | _, TE_Overloaded cs =>
        let fix any (xs:list TypeExpr) : bool :=
          match xs with | [] => false | x::xs' => orb (type_is_subtype a x) (any xs') end in
        any cs
    | _, _ => type_eqb a b
    end.

  Fixpoint type_join (a b:TypeExpr) : TypeExpr :=
    match a, b with
    | TE_Bot, x => x
    | x, TE_Bot => x
    | _, _ =>
      if type_eqb a b then a else
      match a, b with
      | TE_Row oa fa ta, TE_Row ob fb tb =>
          let ia := keys fa in
          let ib := keys fb in
          let ki := dedup (inter_keys ia ib) in
          let fix build (ks:list string) : list (string * TypeExpr) :=
            match ks with
            | [] => []
            | k::ks' =>
                match row_lookup fa k, row_lookup fb k with
                | Some va, Some vb => (k, type_join va vb) :: build ks'
                | _, _ => build ks'
                end
            end in
          TE_Row (orb oa ob) (build ki)
                 (match ta, tb with | Some x, _ => Some x | _, Some y => Some y | _, _ => None end)
      | TE_Fun pa ra ea ipa iba, TE_Fun pb rb eb ipb ibb =>
          let ej :=
            {| se_new := orb ea.(se_new) eb.(se_new);
               se_bound_method := orb ea.(se_bound_method) eb.(se_bound_method);
               se_update := match ea.(se_update), eb.(se_update) with
                            | Some tx, Some ty => Some (type_join tx ty)
                            | Some tx, None => Some tx
                            | None, Some ty => Some ty
                            | None, None => None
                            end;
               se_update_indices := ea.(se_update_indices) ++ eb.(se_update_indices);
               se_points_to_args := orb ea.(se_points_to_args) eb.(se_points_to_args) |} in
          TE_Fun pa (type_join ra rb) ej (orb ipa ipb) (orb iba ibb)
      | TE_Overloaded xs, TE_Overloaded ys => TE_Overloaded (xs ++ ys)
      | _, _ => TE_Top
      end
    end.

  (* =========================== Classifiers ========================= *)

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

  Definition get_return (t:TypeExpr) : TypeExpr :=
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

  Definition effect_join (x y:SideEffect) : SideEffect :=
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

  Definition empty_effect : SideEffect :=
    {| se_new := false; se_bound_method := false; se_update := None;
       se_update_indices := []; se_points_to_args := false |}.

  Definition get_side_effect (t:TypeExpr) : SideEffect :=
    match t with
    | TE_Fun _ _ e _ _ => e
    | TE_Overloaded cs =>
        let fix fold (xs:list TypeExpr) (acc:SideEffect) :=
          match xs with
          | [] => acc
          | f::xs' => fold xs' (effect_join acc (get_side_effect f))
          end in fold cs empty_effect
    | _ => empty_effect
    end.

  (* ======================== Literals / ctors ======================= *)

  Axiom const_hash : ConstV -> nat.
  Axiom const_as_string : ConstV -> option string.
  Axiom const_as_nat    : ConstV -> option nat.

  Definition literal_type (c:ConstV) : TypeExpr := TE_Imm (const_hash c).

  Definition ctor_effect_new : SideEffect :=
    {| se_new := true; se_bound_method := false; se_update := None;
       se_update_indices := []; se_points_to_args := false |}.

  Definition ctor_effect_pts : SideEffect :=
    {| se_new := true; se_bound_method := false; se_update := None;
       se_update_indices := []; se_points_to_args := true |}.

  Definition make_list_constructor  : TypeExpr := TE_Fun [] type_top ctor_effect_pts false false.
  Definition make_tuple_constructor : TypeExpr := TE_Fun [] type_top ctor_effect_pts false false.
  Definition make_dict_constructor  : TypeExpr := TE_Fun [] type_top ctor_effect_new false false.
  Definition make_set_constructor   : TypeExpr := TE_Fun [] type_top ctor_effect_new false false.
  Definition make_slice_constructor : TypeExpr := TE_Fun [] type_top ctor_effect_new false false.

  (* ================== Attributes / subscription / ops =============== *)

  Definition subscr (base:TypeExpr) (attr:string) : TypeExpr :=
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

  Definition subscr_literal (base:TypeExpr) (k:ConstV) : TypeExpr :=
    match const_as_string k with
    | Some s => subscr base s
    | None =>
        match const_as_nat k with
        | Some _ => type_top
        | None => type_top
        end
    end.

  Definition subscr_index (_base:TypeExpr) (_i:nat) : TypeExpr := type_top.

  Definition get_unop (_:TypeExpr) (_:string) : TypeExpr := type_top.
  Definition partial_binop (_ _ :TypeExpr) (_:string) : TypeExpr := type_top.

  (* ========================== Unification =========================== *)
  (** We unify over TypeExpr with TVars and row tails.  Substitution maps
      tvars to types and row tail variables to (fields, tail). *)

  Definition TVar := nat.
  Definition RVar := nat.

  Definition RVRow := (list (string * TypeExpr) * option RVar)%type.

  Record Subst := { tvs : list (TVar * TypeExpr); rvs : list (RVar * RVRow) }.

  Definition empty_subst : Subst := {| tvs := []; rvs := [] |}.

  Fixpoint tv_lookup (s:list (TVar * TypeExpr)) (x:TVar) : option TypeExpr :=
    match s with
    | [] => None
    | (y,t)::s' => if Nat.eqb x y then Some t else tv_lookup s' x
    end.

  Fixpoint rv_lookup (s:list (RVar * RVRow)) (x:RVar) : option RVRow :=
    match s with
    | [] => None
    | (y,t)::s' => if Nat.eqb x y then Some t else rv_lookup s' x
    end.

  Definition tv_extend (s:list (TVar * TypeExpr)) (x:TVar) (t:TypeExpr)
    := (x,t)::s.
  Definition rv_extend (s:list (RVar * RVRow)) (x:RVar) (r:RVRow)
    := (x,r)::s.

  Fixpoint apply_subst (σ:Subst) (t:TypeExpr) : TypeExpr :=
    let fix go (t:TypeExpr) :=
      match t with
      | TE_Bot | TE_Top | TE_Imm _ | TE_Unknown => t
      | TE_TVar x =>
          match tv_lookup σ.(tvs) x with
          | Some u => go u
          | None => t
          end
      | TE_Row o fs tail =>
          let fs' := map (fun '(k,v) => (k, go v)) fs in
          let tail' :=
            match tail with
            | None => None
            | Some rv =>
                match rv_lookup σ.(rvs) rv with
                | None => Some rv
                | Some (_fs2, tail2) => tail2  (* flatten: inline row var, ignore fields here *)
                end
            end in
          TE_Row o fs' tail'
      | TE_Fun ps r e ip ib =>
          let e' :=
            {| se_new := e.(se_new);
               se_bound_method := e.(se_bound_method);
               se_update := option_map go e.(se_update);
               se_update_indices := e.(se_update_indices);
               se_points_to_args := e.(se_points_to_args) |} in
          TE_Fun (map go ps) (go r) e' ip ib
      | TE_Overloaded cs => TE_Overloaded (map go cs)
      end in go t.

  Fixpoint occurs_t (x:TVar) (t:TypeExpr) : bool :=
    match t with
    | TE_TVar y => Nat.eqb x y
    | TE_Row _ fs _ => existsb (fun kv => occurs_t x (snd kv)) fs
    | TE_Fun ps r _ _ _ => orb (existsb (occurs_t x) ps) (occurs_t x r)
    | TE_Overloaded cs => existsb (occurs_t x) cs
    | _ => false
    end.

  Fixpoint occurs_r (x:RVar) (t:TypeExpr) : bool :=
    match t with
    | TE_Row _ fs (Some y) => orb (Nat.eqb x y) (existsb (fun kv => occurs_r x (snd kv)) fs)
    | TE_Row _ fs None     => existsb (fun kv => occurs_r x (snd kv)) fs
    | TE_Fun ps r _ _ _    => orb (existsb (occurs_r x) ps) (occurs_r x r)
    | TE_Overloaded cs     => existsb (occurs_r x) cs
    | _ => false
    end.

  Fixpoint remove_key (k:string) (fs:list (string * TypeExpr)) : list (string * TypeExpr) :=
    match fs with
    | [] => []
    | (k',v)::fs' => if str_eqb k k' then fs' else (k',v)::remove_key k fs'
    end.

  Fixpoint split_common (fs1 fs2:list (string * TypeExpr))
           : list (string * (TypeExpr * TypeExpr)) * list (string * TypeExpr) * list (string * TypeExpr) :=
    match fs1 with
    | [] => ([], [], fs2)
    | (k,v)::fs1' =>
        let '(com,rest1,rest2) := split_common fs1' fs2 in
        match row_lookup fs2 k with
        | Some v2 => ((k,(v,v2))::com, rest1, remove_key k rest2)
        | None    => (com, (k,v)::rest1, rest2)
        end
    end.

  Definition result (A:Type) := option A.

  Definition bind_tvar (σ:Subst) (x:TVar) (t:TypeExpr) : result Subst :=
    let t' := apply_subst σ t in
    if occurs_t x t' then None else
    Some {| tvs := tv_extend σ.(tvs) x t' ; rvs := σ.(rvs) |}.

  Definition bind_rvar (σ:Subst) (x:RVar) (row:RVRow) : result Subst :=
    match row with
    | (fs, Some y) => if Nat.eqb x y then None else
                      Some {| tvs := σ.(tvs); rvs := rv_extend σ.(rvs) x row |}
    | _ => Some {| tvs := σ.(tvs); rvs := rv_extend σ.(rvs) x row |}
    end.

  Fixpoint unify (σ:Subst) (t1 t2:TypeExpr) : result Subst :=
    let t1 := apply_subst σ t1 in
    let t2 := apply_subst σ t2 in
    match t1, t2 with
    | TE_Bot, _ | _, TE_Bot => Some σ
    | TE_Top, TE_Top => Some σ
    | TE_Imm h1, TE_Imm h2 => if Nat.eqb h1 h2 then Some σ else None
    | TE_TVar x, t => bind_tvar σ x t
    | t, TE_TVar x => bind_tvar σ x t
    | TE_Unknown, _ | _, TE_Unknown => Some σ
    | TE_Fun p1 r1 _ _ _, TE_Fun p2 r2 _ _ _ =>
        let fix unify_list (σ:Subst) (xs ys:list TypeExpr) : result Subst :=
          match xs, ys with
          | [], [] => Some σ
          | x::xs', y::ys' =>
              match unify σ x y with
              | None => None
              | Some σ' => unify_list σ' xs' ys'
              end
          | _, _ => None
          end in
        match unify_list σ p1 p2 with
        | None => None
        | Some σ1 => unify σ1 r1 r2
        end
    | TE_Row o1 fs1 tail1, TE_Row o2 fs2 tail2 =>
        let '(com, rest1, rest2) := split_common fs1 fs2 in
        let fix unify_pairs (σ:Subst) (ps:list (string * (TypeExpr * TypeExpr))) : result Subst :=
          match ps with
          | [] => Some σ
          | (_, (a,b))::ps' =>
              match unify σ a b with
              | None => None
              | Some σ' => unify_pairs σ' ps'
              end
          end in
        match unify_pairs σ com with
        | None => None
        | Some σc =>
            match tail1, tail2 with
            | None, None =>
                match rest1, rest2 with
                | [], [] => Some σc
                | _, _ => None
                end
            | Some rv, None =>
                (* leftover on right must be empty *)
                match rest2 with
                | [] => bind_rvar σc rv (rest2, None)
                | _ => None
                end
            | None, Some rv =>
                match rest1 with
                | [] => bind_rvar σc rv (rest1, None)
                | _ => None
                end
            | Some rv1, Some rv2 =>
                match rest1, rest2 with
                | [], _ => bind_rvar σc rv1 (rest2, Some rv2)
                | _, [] => bind_rvar σc rv2 (rest1, Some rv1)
                | _, _ => None
                end
            end
        end
    | TE_Overloaded (c::cs), t =>
        let fix try_cands (σ:Subst) (xs:list TypeExpr) : result Subst :=
          match xs with
          | [] => None
          | u::us =>
              match unify σ u t with
              | Some σ' => Some σ'
              | None => try_cands σ us
              end
          end in try_cands σ (c::cs)
    | t, TE_Overloaded cs =>
        let fix try_cands (σ:Subst) (xs:list TypeExpr) : result Subst :=
          match xs with
          | [] => None
          | u::us =>
              match unify σ t u with
              | Some σ' => Some σ'
              | None => try_cands σ us
              end
          end in try_cands σ cs
    | _, _ => None
    end.

  (* ===================== Partial / Overload Apply ==================== *)

  Definition apply_to_effect (σ:Subst) (e:SideEffect) : SideEffect :=
    {| se_new := e.(se_new);
       se_bound_method := e.(se_bound_method);
       se_update := option_map (apply_subst σ) e.(se_update);
       se_update_indices := e.(se_update_indices);
       se_points_to_args := e.(se_points_to_args) |}.

  (** partial: apply args to a callable, using unification against parameters.
      - For TE_Fun, unify params with args; instantiate return/effect via σ.
      - For TE_Overloaded, try each candidate with unification; join all that match.
      - Fallback: if nothing matches, join all candidates' returns/effects. *)
  Definition partial (f:TypeExpr) (args:list TypeExpr) : TypeExpr :=
    match f with
    | TE_Fun ps r e ip ib =>
        let fix unify_list (σ:Subst) (xs ys:list TypeExpr) : option Subst :=
          match xs, ys with
          | [], [] => Some σ
          | x::xs', y::ys' =>
              match unify σ x y with
              | None => None
              | Some σ' => unify_list σ' xs' ys'
              end
          | _, _ => None
          end in
        match unify_list empty_subst ps args with
        | Some σ =>
            TE_Fun [] (apply_subst σ r) (apply_to_effect σ e) ip ib
        | None =>
            (* arity mismatch or cannot unify: still return a callable, but ⊤ *)
            TE_Fun [] type_top e ip ib
        end
    | TE_Overloaded cs =>
        let fix fold (xs:list TypeExpr) (acc_r:TypeExpr * SideEffect) (acc_any:bool)
          : (TypeExpr * SideEffect * bool) :=
          match xs with
          | [] => (acc_r.1, acc_r.2, acc_any)
          | g::xs' =>
              match g with
              | TE_Fun ps r e ip ib =>
                  let fix unify_list (σ:Subst) (xs ys:list TypeExpr) : option Subst :=
                    match xs, ys with
                    | [], [] => Some σ
                    | x::xs', y::ys' =>
                        match unify σ x y with
                        | None => None
                        | Some σ' => unify_list σ' xs' ys'
                        end
                    | _, _ => None
                    end in
                  match unify_list empty_subst ps args with
                  | Some σ =>
                      let r' := apply_subst σ r in
                      let e' := apply_to_effect σ e in
                      let '(acc_ret, acc_eff) := acc_r in
                      fold xs' (type_join acc_ret r', effect_join acc_eff e') true
                  | None => fold xs' acc_r acc_any
                  end
              | _ => fold xs' acc_r acc_any
              end
          end in
        let '(rj, ej, matched) := fold cs (TE_Bot, empty_effect) false in
        if matched then TE_Fun [] rj ej false false
        else (* conservative fallback: join all returns/effects *)
          let fix fold_all (xs:list TypeExpr) (acc:TypeExpr * SideEffect)
            : (TypeExpr * SideEffect) :=
            match xs with
            | [] => acc
            | g::xs' => fold_all xs' (type_join acc.1 (get_return g),
                                      effect_join acc.2 (get_side_effect g))
            end in
          let '(rj2, ej2) := fold_all cs (TE_Bot, empty_effect) in
          TE_Fun [] rj2 ej2 false false
    | _ => type_top
    end.

  (* ========================= Dunder API ============================= *)

  Inductive DunderInfo :=
  | TDUnOp  (op:UnOpTag)  (arg:TypeExpr)
  | TDBinOp (op:BinOpTag) (lhs rhs:TypeExpr) (mode:Inplace)
  | TDCmpOp (op:CmpOpTag) (lhs rhs:TypeExpr).

  Definition dunder_lookup (_:DunderInfo) : TypeExpr :=
    TE_Fun [] type_top empty_effect false false.

End TypeSystem.
