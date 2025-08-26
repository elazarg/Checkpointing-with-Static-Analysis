(*
  Pointer Analysis for TAC IR
*)

From Coq Require Import String List Bool Arith ZArith PeanoNat.
From Coq Require Import FSets FSetWeakList FMaps FMapWeakList.
From Coq Require Import Relations DecidableType.
Import ListNotations.

Set Implicit Arguments.

Import TAC.

Module PointerAnalysis.

  (* ===== Abstract Objects ===== *)
  Module AbstractObject.
    Inductive t :=
    | Location : nat -> nat -> t           (* allocation site: (block, instr) *)
    | Param    : option string -> t        (* parameter with optional name *)
    | ImmType  : nat -> t                  (* immutable by type hash *)
    | ImmConst : ConstV -> t               (* immutable constant value *)
    | Locals   : t                         (* locals scope *)
    | Globals  : t.                        (* globals scope *)
    Definition eq_dec : forall x y : t, {x = y} + {x <> y}.
    Proof.
      decide equality; try apply Nat.eq_dec; try apply String.string_dec.
      - decide equality; apply String.string_dec.
      - destruct c, c0; try (right; discriminate); try (left; reflexivity);
        try (decide equality; [apply Z.eq_dec | apply Bool.bool_dec | apply String.string_dec]).
    Defined.
  End AbstractObject.

  Module Type TypeSystemSig.
    Import AbstractObject.

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

    (* === New: operator resolution with typed operands === *)
    Inductive DunderInfo :=
    | TDUnOp  (op:UnOpTag)  (arg:TypeExpr)
    | TDBinOp (op:BinOpTag) (lhs rhs:TypeExpr) (mode:Inplace)
    | TDCmpOp (op:CmpOpTag) (lhs rhs:TypeExpr).

    Parameter dunder_lookup : DunderInfo -> TypeExpr.
  End TypeSystemSig.

  Module Analysis (TS : TypeSystemSig).
    Import TS AbstractObject.

    (* ===== Core Domains ===== *)
    Module AODec <: DecidableType.
      Definition t := AbstractObject.t.
      Definition eq := @eq t.
      Definition eq_refl := @eq_refl t.
      Definition eq_sym := @eq_sym t.
      Definition eq_trans := @eq_trans t.
      Definition eq_dec := AbstractObject.eq_dec.
    End AODec.

    Module ObjectSet := FSetWeakList.Make(AODec).
    Module AOMap := FMapWeakList.Make(AODec).

    Module FKDec <: DecidableType.
      Definition t := FieldKey.
      Definition eq := @eq t.
      Definition eq_refl := @eq_refl t.
      Definition eq_sym := @eq_sym t.
      Definition eq_trans := @eq_trans t.
      Definition eq_dec : forall x y : t, {x = y} + {x <> y}.
      Proof. decide equality; try apply Nat.eq_dec; try apply String.string_dec. Defined.
    End FKDec.

    Module FieldMap := FMapWeakList.Make(FKDec).

    Definition PointsTo := AOMap.t (FieldMap.t ObjectSet.t).
    Definition TypeMap  := AOMap.t TS.TypeExpr.
    Definition DirtyMap := AOMap.t (FieldMap.t bool).
    Definition StackEnv := StackVar -> ObjectSet.t.
    Definition ProgramPoint := (nat * nat)%type.

    (* ===== Field Key Helpers ===== *)
    Definition wildcard    : FieldKey := FKName "*".
    Definition self_field  : FieldKey := FKName "self".
    Definition func_field  : FieldKey := FKName "__func__".
    Definition args_field  : FieldKey := FKName "args".
    Definition kwargs_field: FieldKey := FKName "kwargs".

    Definition is_star (k:FieldKey) : bool :=
      match k with | FKName s => String.eqb s "*" | _ => false end.

    Definition field_matches (k1 k2 : FieldKey) : bool :=
      if orb (is_star k1) (is_star k2) then true else
      match k1, k2 with
      | FKPos n1,  FKPos n2  => Nat.eqb n1 n2
      | FKName s1, FKName s2 => String.eqb s1 s2
      | FKBoth n1 s1, FKBoth n2 s2 => Nat.eqb n1 n2 && String.eqb s1 s2
      | FKPos n,   FKBoth n' _ | FKBoth n' _, FKPos n   => Nat.eqb n n'
      | FKName s,  FKBoth _ s' | FKBoth _ s', FKName s  => String.eqb s s'
      | _, _ => false
      end.

    (* ===== Empty/Initial Values ===== *)
    Definition empty_points_to : PointsTo := AOMap.empty _.
    Definition empty_type_map  : TypeMap  := AOMap.empty _.
    Definition empty_dirty_map : DirtyMap := AOMap.empty _.
    Definition empty_stack     : StackEnv := fun _ => ObjectSet.empty.

    (* ===== Helpers for immutables ===== *)
    Definition immutable_const (c : ConstV) : ObjectSet.t :=
      ObjectSet.singleton (ImmConst c).
    Definition immutable_type (ty : TypeExpr) : ObjectSet.t :=
      ObjectSet.singleton (ImmType (get_type_hash ty)).

    (* Keep FieldMap sparse *)
    Definition fm_add_nonempty (fm : FieldMap.t ObjectSet.t)
                               (k : FieldKey) (objs : ObjectSet.t)
      : FieldMap.t ObjectSet.t :=
      if ObjectSet.is_empty objs then FieldMap.remove k fm
      else FieldMap.add k objs fm.

    (* ===== Points-to ops ===== *)
    Definition points_to_lookup (P : PointsTo) (o : AbstractObject.t) (f : FieldKey) : ObjectSet.t :=
      match AOMap.find o P with
      | Some fm =>
          FieldMap.fold (fun k objs acc =>
            if orb (field_matches k f) (field_matches f k)
            then ObjectSet.union acc objs
            else acc) fm ObjectSet.empty
      | None => ObjectSet.empty
      end.

    Definition points_to_update (P : PointsTo) (o : AbstractObject.t) (f : FieldKey)
                                (objs : ObjectSet.t) : PointsTo :=
      let fm := match AOMap.find o P with
                | Some fm => fm | None => FieldMap.empty _
                end in
      AOMap.add o (fm_add_nonempty fm f objs) P.

    Definition upd_points_to (P : PointsTo) (targets : ObjectSet.t) (f : FieldKey)
                             (new_objs : ObjectSet.t) : PointsTo :=
      if Nat.eqb (ObjectSet.cardinal targets) 1 then
        match ObjectSet.choose targets with
        | Some tgt => points_to_update P tgt f new_objs
        | None => P
        end
      else
        ObjectSet.fold (fun tgt acc =>
          let old := points_to_lookup acc tgt f in
          points_to_update acc tgt f (ObjectSet.union old new_objs)
        ) targets P.

    Definition index_lookup (P : PointsTo) (objs : ObjectSet.t) (idx : nat) : ObjectSet.t :=
      ObjectSet.fold (fun o acc =>
        let from_pos  := points_to_lookup P o (FKPos idx) in
        let from_wild := points_to_lookup P o wildcard in
        ObjectSet.union acc (ObjectSet.union from_pos from_wild)
      ) objs ObjectSet.empty.

    (* ===== Type ops ===== *)
    Definition type_lookup (T : TypeMap) (o : AbstractObject.t) : TypeExpr :=
      match AOMap.find o T with | Some ty => ty | None => type_bot end.
    Definition type_update (T : TypeMap) (o : AbstractObject.t) (ty : TypeExpr) : TypeMap :=
      AOMap.add o (type_join (type_lookup T o) ty) T.
    Definition type_update_set (T : TypeMap) (objs : ObjectSet.t) (ty : TypeExpr) : TypeMap :=
      ObjectSet.fold (fun o acc => type_update acc o ty) objs T.
    Definition get_types (T : TypeMap) (objs : ObjectSet.t) : TypeExpr :=
      ObjectSet.fold (fun o acc => type_join acc (type_lookup T o)) objs type_bot.

    (* ===== Dirty ===== *)
    Definition mark_dirty (D : DirtyMap) (o : AbstractObject.t) (f : FieldKey) : DirtyMap :=
      let fm := match AOMap.find o D with | Some fm => fm | None => FieldMap.empty _ end in
      AOMap.add o (FieldMap.add f true fm) D.
    Definition mark_dirty_set (D : DirtyMap) (objs : ObjectSet.t) (f : FieldKey) : DirtyMap :=
      ObjectSet.fold (fun o acc => mark_dirty acc o f) objs D.

    (* ===== Stack ===== *)
    Definition stack_lookup (S : StackEnv) (v : StackVar) : ObjectSet.t := S v.
    Definition stack_update (S : StackEnv) (v : StackVar) (objs : ObjectSet.t) : StackEnv :=
      fun v' => if Nat.eqb v v' then objs else S v'.

    (* ===== Unified State ===== *)
    Record State := {
      st_points_to : PointsTo;
      st_types     : TypeMap;
      st_dirty     : DirtyMap;
      st_stack     : StackEnv
    }.

    Definition empty_state : State := {|
      st_points_to := empty_points_to;
      st_types     := empty_type_map;
      st_dirty     := empty_dirty_map;
      st_stack     := empty_stack
    |}.

    Definition with_points (s : State) (P : PointsTo) : State :=
      {| st_points_to := P; st_types := st_types s; st_dirty := st_dirty s; st_stack := st_stack s |}.
    Definition with_types  (s : State) (T : TypeMap)  : State :=
      {| st_points_to := st_points_to s; st_types := T; st_dirty := st_dirty s; st_stack := st_stack s |}.
    Definition with_dirty  (s : State) (D : DirtyMap) : State :=
      {| st_points_to := st_points_to s; st_types := st_types s; st_dirty := D; st_stack := st_stack s |}.
    Definition with_stack  (s : State) (S : StackEnv) : State :=
      {| st_points_to := st_points_to s; st_types := st_types s; st_dirty := st_dirty s; st_stack := S |}.
    Definition with_pts_ty_dirty (s:State) (P:PointsTo) (T:TypeMap) (D:DirtyMap) : State :=
      {| st_points_to := P; st_types := T; st_dirty := D; st_stack := st_stack s |}.

    (* ===== Location & env helpers ===== *)
    Definition alloc_site (pp : ProgramPoint) : AbstractObject.t :=
      let '(b,i) := pp in Location b i.

    Definition get_local  (P : PointsTo) (name : string) : ObjectSet.t :=
      points_to_lookup P Locals (FKName name).
    Definition set_local  (P : PointsTo) (name : string) (objs : ObjectSet.t) : PointsTo :=
      upd_points_to P (ObjectSet.singleton Locals) (FKName name) objs.
    Definition get_global (P : PointsTo) (name : string) : ObjectSet.t :=
      points_to_lookup P Globals (FKName name).

    (* ===== Attribute evaluation (unchanged) ===== *)
    Definition eval_const (c : ConstV) : (ObjectSet.t * TypeExpr) :=
      let ty := literal_type c in (immutable_const c, ty).

    Definition eval_attribute (st : State) (var_objs : ObjectSet.t)
                              (attr : string) (pp : ProgramPoint)
      : (State * ObjectSet.t * TypeExpr) :=
      let var_type    := get_types (st_types st) var_objs in
      let attr_type   := subscr var_type attr in
      let result_type := if is_property attr_type then get_return attr_type else attr_type in
      let res :=
        if type_is_immutable result_type then
          (st, immutable_type result_type)
        else if is_bound_method attr_type then
          let bm := alloc_site pp in
          let func_objs :=
            ObjectSet.fold (fun o acc =>
              ObjectSet.union acc (points_to_lookup (st_points_to st) o (FKName attr)))
              var_objs ObjectSet.empty in
          let P0 := upd_points_to (st_points_to st) (ObjectSet.singleton bm) self_field var_objs in
          let P1 := upd_points_to P0 (ObjectSet.singleton bm) func_field func_objs in
          let T' := type_update (st_types st) bm attr_type in
          (with_pts_ty_dirty st P1 T' (st_dirty st), ObjectSet.singleton bm)
        else if andb (any_new attr_type) (all_new attr_type) then
          let new_obj := alloc_site pp in
          let T' := type_update (st_types st) new_obj result_type in
          (with_types st T', ObjectSet.singleton new_obj)
        else
          let field_objs :=
            ObjectSet.fold (fun o acc =>
              ObjectSet.union acc (points_to_lookup (st_points_to st) o (FKName attr)))
              var_objs ObjectSet.empty in
          if any_new attr_type then
            let new_obj := alloc_site pp in
            let T' := type_update (st_types st) new_obj result_type in
            (with_types st T', ObjectSet.union field_objs (ObjectSet.singleton new_obj))
          else (st, field_objs)
      in
      let '(st', base_objs) := res in
      let result_objs :=
        if type_is_immutable result_type
        then ObjectSet.union base_objs (immutable_type result_type)
        else base_objs in
      (st', result_objs, result_type).

    (* ===== Dunder evaluation (NEW) ===== *)
    Definition eval_dunder (st : State) (e : Dunder) (pp : ProgramPoint)
      : (State * ObjectSet.t * TypeExpr) :=
      let T := st_types st in
      match e with
      | DUnOp op a =>
          let a_objs := st_stack st a in
          let a_ty   := get_types T a_objs in
          let f_ty   := dunder_lookup (TDUnOp op a_ty) in
          if type_is_immutable f_ty
          then (st, immutable_type f_ty, f_ty)
          else let loc := alloc_site pp in
               let st' := with_types st (type_update T loc f_ty) in
               (st', ObjectSet.singleton loc, f_ty)

      | DBinOp op l r mode =>
          let l_objs := st_stack st l in
          let r_objs := st_stack st r in
          let l_ty   := get_types T l_objs in
          let r_ty   := get_types T r_objs in
          let f_ty   := dunder_lookup (TDBinOp op l_ty r_ty mode) in
          if type_is_immutable f_ty
          then (st, immutable_type f_ty, f_ty)
          else let loc := alloc_site pp in
               let st' := with_types st (type_update T loc f_ty) in
               (st', ObjectSet.singleton loc, f_ty)

      | DCmpOp op l r =>
          let l_objs := st_stack st l in
          let r_objs := st_stack st r in
          let l_ty   := get_types T l_objs in
          let r_ty   := get_types T r_objs in
          let f_ty   := dunder_lookup (TDCmpOp op l_ty r_ty) in
          if type_is_immutable f_ty
          then (st, immutable_type f_ty, f_ty)
          else let loc := alloc_site pp in
               let st' := with_types st (type_update T loc f_ty) in
               (st', ObjectSet.singleton loc, f_ty)
      end.

    (* ===== Bound-call helpers & joins (unchanged) ===== *)
    Definition collect_wild_values (P:PointsTo) (containers:ObjectSet.t) : ObjectSet.t :=
      ObjectSet.fold (fun o acc => ObjectSet.union acc (points_to_lookup P o wildcard))
                     containers ObjectSet.empty.
    Definition bound_args_tuples (P:PointsTo) (callee:ObjectSet.t) : ObjectSet.t :=
      ObjectSet.fold (fun f acc => ObjectSet.union acc (points_to_lookup P f args_field))
                     callee ObjectSet.empty.
    Definition bound_kwargs_dicts (P:PointsTo) (callee:ObjectSet.t) : ObjectSet.t :=
      ObjectSet.fold (fun f acc => ObjectSet.union acc (points_to_lookup P f kwargs_field))
                     callee ObjectSet.empty.
    Definition bound_self (P:PointsTo) (callee:ObjectSet.t) : ObjectSet.t :=
      ObjectSet.fold (fun f acc => ObjectSet.union acc (points_to_lookup P f self_field))
                     callee ObjectSet.empty.

    Definition join_fieldmaps (fm1 fm2 : FieldMap.t ObjectSet.t) : FieldMap.t ObjectSet.t :=
      FieldMap.fold (fun k objs acc =>
        let old := match FieldMap.find k acc with | Some o => o | None => ObjectSet.empty end in
        fm_add_nonempty acc k (ObjectSet.union old objs)
      ) fm2 fm1.
    Definition join_points_to (P1 P2 : PointsTo) : PointsTo :=
      AOMap.fold (fun o fm acc =>
        let old := match AOMap.find o acc with | Some fm0 => fm0 | None => FieldMap.empty _ end in
        AOMap.add o (join_fieldmaps old fm) acc
      ) P2 P1.
    Definition join_type_maps (T1 T2 : TypeMap) : TypeMap :=
      AOMap.fold (fun o ty acc =>
        let old := match AOMap.find o acc with | Some ty0 => ty0 | None => type_bot end in
        AOMap.add o (type_join old ty) acc
      ) T2 T1.
    Definition join_dirty_field (b1 b2 : bool) : bool := orb b1 b2.
    Definition join_dirty_maps (D1 D2 : DirtyMap) : DirtyMap :=
      AOMap.fold (fun o fm2 acc =>
        let fm1 := match AOMap.find o acc with | Some fm => fm | None => FieldMap.empty _ end in
        let fm' :=
          FieldMap.fold (fun k b accfm =>
            let old := match FieldMap.find k accfm with | Some bb => bb | None => false end in
            FieldMap.add k (join_dirty_field old b) accfm
          ) fm2 fm1
        in AOMap.add o fm' acc
      ) D2 D1.
    Definition join_stack (S1 S2 : StackEnv) : StackEnv :=
      fun v => ObjectSet.union (S1 v) (S2 v).
    Definition join_state (s1 s2 : State) : State :=
      {| st_points_to := join_points_to (st_points_to s1) (st_points_to s2);
         st_types     := join_type_maps (st_types s1)     (st_types s2);
         st_dirty     := join_dirty_maps (st_dirty s1)    (st_dirty s2);
         st_stack     := join_stack     (st_stack s1)     (st_stack s2) |}.

    (* ===== Calls & transfers (unchanged except ILookup) ===== *)
    Definition eval_call_single (st : State) (callee : AbstractObject.t) (pp : ProgramPoint)
      : (State * ObjectSet.t * TypeExpr) :=
      let P := st_points_to st in
      let T := st_types st in
      let callee_set := ObjectSet.singleton callee in
      let args_tups := bound_args_tuples P callee_set in
      let kwargs_ds := bound_kwargs_dicts P callee_set in
      let self_objs := bound_self P callee_set in
      let pos_vals := collect_wild_values P args_tups in
      let kw_vals  := collect_wild_values P kwargs_ds in
      let arg_types := [ type_join (get_types T pos_vals) (get_types T kw_vals) ] in
      let func_ty   := type_lookup T callee in
      let applied   := partial func_ty arg_types in
      let effect    := get_side_effect applied in
      let ret_ty    := get_return applied in
      let res_objs :=
        if type_is_immutable ret_ty then immutable_type ret_ty
        else if se_new effect then ObjectSet.singleton (alloc_site pp)
        else if se_points_to_args effect then ObjectSet.union pos_vals kw_vals
        else ObjectSet.empty in
      let st' :=
        match se_update effect with
        | Some up_ty =>
            let T' := ObjectSet.fold (fun o acc => type_update acc o up_ty) self_objs T in
            let D' := mark_dirty_set (st_dirty st) self_objs wildcard in
            let P' :=
              match se_update_indices effect with
              | [] => P
              | idxs =>
                  List.fold_left (fun acc idx =>
                     let param_objs := index_lookup P args_tups idx in
                     upd_points_to acc self_objs wildcard param_objs
                  ) idxs P
              end in
            with_pts_ty_dirty st P' T' D'
        | None => st
        end in
      let st'' :=
        if se_new effect then
          let T'' := type_update (st_types st') (alloc_site pp) ret_ty in
          with_types st' T''
        else st' in
      let st''' :=
        if andb (se_new effect) (se_points_to_args effect) then
          let ali := ObjectSet.union pos_vals kw_vals in
          let P'' := upd_points_to (st_points_to st'') (ObjectSet.singleton (alloc_site pp)) wildcard ali in
          with_points st'' P''
        else st'' in
      (st''', res_objs, ret_ty).

    Definition eval_call (st : State) (func_objs : ObjectSet.t) (pp : ProgramPoint)
      : (State * ObjectSet.t * TypeExpr) :=
      ObjectSet.fold
        (fun f acc =>
           let '(acc_st, acc_objs, acc_ty) := acc in
           let '(one_st, one_objs, one_ty) := eval_call_single acc_st f pp in
           (one_st, ObjectSet.union acc_objs one_objs, type_join acc_ty one_ty))
        func_objs
        (st, ObjectSet.empty, type_bot).

    Definition transfer_load_const (st : State) (dst : StackVar) (c : ConstV) : State :=
      let (objs, ty) := eval_const c in
      let T' := type_update_set (st_types st) objs ty in
      let st' := with_types st T' in
      with_stack st' (stack_update (st_stack st) dst objs).

    Definition transfer_load_local (st : State) (dst : StackVar) (name : string) : State :=
      let objs := get_local (st_points_to st) name in
      with_stack st (stack_update (st_stack st) dst objs).

    Definition transfer_load_global (st : State) (dst : StackVar) (name : string) : State :=
      let objs := get_global (st_points_to st) name in
      with_stack st (stack_update (st_stack st) dst objs).

    Definition transfer_set_local (st : State) (name : string) (src : StackVar) : State :=
      let objs := stack_lookup (st_stack st) src in
      let P' := set_local (st_points_to st) name objs in
      with_points st P'.

    Definition transfer_get_attr (st : State) (dst : StackVar) (obj : StackVar)
                                 (attr : string) (pp : ProgramPoint) : State :=
      let obj_set := stack_lookup (st_stack st) obj in
      let (st', result_objs, result_type) := eval_attribute st obj_set attr pp in
      let T' := type_update_set (st_types st') result_objs result_type in
      let st'' := with_types st' T' in
      with_stack st'' (stack_update (st_stack st'') dst result_objs).

    Definition transfer_set_attr (st : State) (obj : StackVar) (attr : string)
                                 (val : StackVar) : State :=
      let targets := stack_lookup (st_stack st) obj in
      let values  := stack_lookup (st_stack st) val in
      let P' := upd_points_to (st_points_to st) targets (FKName attr) values in
      let D' := mark_dirty_set (st_dirty st) targets (FKName attr) in
      with_pts_ty_dirty st P' (st_types st) D'.

    Definition transfer_construct_tuple (st : State) (dst : StackVar) (elems : list StackVar)
                                       (pp : ProgramPoint) : State :=
      let tup := alloc_site pp in
      let indexed_elems := List.combine (List.seq 0 (List.length elems)) elems in
      let P' := List.fold_left (fun acc pair =>
        let (idx, elem) := pair in
        let elem_objs := stack_lookup (st_stack st) elem in
        let P1 := upd_points_to acc (ObjectSet.singleton tup) (FKPos idx) elem_objs in
        upd_points_to P1 (ObjectSet.singleton tup) wildcard elem_objs
      ) indexed_elems (st_points_to st) in
      let T' := type_update (st_types st) tup (get_return make_tuple_constructor) in
      let st' := with_pts_ty_dirty st P' T' (st_dirty st) in
      with_stack st' (stack_update (st_stack st') dst (ObjectSet.singleton tup)).

    Definition transfer_construct_dict (st : State) (dst : StackVar)
                                       (pairs : list (StackVar * StackVar))
                                       (pp : ProgramPoint) : State :=
      let dict := alloc_site pp in
      let P' := List.fold_left (fun acc pair =>
        let (key_var, val_var) := pair in
        let key_objs := stack_lookup (st_stack st) key_var in
        let val_objs := stack_lookup (st_stack st) val_var in
        let P0 := upd_points_to acc (ObjectSet.singleton dict) wildcard val_objs in
        match ObjectSet.choose key_objs with
        | Some (ImmConst (KString s)) =>
            if Nat.eqb (ObjectSet.cardinal key_objs) 1
            then upd_points_to P0 (ObjectSet.singleton dict) (FKName s) val_objs
            else P0
        | _ => P0
        end
      ) pairs (st_points_to st) in
      let T' := type_update (st_types st) dict (get_return make_dict_constructor) in
      let st' := with_pts_ty_dirty st P' T' (st_dirty st) in
      with_stack st' (stack_update (st_stack st') dst (ObjectSet.singleton dict)).

    Definition transfer_bind (st : State) (dst func_var args_var kwargs_var : StackVar)
                             (pp : ProgramPoint) : State :=
      let bound      := alloc_site pp in
      let func_objs  := stack_lookup (st_stack st) func_var in
      let args_objs  := stack_lookup (st_stack st) args_var in
      let kwargs_objs:= stack_lookup (st_stack st) kwargs_var in
      let P1 := upd_points_to (st_points_to st) (ObjectSet.singleton bound) func_field  func_objs in
      let P2 := upd_points_to P1                 (ObjectSet.singleton bound) args_field  args_objs in
      let P3 := upd_points_to P2                 (ObjectSet.singleton bound) kwargs_field kwargs_objs in
      let self_objs := index_lookup P3 args_objs 0 in
      let P4 := if ObjectSet.is_empty self_objs then P3
                else upd_points_to P3 (ObjectSet.singleton bound) self_field self_objs in
      let T' := type_update (st_types st) bound (get_types (st_types st) func_objs) in
      let st' := with_pts_ty_dirty st P4 T' (st_dirty st) in
      with_stack st' (stack_update (st_stack st') dst (ObjectSet.singleton bound)).

    Definition transfer_unpack (st : State) (dsts : list StackVar) (src : StackVar) : State :=
      let src_objs := stack_lookup (st_stack st) src in
      let indexed_dsts := List.combine (List.seq 0 (List.length dsts)) dsts in
      let S' := List.fold_left (fun acc pair =>
        let (idx, dst) := pair in
        let objs := index_lookup (st_points_to st) src_objs idx in
        stack_update acc dst objs
      ) indexed_dsts (st_stack st) in
      with_stack st S'.

    Definition transfer_call (st : State) (dst : StackVar) (func : StackVar) (pp : ProgramPoint) : State :=
      let func_objs := stack_lookup (st_stack st) func in
      let (st', result_objs, result_type) := eval_call st func_objs pp in
      let T' := type_update_set (st_types st') result_objs result_type in
      let st'' := with_types st' T' in
      with_stack st'' (stack_update (st_stack st'') dst result_objs).

    (* Main transfer dispatcher: note the NEW ILookup case and no old dunder cases *)
    Definition transfer (st : State) (instr : Instruction) (pp : ProgramPoint) : State :=
      match instr with
      | IMov d s => with_stack st (stack_update (st_stack st) d (stack_lookup (st_stack st) s))
      | ILoadConst d c => transfer_load_const st d c
      | ILoadLocal d x => transfer_load_local st d x
      | ILoadGlobal d x => transfer_load_global st d x
      | ISetLocal x s => transfer_set_local st x s
      | IGetAttr d o a => transfer_get_attr st d o a pp
      | ISetAttr o a v => transfer_set_attr st o a v
      | IConstructTuple d xs => transfer_construct_tuple st d xs pp
      | IConstructDict d kvs => transfer_construct_dict st d kvs pp
      | IBind d f a k => transfer_bind st d f a k pp
      | IUnpack ds s => transfer_unpack st ds s
      | ICall d f => transfer_call st d f pp
      | ILookup d expr =>
          let (st', objs, ty) := eval_dunder st expr pp in
          let T' := type_update_set (st_types st') objs ty in
          let st'' := with_types st' T' in
          with_stack st'' (stack_update (st_stack st'') d objs)
      | IAssumeValue _ _ => st
      | IExit => st
      end.

  End Analysis.

End PointerAnalysis.
