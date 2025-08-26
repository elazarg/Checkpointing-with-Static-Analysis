(*
  Coq Pointer Analysis for TAC IR
  -------------------------------------------------
  Key points:
  - Single PointerAnalysis module (no duplicate definitions).
  - Field-key subsumption via AbstractField.matches and fm_lookup_match.
  - Strong/weak updates; tuple/dict constructors with wildcard + named keys.
  - bind derives self from args[0].
  - call joins effects across multiple callees; fresh result typed via
    get_return_type(object_type callee); optional param type update.
  - Reachability GC and small API.
*)

(* ===== Library Imports ===== *)
From Coq Require Import String List Bool Arith ZArith PeanoNat.
From Coq Require Import Sets.Ensembles.
From Coq Require Import FSets FSetWeakList FMaps FMapWeakList.
From Coq Require Import Relations DecidableType.
Import ListNotations.

Set Implicit Arguments.

(* Assume TAC module is provided by the caller *)
Import TAC.

(* ===== Pointer Analysis Module ===== *)
Module PointerAnalysis.

  (* ===== Abstract Objects ===== *)
  Module AbstractObject.
    Inductive t :=
    | Loc      : nat -> nat -> t           (* allocation site: (block, instr) *)
    | Param    : string -> t               (* external parameter *)
    | Imm      : ConstV -> t               (* immutable constant *)
    | Locals   : t                         (* local variables root *)
    | Globals  : t                         (* global variables root *)
    | Temp     : t                         (* stack temporaries root *)
    | RetUp    : t.                        (* summary return object *)

    Definition eq_dec : forall x y : t, {x = y} + {x <> y}.
    Proof.
      decide equality; try decide equality.
      - apply Nat.eq_dec.
      - apply Nat.eq_dec.
      - apply String.string_dec.
      - destruct c, c0; try discriminate; decide equality;
        try (apply Z.eq_dec); try (apply Bool.bool_dec); try (apply String.string_dec).
    Defined.
  End AbstractObject.

  (* ===== Abstract Field Keys ===== *)
  Module AbstractField.
    Definition t := FieldKey.

    Definition star   : t := FKName "*".
    Definition self   : t := FKName "self".
    Definition args   : t := FKName "args".
    Definition kwargs : t := FKName "kwargs".
    Definition func   : t := FKName "__func__".

    Definition eq_dec : forall x y : t, {x = y} + {x <> y}.
    Proof.
      decide equality; try decide equality.
      - apply Nat.eq_dec.
      - apply String.string_dec.
      - apply Nat.eq_dec.
      - apply String.string_dec.
    Defined.

    (* Subsuming match for FKPos/FKName/FKBoth. *)
    Definition matches (k1 k2 : t) : bool :=
      match k1, k2 with
      | FKPos n1,  FKPos n2  => Nat.eqb n1 n2
      | FKName s1, FKName s2 => String.eqb s1 s2
      | FKBoth n1 s1, FKBoth n2 s2 => andb (Nat.eqb n1 n2) (String.eqb s1 s2)
      | FKPos n,   FKBoth n' _ => Nat.eqb n n'
      | FKName s,  FKBoth _ s' => String.eqb s s'
      | FKBoth n' _, FKPos n   => Nat.eqb n n'
      | FKBoth _ s', FKName s  => String.eqb s s'
      | _, _ => false
      end.
  End AbstractField.

  (* ===== Type System Interface ===== *)
  Module Type TypeSystemSig.
    Import AbstractObject AbstractField.
    Parameter TypeExpr : Type.
    Parameter type_bot : TypeExpr.
    Parameter type_top : TypeExpr.
    Parameter type_join : TypeExpr -> TypeExpr -> TypeExpr.
    Parameter type_meet : TypeExpr -> TypeExpr -> TypeExpr.
    Parameter type_leq : TypeExpr -> TypeExpr -> bool.
    Parameter type_is_immutable : TypeExpr -> bool.

    Record EffectSummary := {
      eff_new : bool;                         (* allocates new object *)
      eff_update : option (nat * TypeExpr);   (* update param i to type *)
      eff_points_to_args : bool;              (* result may alias args/receiver *)
      eff_bound_method : bool                 (* reserved *)
    }.

    Parameter default_effect : EffectSummary.
    Parameter get_callable_effect : AbstractObject.t -> option EffectSummary.
    Parameter object_type : AbstractObject.t -> TypeExpr.
    Parameter alloc_type : Instruction -> TypeExpr.
    Parameter get_return_type : TypeExpr -> TypeExpr.
    Parameter apply_partial : TypeExpr -> list TypeExpr -> TypeExpr.
  End TypeSystemSig.

  Module Analysis (TS : TypeSystemSig).
    Import TS AbstractObject AbstractField.

    (* ===== Sets & Maps ===== *)
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
    Module AFMap := FMapWeakList.Make(AbstractField).

    (* ===== Domains ===== *)
    Definition FieldMap := AFMap.t ObjectSet.t.  (* field -> targets *)
    Definition PointsTo := AOMap.t FieldMap.     (* obj -> fields  *)
    Definition TypeMap  := AOMap.t TypeExpr.     (* obj -> type    *)
    Definition StackEnv := StackVar -> ObjectSet.t.
    Definition ProgramPoint := (nat * nat)%type.

    (* ===== Baselines ===== *)
    Definition empty_field_map : FieldMap := AFMap.empty _.
    Definition empty_points_to : PointsTo := AOMap.empty _.
    Definition empty_type_map  : TypeMap  := AOMap.empty _.
    Definition empty_stack     : StackEnv := fun _ => ObjectSet.empty.

    (* ===== Join ops (used by calls) ===== *)
    Definition join_field_maps (fm1 fm2 : FieldMap) : FieldMap :=
      AFMap.fold (fun f objs2 acc =>
        let objs1 := match AFMap.find f acc with | Some os => os | None => ObjectSet.empty end in
        AFMap.add f (ObjectSet.union objs1 objs2) acc) fm2 fm1.

    Definition join_points_to (P1 P2 : PointsTo) : PointsTo :=
      AOMap.fold (fun o fm2 acc =>
        let fm1 := match AOMap.find o acc with | Some fm => fm | None => AFMap.empty _ end in
        AOMap.add o (join_field_maps fm1 fm2) acc) P2 P1.

    Definition type_lookup (T : TypeMap) (o : AbstractObject.t) : TypeExpr :=
      match AOMap.find o T with | Some ty => ty | None => type_bot end.

    Definition join_type_maps (T1 T2 : TypeMap) : TypeMap :=
      AOMap.fold (fun o ty2 acc => AOMap.add o (type_join (type_lookup acc o) ty2) acc) T2 T1.

    (* ===== Points-to lookup (with field-key matching) ===== *)
    Definition fm_lookup_match (fm:FieldMap) (f:AbstractField.t) : ObjectSet.t :=
      AFMap.fold (fun k objs acc =>
        if orb (AbstractField.matches k f) (AbstractField.matches f k)
        then ObjectSet.union acc objs else acc) fm ObjectSet.empty.

    Definition points_to_lookup (P : PointsTo) (o : AbstractObject.t) (f : AbstractField.t) : ObjectSet.t :=
      match AOMap.find o P with
      | Some fm => fm_lookup_match fm f
      | None => ObjectSet.empty
      end.

    Definition points_to_update (P : PointsTo) (o : AbstractObject.t) (f : AbstractField.t)
                                (objs : ObjectSet.t) : PointsTo :=
      let fm := match AOMap.find o P with | Some fm => fm | None => empty_field_map end in
      let fm' := AFMap.add f objs fm in
      AOMap.add o fm' P.

    (* Strong/weak update by target cardinality *)
    Definition upd_points_to (P : PointsTo) (targets : ObjectSet.t) (f : AbstractField.t)
                             (new_objs : ObjectSet.t) : PointsTo :=
      if Nat.eqb (ObjectSet.cardinal targets) 1 then
        match ObjectSet.choose targets with
        | Some tgt => points_to_update P tgt f new_objs
        | None => P
        end
      else
        ObjectSet.fold (fun tgt P' =>
          let old := points_to_lookup P' tgt f in
          points_to_update P' tgt f (ObjectSet.union old new_objs)) targets P.

    (* ===== Types ===== *)
    Definition type_update (T : TypeMap) (o : AbstractObject.t) (ty : TypeExpr) : TypeMap :=
      AOMap.add o (type_join (type_lookup T o) ty) T.

    Definition type_weak_update (T : TypeMap) (objs : ObjectSet.t) (ty : TypeExpr) : TypeMap :=
      ObjectSet.fold (fun o acc => AOMap.add o (type_join (type_lookup acc o) ty) acc) objs T.

    (* ===== Stack ===== *)
    Definition stack_lookup (S : StackEnv) (v : StackVar) : ObjectSet.t := S v.
    Definition stack_update (S : StackEnv) (v : StackVar) (objs : ObjectSet.t) : StackEnv :=
      fun v' => if Nat.eqb v v' then objs else S v'.

    (* ===== Abstract State ===== *)
    Record AbstractState := { as_points_to : PointsTo; as_types : TypeMap }.
    Record State := { st_abstract : AbstractState; st_stack : StackEnv }.

    Definition empty_state : State := {| st_abstract := {| as_points_to := empty_points_to; as_types := empty_type_map |};
                                         st_stack := empty_stack |}.

    (* ===== Helpers ===== *)
    Definition alloc_site (pp : ProgramPoint) : AbstractObject.t := let '(b,i) := pp in Loc b i.

    Definition get_local  (P : PointsTo) (name : string) : ObjectSet.t := points_to_lookup P Locals  (FKName name).
    Definition set_local  (P : PointsTo) (name : string) (objs : ObjectSet.t) : PointsTo := upd_points_to P (ObjectSet.singleton Locals)  (FKName name) objs.
    Definition get_global (P : PointsTo) (name : string) : ObjectSet.t := points_to_lookup P Globals (FKName name).

    Definition attr_lookup (P : PointsTo) (objs : ObjectSet.t) (attr : string) : ObjectSet.t :=
      ObjectSet.fold (fun o acc => ObjectSet.union acc (points_to_lookup P o (FKName attr))) objs ObjectSet.empty.

    Definition index_lookup (P : PointsTo) (objs : ObjectSet.t) (idx : nat) : ObjectSet.t :=
      ObjectSet.fold (fun o acc =>
        let p := points_to_lookup P o (FKPos idx) in
        let s := points_to_lookup P o star in
        ObjectSet.union acc (ObjectSet.union p s)) objs ObjectSet.empty.

    (* ===== Transfers ===== *)
    Definition with_stack (st:State) (dst:StackVar) (objs:ObjectSet.t) : State :=
      {| st_abstract := st.(st_abstract); st_stack := stack_update st.(st_stack) dst objs |}.

    Definition transfer_mov (st : State) (dst src : StackVar) : State := with_stack st dst (stack_lookup (st_stack st) src).

    Definition transfer_load_const (st : State) (dst : StackVar) (c : ConstV) : State :=
      let obj := Imm c in
      let T' := type_update (as_types (st_abstract st)) obj (object_type obj) in
      {| st_abstract := {| as_points_to := as_points_to (st_abstract st); as_types := T' |};
         st_stack := stack_update (st_stack st) dst (ObjectSet.singleton obj) |}.

    Definition transfer_load_local  (st : State) (dst : StackVar) (name : string) : State := with_stack st dst (get_local  (as_points_to (st_abstract st)) name).
    Definition transfer_load_global (st : State) (dst : StackVar) (name : string) : State := with_stack st dst (get_global (as_points_to (st_abstract st)) name).

    Definition transfer_set_local (st : State) (name : string) (src : StackVar) : State :=
      let objs := stack_lookup (st_stack st) src in
      let P' := set_local (as_points_to (st_abstract st)) name objs in
      {| st_abstract := {| as_points_to := P'; as_types := as_types (st_abstract st) |}; st_stack := st_stack st |}.

    Definition transfer_get_attr (st : State) (dst : StackVar) (obj : StackVar) (attr : string) : State :=
      let src_objs := stack_lookup (st_stack st) obj in
      with_stack st dst (attr_lookup (as_points_to (st_abstract st)) src_objs attr).

    Definition transfer_set_attr (st : State) (obj : StackVar) (attr : string) (val : StackVar) : State :=
      let targets := stack_lookup (st_stack st) obj in
      let values  := stack_lookup (st_stack st) val in
      let P' := upd_points_to (as_points_to (st_abstract st)) targets (FKName attr) values in
      {| st_abstract := {| as_points_to := P'; as_types := as_types (st_abstract st) |}; st_stack := st_stack st |}.

    Definition transfer_construct_tuple (st : State) (dst : StackVar) (elems : list StackVar) (pp : ProgramPoint) : State :=
      let tup := alloc_site pp in
      let indexed := combine (seq 0 (length elems)) elems in
      let P' := fold_left (fun P_acc '(i, v) =>
                  let vals := stack_lookup (st_stack st) v in
                  let P1 := upd_points_to P_acc (ObjectSet.singleton tup) (FKPos i) vals in
                  upd_points_to P1 (ObjectSet.singleton tup) star vals) (as_points_to (st_abstract st)) indexed in
      let T' := type_update (as_types (st_abstract st)) tup (alloc_type (IConstructTuple dst elems)) in
      {| st_abstract := {| as_points_to := P'; as_types := T' |}; st_stack := stack_update (st_stack st) dst (ObjectSet.singleton tup) |}.

    Definition transfer_construct_dict (st : State) (dst : StackVar) (pairs : list (StackVar * StackVar)) (pp : ProgramPoint) : State :=
      let dict := alloc_site pp in
      let P' := fold_left (fun P_acc '(k,v) =>
                  let key_objs := stack_lookup (st_stack st) k in
                  let val_objs := stack_lookup (st_stack st) v in
                  (* always write wildcard; add named slot for singleton string literal *)
                  let P0 := upd_points_to P_acc (ObjectSet.singleton dict) star val_objs in
                  match ObjectSet.choose key_objs with
                  | Some (Imm (KString s)) => if Nat.eqb (ObjectSet.cardinal key_objs) 1
                                              then upd_points_to P0 (ObjectSet.singleton dict) (FKName s) val_objs
                                              else P0
                  | _ => P0
                  end) (as_points_to (st_abstract st)) pairs in
      let T' := type_update (as_types (st_abstract st)) dict (alloc_type (IConstructDict dst pairs)) in
      {| st_abstract := {| as_points_to := P'; as_types := T' |}; st_stack := stack_update (st_stack st) dst (ObjectSet.singleton dict) |}.

    (* Bind: derive self from args[0] *)
    Definition transfer_bind (st : State) (dst func args_v kwargs_v : StackVar) (pp : ProgramPoint) : State :=
      let bound := alloc_site pp in
      let func_o   := stack_lookup (st_stack st) func in
      let args_o   := stack_lookup (st_stack st) args_v in
      let kwargs_o := stack_lookup (st_stack st) kwargs_v in
      let P0 := as_points_to (st_abstract st) in
      let P1 := upd_points_to P0 (ObjectSet.singleton bound) func   func_o in
      let P2 := upd_points_to P1 (ObjectSet.singleton bound) args   args_o in
      let P3 := upd_points_to P2 (ObjectSet.singleton bound) kwargs kwargs_o in
      let recv := index_lookup P3 args_o 0 in
      let P4 := if Nat.eqb (ObjectSet.cardinal recv) 0 then P3
                else upd_points_to P3 (ObjectSet.singleton bound) self recv in
      let T' := type_update (as_types (st_abstract st)) bound (alloc_type (IBind dst func args_v kwargs_v)) in
      {| st_abstract := {| as_points_to := P4; as_types := T' |}; st_stack := stack_update (st_stack st) dst (ObjectSet.singleton bound) |}.

    (* Helpers for call *)
    Definition callable_args (P:PointsTo) (o:AbstractObject.t) : ObjectSet.t := points_to_lookup P o args.
    Definition callable_self (P:PointsTo) (o:AbstractObject.t) : ObjectSet.t := points_to_lookup P o self.

    Definition apply_call_effect (P : PointsTo) (T : TypeMap) (o_fun : AbstractObject.t)
                                 (eff : EffectSummary) (pp : ProgramPoint)
      : (PointsTo * TypeMap * ObjectSet.t) :=
      let fresh_obj := alloc_site pp in
      let base_res := if eff.(eff_new) then ObjectSet.singleton fresh_obj
                      else ObjectSet.singleton RetUp in
      let ali := if eff.(eff_points_to_args)
                 then ObjectSet.union (callable_args P o_fun) (callable_self P o_fun)
                 else ObjectSet.empty in
      let res := ObjectSet.union base_res ali in
      let T' := if eff.(eff_new)
                then AOMap.add fresh_obj (get_return_type (object_type o_fun)) T
                else T in
      let '(P1,T1) := match eff.(eff_update) with
                      | Some (i, new_ty) =>
                          let arg_objs := callable_args P o_fun in
                          let param_objs := index_lookup P arg_objs i in
                          (P, type_weak_update T' param_objs new_ty)
                      | None => (P, T')
                      end in
      let P2 := if andb eff.(eff_new) eff.(eff_points_to_args)
                then let ali2 := ObjectSet.union (callable_args P o_fun) (callable_self P o_fun) in
                     upd_points_to P1 (ObjectSet.singleton fresh_obj) star ali2
                else P1 in
      (P2, T1, res).

    Definition transfer_call (st : State) (dst : StackVar) (func_v : StackVar) (pp : ProgramPoint) : State :=
      let P0 := as_points_to (st_abstract st) in
      let T0 := as_types (st_abstract st) in
      let funs := stack_lookup (st_stack st) func_v in
      let '(P1,T1,R) :=
        ObjectSet.fold
          (fun o_fun '(Pacc,Tacc,Racc) =>
             let eff := match get_callable_effect o_fun with | Some e => e | None => default_effect end in
             let (P',T',R') := apply_call_effect P0 T0 o_fun eff pp in
             (join_points_to Pacc P', join_type_maps Tacc T', ObjectSet.union Racc R'))
          funs (P0,T0,ObjectSet.empty) in
      {| st_abstract := {| as_points_to := P1; as_types := T1 |};
         st_stack := stack_update (st_stack st) dst R |}.

    (* Main dispatcher *)
    Definition transfer (st : State) (instr : Instruction) (pp : ProgramPoint) : State :=
      match instr with
      | IMov d s                   => transfer_mov st d s
      | ILoadConst d c             => transfer_load_const st d c
      | ILoadLocal d x             => transfer_load_local st d x
      | ILoadGlobal d x            => transfer_load_global st d x
      | ISetLocal x s              => transfer_set_local st x s
      | IGetAttr d o a             => transfer_get_attr st d o a
      | ISetAttr o a v             => transfer_set_attr st o a v
      | IConstructTuple d xs       => transfer_construct_tuple st d xs pp
      | IConstructDict  d kvs      => transfer_construct_dict  st d kvs pp
      | IBind d f a k              => transfer_bind st d f a k pp
      | IUnpack ds src             =>
          let src_objs := stack_lookup (st_stack st) src in
          let idx_dsts := combine (seq 0 (length ds)) ds in
          let S' := fold_left (fun S_acc '(i,d) => stack_update S_acc d (index_lookup (as_points_to (st_abstract st)) src_objs i)) (st_stack st) idx_dsts in
          {| st_abstract := st_abstract st; st_stack := S' |}
      | ICall d f                  => transfer_call st d f pp
      | ILookupDunderUnary _ _ _   => st
      | ILookupDunderBinary _ _ _ _=> st
      | ILookupOverload _ _ _ _    => st
      | IAssumeValue _ _           => st
      | IExit                      => st
      end.

    (* ===== Reachability & GC ===== *)
    Definition reachable_from_object (P : PointsTo) (o : AbstractObject.t) : ObjectSet.t :=
      match AOMap.find o P with
      | Some fm => AFMap.fold (fun _ objs acc => ObjectSet.union acc objs) fm ObjectSet.empty
      | None => ObjectSet.empty
      end.

    Fixpoint compute_reachable (P : PointsTo) (work : ObjectSet.t)
                               (seen : ObjectSet.t) (fuel : nat) : ObjectSet.t :=
      match fuel with
      | 0 => seen
      | S fuel' =>
        if ObjectSet.is_empty work then seen else
        match ObjectSet.choose work with
        | Some o =>
            let work' := ObjectSet.remove o work in
            if ObjectSet.mem o seen then compute_reachable P work' seen fuel' else
            let seen' := ObjectSet.add o seen in
            let wnew  := reachable_from_object P o in
            compute_reachable P (ObjectSet.union work' wnew) seen' fuel'
        | None => seen
        end
      end.

    Definition get_roots (P : PointsTo) (live : list string) : ObjectSet.t :=
      let r0 := ObjectSet.singleton Locals in
      fold_left (fun acc x => ObjectSet.union acc (get_local P x)) live r0.

    Definition abstract_gc (st : AbstractState) (live : list string) : AbstractState :=
      let P := as_points_to st in
      let T := as_types st in
      let roots := get_roots P live in
      let reach := compute_reachable P roots ObjectSet.empty 1000 in
      let P' := AOMap.fold (fun o fm acc => if ObjectSet.mem o reach then AOMap.add o fm acc else acc) P empty_points_to in
      let T' := AOMap.fold (fun o ty acc => if ObjectSet.mem o reach then AOMap.add o ty acc else acc) T empty_type_map in
      {| as_points_to := P'; as_types := T' |}.

    (* ===== External API ===== *)
    Module API.
      Definition get_object_types (st : AbstractState) (objs : ObjectSet.t) : TypeExpr :=
        ObjectSet.fold (fun obj acc => type_join acc (type_lookup (as_types st) obj)) objs type_bot.

      Definition set_object_type (st : AbstractState) (obj : AbstractObject.t) (ty : TypeExpr) : AbstractState :=
        {| as_points_to := as_points_to st; as_types := type_update (as_types st) obj ty |}.

      Definition get_var_objects (st : State) (v : StackVar) : ObjectSet.t := stack_lookup (st_stack st) v.

      Definition may_alias (objs1 objs2 : ObjectSet.t) : bool := negb (ObjectSet.is_empty (ObjectSet.inter objs1 objs2)).

      Definition get_reachable_from_var (st : State) (v : StackVar) : ObjectSet.t :=
        let objs := get_var_objects st v in
        compute_reachable (as_points_to (st_abstract st)) objs ObjectSet.empty 100.
    End API.

  End Analysis.

End PointerAnalysis.
