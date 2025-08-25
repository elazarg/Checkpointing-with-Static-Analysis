From Coq Require Import String List Bool Arith ZArith PeanoNat.
From Coq Require Import Sets.Ensembles.
From Coq Require Import FSets FSetWeakList FMaps FMapWeakList.
From Coq Require Import Relations DecidableType.
Import ListNotations.

(* ===== Import TAC Definitions ===== *)
(* We assume TAC module is available with these definitions *)
Module TAC.
  Definition StackVar := nat.
  
  Inductive FieldKey :=
  | FKPos  : nat -> FieldKey
  | FKName : string -> FieldKey
  | FKBoth : nat -> string -> FieldKey.
  
  Inductive ConstV : Type :=
  | KInt      : Z -> ConstV
  | KBool     : bool -> ConstV
  | KString   : string -> ConstV
  | KNone     : ConstV
  | KStopIter : ConstV.
  
  Inductive Instruction : Type :=
  | IMov          : StackVar -> StackVar -> Instruction
  | ILoadConst    : StackVar -> ConstV -> Instruction
  | ILoadLocal    : StackVar -> string -> Instruction
  | ILoadGlobal   : StackVar -> string -> Instruction
  | ISetLocal     : string -> StackVar -> Instruction
  | ILookupDunderUnary  : StackVar -> string -> StackVar -> Instruction
  | ILookupDunderBinary : StackVar -> string -> StackVar -> StackVar -> Instruction
  | IResolveOverload    : StackVar -> StackVar -> StackVar -> StackVar -> Instruction
  | IGetAttr      : StackVar -> StackVar -> string -> Instruction
  | ISetAttr      : StackVar -> string -> StackVar -> Instruction
  | IUnpack       : list StackVar -> StackVar -> Instruction
  | IConstructTuple : StackVar -> list StackVar -> Instruction
  | IConstructDict  : StackVar -> list (StackVar * StackVar) -> Instruction
  | IBind         : StackVar -> StackVar -> StackVar -> StackVar -> Instruction
  | ICall         : StackVar -> StackVar -> Instruction
  | IAssumeValue  : StackVar -> ConstV -> Instruction
  | IExit         : Instruction.
End TAC.

Import TAC.

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
    - apply Z.eq_dec.
    - apply Bool.bool_dec.
    - apply String.string_dec.
  Defined.
End AbstractObject.

(* ===== Field Keys ===== *)
Module AbstractField.
  Definition t := FieldKey.
  
  Definition star : t := FKName "*".        (* wildcard field *)
  Definition args : t := FKName "args".     (* for bound callables *)
  Definition kwargs : t := FKName "kwargs". (* for bound callables *)
  
  Definition eq_dec : forall x y : t, {x = y} + {x <> y}.
  Proof.
    decide equality; try decide equality.
    - apply Nat.eq_dec.
    - apply String.string_dec.
    - apply Nat.eq_dec.
    - apply String.string_dec.
  Defined.
  
  (* Check if a field key matches (with wildcard support) *)
  Definition matches (k1 k2 : t) : bool :=
    match k1, k2 with
    | FKPos n1, FKPos n2 => Nat.eqb n1 n2
    | FKName s1, FKName s2 => String.eqb s1 s2
    | FKBoth n1 s1, FKBoth n2 s2 => andb (Nat.eqb n1 n2) (String.eqb s1 s2)
    | FKPos n, FKBoth n' _ => Nat.eqb n n'
    | FKName s, FKBoth _ s' => String.eqb s s'
    | FKBoth n' _, FKPos n => Nat.eqb n n'
    | FKBoth _ s', FKName s => String.eqb s s'
    | _, _ => false
    end.
End AbstractField.

(* ===== Type System Interface ===== *)
Module Type TypeSystemInterface.
  Import AbstractObject.
  Import AbstractField.
  
  (* Abstract type expressions *)
  Parameter TypeExpr : Type.
  Parameter type_bot : TypeExpr.
  Parameter type_top : TypeExpr.
  Parameter type_join : TypeExpr -> TypeExpr -> TypeExpr.
  Parameter type_meet : TypeExpr -> TypeExpr -> TypeExpr.
  Parameter type_leq : TypeExpr -> TypeExpr -> bool.
  
  (* Effect summaries for callables *)
  Record EffectSummary := {
    eff_new : bool;                    (* allocates new object *)
    eff_update : list (nat * t);       (* updated fields: (param_idx, field) pairs *)
    eff_points_to_args : bool;         (* result may alias arguments *)
  }.
  
  (* Default effect: pure function *)
  Parameter default_effect : EffectSummary.
  
  (* Get effect summary for a callable object *)
  Parameter get_callable_effect : AbstractObject.t -> option EffectSummary.
  
  (* Get type of an abstract object *)
  Parameter object_type : AbstractObject.t -> TypeExpr.
  
  (* Type of allocation based on instruction *)
  Parameter alloc_type : Instruction -> TypeExpr.
End TypeSystemInterface.

(* ===== Main Analysis Module ===== *)
Module PointerAnalysis (TS : TypeSystemInterface).
  Import TS.
  Import AbstractObject.
  Import AbstractField.
  
  (* ===== Object Sets using FSets ===== *)
  Module AODec <: DecidableType.
    Definition t := AbstractObject.t.
    Definition eq := @eq t.
    Definition eq_refl := @eq_refl t.
    Definition eq_sym := @eq_sym t.
    Definition eq_trans := @eq_trans t.
    Definition eq_dec := AbstractObject.eq_dec.
  End AODec.
  
  Module ObjectSet := FSetWeakList.Make(AODec).
  
  (* ===== Points-to Domain ===== *)
  Module AOMap := FMapWeakList.Make(AODec).
  Module AFMap := FMapWeakList.Make(AbstractField).
  
  Definition FieldMap := AFMap.t ObjectSet.t.
  Definition PointsTo := AOMap.t FieldMap.
  
  Definition empty_points_to : PointsTo := AOMap.empty FieldMap.
  
  (* Lookup with proper handling of empty cases *)
  Definition points_to_lookup (P : PointsTo) (o : AbstractObject.t) (f : AbstractField.t) : ObjectSet.t :=
    match AOMap.find o P with
    | Some fm => 
        match AFMap.find f fm with
        | Some objs => objs
        | None => ObjectSet.empty
        end
    | None => ObjectSet.empty
    end.
  
  (* Points-to update with proper field map handling *)
  Definition points_to_update (P : PointsTo) (o : AbstractObject.t) (f : AbstractField.t) 
                               (objs : ObjectSet.t) : PointsTo :=
    let fm := match AOMap.find o P with
             | Some fm => fm
             | None => AFMap.empty ObjectSet.t
             end in
    let fm' := AFMap.add f objs fm in
    AOMap.add o fm' P.
  
  (* Weak/Strong update based on target set size *)
  Definition upd_points_to (P : PointsTo) (targets : ObjectSet.t) (f : AbstractField.t) 
                           (new_objs : ObjectSet.t) : PointsTo :=
    if ObjectSet.cardinal targets =? 1
    then 
      (* Strong update *)
      match ObjectSet.choose targets with
      | Some tgt => points_to_update P tgt f new_objs
      | None => P  (* shouldn't happen *)
      end
    else
      (* Weak update *)
      ObjectSet.fold (fun tgt P' =>
        let old := points_to_lookup P' tgt f in
        points_to_update P' tgt f (ObjectSet.union old new_objs)
      ) targets P.
  
  (* ===== Type Domain ===== *)
  Definition TypeMap := AOMap.t TypeExpr.
  
  Definition empty_type_map : TypeMap := AOMap.empty TypeExpr.
  
  Definition type_lookup (T : TypeMap) (o : AbstractObject.t) : TypeExpr :=
    match AOMap.find o T with
    | Some ty => ty
    | None => type_bot
    end.
  
  Definition type_update (T : TypeMap) (o : AbstractObject.t) (ty : TypeExpr) : TypeMap :=
    let old_ty := type_lookup T o in
    AOMap.add o (type_join old_ty ty) T.
  
  (* ===== Abstract State ===== *)
  Record AbstractState := {
    as_points_to : PointsTo;
    as_types : TypeMap;
    (* Dirty domain omitted for now *)
  }.
  
  Definition empty_state : AbstractState := {|
    as_points_to := empty_points_to;
    as_types := empty_type_map;
  |}.
  
  (* ===== Stack Environment ===== *)
  Definition StackEnv := StackVar -> ObjectSet.t.
  
  Definition empty_stack : StackEnv := fun _ => ObjectSet.empty.
  
  Definition stack_lookup (S : StackEnv) (v : StackVar) : ObjectSet.t := S v.
  
  Definition stack_update (S : StackEnv) (v : StackVar) (objs : ObjectSet.t) : StackEnv :=
    fun v' => if Nat.eq_dec v v' then objs else S v'.
  
  (* ===== Combined State ===== *)
  Record State := {
    st_abstract : AbstractState;
    st_stack : StackEnv;
  }.
  
  Definition empty_combined_state : State := {|
    st_abstract := empty_state;
    st_stack := empty_stack;
  |}.
  
  (* ===== Helper Functions ===== *)
  
  (* Program point *)
  Definition ProgramPoint := (nat * nat)%type.
  
  (* Create allocation site from program point *)
  Definition alloc_site (pp : ProgramPoint) : AbstractObject.t :=
    let (block, instr) := pp in
    Loc block instr.
  
  (* Get local variable objects *)
  Definition get_local (P : PointsTo) (name : string) : ObjectSet.t :=
    points_to_lookup P Locals (FKName name).
  
  (* Set local variable objects *)
  Definition set_local (P : PointsTo) (name : string) (objs : ObjectSet.t) : PointsTo :=
    upd_points_to P (ObjectSet.singleton Locals) (FKName name) objs.
  
  (* Get global variable objects *)
  Definition get_global (P : PointsTo) (name : string) : ObjectSet.t :=
    points_to_lookup P Globals (FKName name).
  
  (* Attribute lookup - union over all objects *)
  Definition attr_lookup (P : PointsTo) (objs : ObjectSet.t) (attr : string) : ObjectSet.t :=
    ObjectSet.fold (fun o acc =>
      ObjectSet.union acc (points_to_lookup P o (FKName attr))
    ) objs ObjectSet.empty.
  
  (* Index lookup with wildcard support *)
  Definition index_lookup (P : PointsTo) (objs : ObjectSet.t) (idx : nat) : ObjectSet.t :=
    ObjectSet.fold (fun o acc =>
      let from_idx := points_to_lookup P o (FKPos idx) in
      let from_star := points_to_lookup P o star in
      ObjectSet.union acc (ObjectSet.union from_idx from_star)
    ) objs ObjectSet.empty.
  
  (* ===== Transfer Functions ===== *)
  
  (* Move: $d := $s *)
  Definition transfer_mov (st : State) (dst src : StackVar) : State :=
    let S := st_stack st in
    let objs := stack_lookup S src in
    {| st_abstract := st_abstract st;
       st_stack := stack_update S dst objs |}.
  
  (* Load constant: $d := const *)
  Definition transfer_load_const (st : State) (dst : StackVar) (c : ConstV) : State :=
    let S := st_stack st in
    let obj := Imm c in
    let T := as_types (st_abstract st) in
    let T' := type_update T obj (object_type obj) in
    {| st_abstract := {| as_points_to := as_points_to (st_abstract st);
                        as_types := T' |};
       st_stack := stack_update S dst (ObjectSet.singleton obj) |}.
  
  (* Load local: $d := local(x) *)
  Definition transfer_load_local (st : State) (dst : StackVar) (name : string) : State :=
    let P := as_points_to (st_abstract st) in
    let S := st_stack st in
    let objs := get_local P name in
    {| st_abstract := st_abstract st;
       st_stack := stack_update S dst objs |}.
  
  (* Load global: $d := global(x) *)
  Definition transfer_load_global (st : State) (dst : StackVar) (name : string) : State :=
    let P := as_points_to (st_abstract st) in
    let S := st_stack st in
    let objs := get_global P name in
    {| st_abstract := st_abstract st;
       st_stack := stack_update S dst objs |}.
  
  (* Set local: local(x) := $s *)
  Definition transfer_set_local (st : State) (name : string) (src : StackVar) : State :=
    let P := as_points_to (st_abstract st) in
    let T := as_types (st_abstract st) in
    let S := st_stack st in
    let objs := stack_lookup S src in
    let P' := set_local P name objs in
    {| st_abstract := {| as_points_to := P'; as_types := T |};
       st_stack := S |}.
  
  (* Get attribute: $d := $o.attr *)
  Definition transfer_get_attr (st : State) (dst : StackVar) (obj_var : StackVar) (attr : string) : State :=
    let P := as_points_to (st_abstract st) in
    let S := st_stack st in
    let obj_set := stack_lookup S obj_var in
    let result := attr_lookup P obj_set attr in
    {| st_abstract := st_abstract st;
       st_stack := stack_update S dst result |}.
  
  (* Set attribute: $o.attr := $v *)
  Definition transfer_set_attr (st : State) (obj_var : StackVar) (attr : string) (val_var : StackVar) : State :=
    let P := as_points_to (st_abstract st) in
    let T := as_types (st_abstract st) in
    let S := st_stack st in
    let targets := stack_lookup S obj_var in
    let values := stack_lookup S val_var in
    let P' := upd_points_to P targets (FKName attr) values in
    {| st_abstract := {| as_points_to := P'; as_types := T |};
       st_stack := S |}.
  
  (* Construct tuple: $d := tuple($e0, ..., $en) *)
  Definition transfer_construct_tuple (st : State) (dst : StackVar) (elems : list StackVar) 
                                      (pp : ProgramPoint) : State :=
    let P := as_points_to (st_abstract st) in
    let T := as_types (st_abstract st) in
    let S := st_stack st in
    let tup := alloc_site pp in
    
    (* Wire up tuple elements at both positional and star fields *)
    let indexed_elems := List.combine (List.seq 0 (List.length elems)) elems in
    let P' := List.fold_left (fun P_acc pair =>
      let (idx, elem_var) := pair in
      let elem_objs := stack_lookup S elem_var in
      let P1 := upd_points_to P_acc (ObjectSet.singleton tup) (FKPos idx) elem_objs in
      upd_points_to P1 (ObjectSet.singleton tup) star elem_objs
    ) indexed_elems P in
    
    (* Update type *)
    let T' := type_update T tup (alloc_type (IConstructTuple dst elems)) in
    
    {| st_abstract := {| as_points_to := P'; as_types := T' |};
       st_stack := stack_update S dst (ObjectSet.singleton tup) |}.
  
  (* Construct dict: $d := dict([(k1,v1), ...]) *)
  Definition transfer_construct_dict (st : State) (dst : StackVar) 
                                     (pairs : list (StackVar * StackVar)) 
                                     (pp : ProgramPoint) : State :=
    let P := as_points_to (st_abstract st) in
    let T := as_types (st_abstract st) in
    let S := st_stack st in
    let dict := alloc_site pp in
    
    (* Wire up dictionary entries *)
    let P' := List.fold_left (fun P_acc pair =>
      let (key_var, val_var) := pair in
      let key_objs := stack_lookup S key_var in
      let val_objs := stack_lookup S val_var in
      (* Check if key is a string literal *)
      match ObjectSet.choose key_objs with
      | Some (Imm (KString s)) =>
          (* String key: use named field *)
          upd_points_to P_acc (ObjectSet.singleton dict) (FKName s) val_objs
      | _ =>
          (* Non-string or multiple keys: use star field *)
          upd_points_to P_acc (ObjectSet.singleton dict) star val_objs
      end
    ) pairs P in
    
    (* Update type *)
    let T' := type_update T dict (alloc_type (IConstructDict dst pairs)) in
    
    {| st_abstract := {| as_points_to := P'; as_types := T' |};
       st_stack := stack_update S dst (ObjectSet.singleton dict) |}.
  
  (* Bind: $d := bind($f, $a, $k) - creates bound callable *)
  Definition transfer_bind (st : State) (dst func_var args_var kwargs_var : StackVar) 
                           (pp : ProgramPoint) : State :=
    let P := as_points_to (st_abstract st) in
    let T := as_types (st_abstract st) in
    let S := st_stack st in
    let bound := alloc_site pp in
    
    let func_objs := stack_lookup S func_var in
    let args_objs := stack_lookup S args_var in
    let kwargs_objs := stack_lookup S kwargs_var in
    
    (* Wire up bound callable *)
    let P1 := upd_points_to P (ObjectSet.singleton bound) (FKName "__func__") func_objs in
    let P2 := upd_points_to P1 (ObjectSet.singleton bound) args args_objs in
    let P' := upd_points_to P2 (ObjectSet.singleton bound) kwargs kwargs_objs in
    
    (* Update type *)
    let T' := type_update T bound (alloc_type (IBind dst func_var args_var kwargs_var)) in
    
    {| st_abstract := {| as_points_to := P'; as_types := T' |};
       st_stack := stack_update S dst (ObjectSet.singleton bound) |}.
  
  (* Unpack: [$d0, ..., $dn] := unpack($s) *)
  Definition transfer_unpack (st : State) (dsts : list StackVar) (src : StackVar) : State :=
    let P := as_points_to (st_abstract st) in
    let S := st_stack st in
    let src_objs := stack_lookup S src in
    
    (* For each destination, collect objects from appropriate indices *)
    let indexed_dsts := List.combine (List.seq 0 (List.length dsts)) dsts in
    let S' := List.fold_left (fun S_acc pair =>
      let (idx, dst) := pair in
      let objs := index_lookup P src_objs idx in
      stack_update S_acc dst objs
    ) indexed_dsts S in
    
    {| st_abstract := st_abstract st;
       st_stack := S' |}.
  
  (* Apply effects from a function call *)
  Definition apply_call_effects (P : PointsTo) (T : TypeMap) (S : StackEnv)
                                (eff : EffectSummary) (func_objs args_objs : ObjectSet.t) 
                                (pp : ProgramPoint) : (PointsTo * TypeMap * ObjectSet.t) :=
    let result_objs := 
      if eff.(eff_new)
      then ObjectSet.singleton (alloc_site pp)
      else if eff.(eff_points_to_args)
           then ObjectSet.union args_objs (ObjectSet.singleton RetUp)
           else ObjectSet.singleton RetUp in
    
    (* Apply field updates from effects *)
    let P' := List.fold_left (fun P_acc update =>
      let (param_idx, field) := update in
      (* This would need to resolve which objects correspond to param_idx *)
      (* Simplified for now *)
      P_acc
    ) eff.(eff_update) P in
    
    (* Update type for new allocation *)
    let T' := if eff.(eff_new)
             then type_update T (alloc_site pp) (alloc_type (ICall 0 0))
             else T in
    
    (P', T', result_objs).
  
  (* Call: $d := call($f) *)
  Definition transfer_call (st : State) (dst : StackVar) (func_var : StackVar) 
                           (pp : ProgramPoint) : State :=
    let P := as_points_to (st_abstract st) in
    let T := as_types (st_abstract st) in
    let S := st_stack st in
    let func_objs := stack_lookup S func_var in
    
    (* Get effect summaries for all possible callables *)
    let results := ObjectSet.fold (fun func_obj acc =>
      match get_callable_effect func_obj with
      | Some eff =>
          (* Get arguments if this is a bound callable *)
          let args_objs := 
            if ObjectSet.mem func_obj (points_to_lookup P func_obj args)
            then points_to_lookup P func_obj args
            else ObjectSet.empty in
          
          let (P', T', res) := apply_call_effects P T S eff func_objs args_objs pp in
          let (P_acc, T_acc, res_acc) := acc in
          (P', T', ObjectSet.union res_acc res)
      | None =>
          (* Unknown callable - conservative approximation *)
          let (P_acc, T_acc, res_acc) := acc in
          (P_acc, T_acc, ObjectSet.add RetUp res_acc)
      end
    ) func_objs (P, T, ObjectSet.empty) in
    
    let (P', T', result_objs) := results in
    
    {| st_abstract := {| as_points_to := P'; as_types := T' |};
       st_stack := stack_update S dst result_objs |}.
  
  (* Main transfer function *)
  Definition transfer (st : State) (instr : Instruction) (pp : ProgramPoint) : State :=
    match instr with
    | IMov dst src => transfer_mov st dst src
    | ILoadConst dst c => transfer_load_const st dst c
    | ILoadLocal dst name => transfer_load_local st dst name
    | ILoadGlobal dst name => transfer_load_global st dst name
    | ISetLocal name src => transfer_set_local st name src
    | IGetAttr dst obj attr => transfer_get_attr st dst obj attr
    | ISetAttr obj attr val => transfer_set_attr st obj attr val
    | IConstructTuple dst elems => transfer_construct_tuple st dst elems pp
    | IConstructDict dst pairs => transfer_construct_dict st dst pairs pp
    | IBind dst f a k => transfer_bind st dst f a k pp
    | IUnpack dsts src => transfer_unpack st dsts src
    | ICall dst func => transfer_call st dst func pp
    | ILookupDunderUnary dst _ _ => st  (* Pure - no heap change *)
    | ILookupDunderBinary dst _ _ _ => st  (* Pure - no heap change *)
    | IResolveOverload dst _ _ _ => st  (* Pure - no heap change *)
    | IAssumeValue _ _ => st  (* No state change *)
    | IExit => st  (* No state change *)
    end.
  
  (* ===== Reachability Analysis ===== *)
  
  (* Collect all objects reachable from a single object *)
  Definition reachable_from_object (P : PointsTo) (o : AbstractObject.t) : ObjectSet.t :=
    match AOMap.find o P with
    | Some fm =>
        AFMap.fold (fun _ objs acc =>
          ObjectSet.union acc objs
        ) fm ObjectSet.empty
    | None => ObjectSet.empty
    end.
  
  (* Fixed-point computation of reachability *)
  Fixpoint compute_reachable (P : PointsTo) (worklist : ObjectSet.t) 
                             (visited : ObjectSet.t) (fuel : nat) : ObjectSet.t :=
    match fuel with
    | 0 => visited
    | S fuel' =>
        if ObjectSet.is_empty worklist
        then visited
        else
          match ObjectSet.choose worklist with
          | Some o =>
              let worklist' := ObjectSet.remove o worklist in
              if ObjectSet.mem o visited
              then compute_reachable P worklist' visited fuel'
              else
                let visited' := ObjectSet.add o visited in
                let new_objs := reachable_from_object P o in
                let worklist'' := ObjectSet.union worklist' new_objs in
                compute_reachable P worklist'' visited' fuel'
          | None => visited
          end
    end.
  
  (* Get root objects from live variables *)
  Definition get_roots (P : PointsTo) (live : list string) : ObjectSet.t :=
    List.fold_left (fun acc var =>
      ObjectSet.union acc (get_local P var)
    ) live ObjectSet.empty.
  
  (* Abstract GC: restrict state to reachable objects *)
  Definition abstract_gc (st : AbstractState) (live : list string) : AbstractState :=
    let P := as_points_to st in
    let T := as_types st in
    let roots := get_roots P live in
    let reachable := compute_reachable P roots ObjectSet.empty 1000 in
    
    (* Filter points-to map *)
    let P' := AOMap.fold (fun o fm acc =>
      if ObjectSet.mem o reachable
      then AOMap.add o fm acc
      else acc
    ) P empty_points_to in
    
    (* Filter type map *)
    let T' := AOMap.fold (fun o ty acc =>
      if ObjectSet.mem o reachable
      then AOMap.add o ty acc
      else acc
    ) T empty_type_map in
    
    {| as_points_to := P'; as_types := T' |}.
  
  (* ===== Lattice Operations ===== *)
  
  (* Join points-to maps *)
  Definition join_points_to (P1 P2 : PointsTo) : PointsTo :=
    AOMap.fold (fun o fm1 acc =>
      match AOMap.find o P2 with
      | Some fm2 =>
          (* Join field maps *)
          let fm_joined := AFMap.fold (fun f objs1 fm_acc =>
            match AFMap.find f fm2 with
            | Some objs2 => AFMap.add f (ObjectSet.union objs1 objs2) fm_acc
            | None => AFMap.add f objs1 fm_acc
            end
          ) fm1 fm2 in
          AOMap.add o fm_joined acc
      | None => AOMap.add o fm1 acc
      end
    ) P1 P2.
  
  (* Join type maps *)
  Definition join_type_maps (T1 T2 : TypeMap) : TypeMap :=
    AOMap.fold (fun o ty1 acc =>
      match AOMap.find o T2 with
      | Some ty2 => AOMap.add o (type_join ty1 ty2) acc
      | None => AOMap.add o ty1 acc
      end
    ) T1 T2.
  
  (* Join abstract states *)
  Definition join_states (st1 st2 : AbstractState) : AbstractState := {|
    as_points_to := join_points_to (as_points_to st1) (as_points_to st2);
    as_types := join_type_maps (as_types st1) (as_types st2);
  |}.
  
  (* Order on abstract states *)
  Definition state_leq (st1 st2 : AbstractState) : Prop :=
    (forall o f, ObjectSet.Subset 
      (points_to_lookup (as_points_to st1) o f)
      (points_to_lookup (as_points_to st2) o f)) /\
    (forall o, type_leq (type_lookup (as_types st1) o) 
                        (type_lookup (as_types st2) o) = true).
  
  (* ===== Key Properties (Admitted) ===== *)
  
  (* Join is least upper bound *)
  Lemma join_is_lub :
    forall st1 st2 st',
    state_leq st1 st' ->
    state_leq st2 st' ->
    state_leq (join_states st1 st2) st'.
  Proof.
    Admitted.
  
  (* Transfer functions are monotonic *)
  Lemma transfer_monotonic :
    forall st1 st2 instr pp,
    state_leq st1 st2 ->
    state_leq 
      (st_abstract (transfer {| st_abstract := st1; st_stack := empty_stack |} instr pp))
      (st_abstract (transfer {| st_abstract := st2; st_stack := empty_stack |} instr pp)).
  Proof.
    Admitted.
  
  (* GC preserves soundness *)
  Lemma gc_sound :
    forall st live st',
    st' = abstract_gc st live ->
    (* For all reachable objects, their points-to info is preserved *)
    True.
  Proof.
    Admitted.
  
End PointerAnalysis.
