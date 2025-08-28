(*
  TYPE_COMPLETE.v
  Complete Type System with Protocol Satisfaction and Method Binding
*)
From Coq Require Import String List Bool Arith PeanoNat Lia Program.Wf ZArith.
Import ListNotations.

Set Implicit Arguments.

Module CompleteTypeSystem <: TypeSystemSig.
  Import TAC.

  (* Use the parameterized approach for SideEffect to avoid mutual induction issues *)
  Parameter TypeExpr : Type.
  
  Record SideEffect := {
    se_new            : bool;
    se_bound_method   : bool; 
    se_update         : option TypeExpr;
    se_update_indices : list nat;
    se_points_to_args : bool
  }.

  (* Core type definitions *)
  Inductive FieldKey :=
  | FK_Pos  : nat -> FieldKey
  | FK_Name : string -> FieldKey  
  | FK_Both : nat -> string -> FieldKey.
  
  Definition Row := (FieldKey * TypeExpr)%type.
  Definition Rows := list Row.

  Inductive LiteralValue :=
  | L_Int    : Z -> LiteralValue
  | L_Bool   : bool -> LiteralValue
  | L_String : string -> LiteralValue
  | L_None   : LiteralValue
  | L_Tuple  : list TypeExpr -> LiteralValue.

  Inductive TypeExpr_ :=
  | TE_Bot
  | TE_Top  
  | TE_Any
  | TE_TVar      : nat -> bool -> TypeExpr_  (* id, is_variadic *)
  | TE_Literal   : LiteralValue -> TypeExpr_
  | TE_Union     : list TypeExpr -> TypeExpr_
  | TE_Row       : Rows -> TypeExpr_
  | TE_Fun       : Rows -> TypeExpr -> SideEffect -> 
                   bool -> list nat -> TypeExpr_  (* params, ret, eff, is_prop, tyvars *)
  | TE_Overload  : list TypeExpr -> TypeExpr_
  | TE_Class     : string -> Rows -> list TypeExpr -> 
                   bool -> list nat -> TypeExpr_  (* name, members, bases, is_protocol, tyvars *)
  | TE_Module    : string -> Rows -> TypeExpr_
  | TE_Instance  : TypeExpr -> list TypeExpr -> TypeExpr_
  | TE_Ref       : string -> TypeExpr_.

  Axiom TypeExpr_eq : TypeExpr = TypeExpr_.

  Definition cast (t : TypeExpr_) : TypeExpr := 
    eq_rect_r (fun T => T) t TypeExpr_eq.
  Definition uncast (t : TypeExpr) : TypeExpr_ := 
    eq_rect TypeExpr (fun _ => TypeExpr_) t _ TypeExpr_eq.

  (* String equality *)
  Definition str_eqb := String.eqb.

  (* ===== Key operations ===== *)
  
  Definition field_key_eqb (k1 k2 : FieldKey) : bool :=
    match k1, k2 with
    | FK_Pos n1, FK_Pos n2 => Nat.eqb n1 n2
    | FK_Name s1, FK_Name s2 => str_eqb s1 s2
    | FK_Both n1 s1, FK_Both n2 s2 => andb (Nat.eqb n1 n2) (str_eqb s1 s2)
    | _, _ => false
    end.

  Definition key_matches (pattern arg : FieldKey) : bool :=
    match pattern, arg with
    | FK_Pos n1, FK_Pos n2 => Nat.eqb n1 n2
    | FK_Name s1, FK_Name s2 => str_eqb s1 s2
    | FK_Both n s, FK_Pos n' => Nat.eqb n n'
    | FK_Both n s, FK_Name s' => str_eqb s s'
    | FK_Pos n, FK_Both n' _ => Nat.eqb n n'
    | FK_Name s, FK_Both _ s' => str_eqb s s'  
    | FK_Both n1 s1, FK_Both n2 s2 => andb (Nat.eqb n1 n2) (str_eqb s1 s2)
    | _, _ => false
    end.

  (* ===== Size measure ===== *)
  
  Fixpoint size (t : TypeExpr) : nat :=
    match uncast t with
    | TE_Bot | TE_Top | TE_Any | TE_TVar _ _ | TE_Ref _ => 1
    | TE_Literal l => 1 + literal_size l
    | TE_Union ts => 1 + list_size ts
    | TE_Row rows => 1 + rows_size rows
    | TE_Fun params ret _ _ _ => 1 + rows_size params + size ret
    | TE_Overload fs => 1 + list_size fs
    | TE_Class _ members _ _ _ => 1 + rows_size members
    | TE_Module _ members => 1 + rows_size members
    | TE_Instance g args => 1 + size g + list_size args
    end
  with literal_size (l : LiteralValue) : nat :=
    match l with
    | L_Tuple ts => 1 + list_size ts
    | _ => 1
    end
  with list_size (ts : list TypeExpr) : nat :=
    match ts with
    | [] => 0
    | t::ts' => size t + list_size ts'
    end
  with rows_size (rows : Rows) : nat :=
    match rows with
    | [] => 0
    | (_, t)::rows' => 1 + size t + rows_size rows'
    end.

  (* ===== Row operations ===== *)
  
  Fixpoint row_lookup (rows : Rows) (k : FieldKey) : option TypeExpr :=
    match rows with
    | [] => None
    | (k', t)::rest => if key_matches k k' then Some t else row_lookup rest k
    end.
    
  Fixpoint row_has_key (rows : Rows) (k : FieldKey) : bool :=
    match row_lookup rows k with Some _ => true | None => false end.

  Fixpoint row_domain (rows : Rows) : list FieldKey :=
    match rows with
    | [] => []
    | (k, _)::rest => k :: row_domain rest
    end.

  (* ===== Type basics ===== *)
  
  Definition type_bot : TypeExpr := cast TE_Bot.
  Definition type_top : TypeExpr := cast TE_Top.

  Fixpoint type_eqb (t1 t2 : TypeExpr) : bool :=
    match uncast t1, uncast t2 with
    | TE_Bot, TE_Bot => true
    | TE_Top, TE_Top => true
    | TE_Any, TE_Any => true
    | TE_TVar x1 v1, TE_TVar x2 v2 => andb (Nat.eqb x1 x2) (Bool.eqb v1 v2)
    | TE_Ref s1, TE_Ref s2 => str_eqb s1 s2
    | _, _ => false
    end.

  Definition type_join (t1 t2 : TypeExpr) : TypeExpr :=
    match uncast t1, uncast t2 with
    | TE_Bot, _ => t2
    | _, TE_Bot => t1
    | TE_Top, _ | _, TE_Top => type_top
    | _, _ => 
        if type_eqb t1 t2 then t1 else cast (TE_Union [t1; t2])
    end.

  (* ===== Protocol Satisfaction ===== *)
  
  (* Check if type T satisfies protocol P *)
  (* T satisfies P if T has all members required by P with compatible types *)
  Fixpoint satisfies_protocol (t : TypeExpr) (proto : TypeExpr) : bool :=
    match uncast proto with
    | TE_Class _ proto_members _ true _ =>  (* is_protocol = true *)
        (* Get members of t *)
        let t_members := match uncast t with
                         | TE_Class _ members _ _ _ => members
                         | TE_Module _ members => members
                         | TE_Row rows => rows
                         | _ => []
                         end in
        (* Check all protocol members are satisfied *)
        forallb (fun '(pk, pt) =>
          match row_lookup t_members pk with
          | Some tt => 
              (* For methods, check function subtyping (contravariant params, covariant return) *)
              match uncast pt, uncast tt with
              | TE_Fun p_params p_ret _ _ _, TE_Fun t_params t_ret _ _ _ =>
                  (* Simplified: just check structural compatibility *)
                  andb (params_compatible t_params p_params) 
                       (type_is_subtype t_ret p_ret)
              | _, _ => type_is_subtype tt pt
              end
          | None => false  (* Missing required member *)
          end
        ) proto_members
    | _ => false  (* Not a protocol *)
    end
  
  with params_compatible (t_params p_params : Rows) : bool :=
    (* Parameters are contravariant: protocol params must be supertypes of type params *)
    forallb (fun '(pk, _) =>
      row_has_key t_params pk  (* Just check presence for simplicity *)
    ) p_params
  
  with type_is_subtype (t1 t2 : TypeExpr) : bool :=
    match uncast t1, uncast t2 with
    | _, TE_Top => true
    | TE_Bot, _ => true
    | TE_Any, _ | _, TE_Any => true
    | TE_Class _ _ _ true _, _ =>  (* t1 is protocol *)
        satisfies_protocol t2 t1
    | _, TE_Class _ _ _ true _ =>  (* t2 is protocol *)
        satisfies_protocol t1 t2
    | _, _ => type_eqb t1 t2
    end.

  (* ===== Method Binding ===== *)
  
  (* bind_self: When accessing a method as an attribute, bind the receiver *)
  Definition bind_self (method : TypeExpr) (receiver : TypeExpr) : TypeExpr :=
    match uncast method with
    | TE_Fun params ret eff is_prop tvars =>
        (* Remove first parameter (self) and mark as bound method *)
        let params_without_self := 
          match params with
          | [] => []
          | (FK_Pos 0, _)::rest => 
              (* Reindex remaining params: 1->0, 2->1, etc *)
              map (fun '(k, t) => 
                match k with
                | FK_Pos n => (FK_Pos (n - 1), t)
                | FK_Both n s => (FK_Both (n - 1) s, t)
                | _ => (k, t)
                end
              ) rest
          | _ => params  (* No self param *)
          end in
        cast (TE_Fun params_without_self ret 
                     {| se_new := se_new eff;
                        se_bound_method := true;  (* Mark as bound *)
                        se_update := se_update eff;
                        se_update_indices := se_update_indices eff;
                        se_points_to_args := se_points_to_args eff |}
                     is_prop tvars)
                     
    | TE_Overload methods =>
        (* Bind each overloaded method *)
        cast (TE_Overload (map (fun m => bind_self m receiver) methods))
        
    | _ => method  (* Not a method *)
    end.

  (* ===== Member Access with Binding ===== *)
  
  Definition subscr (base : TypeExpr) (attr : string) : TypeExpr :=
    let raw_member := 
      match uncast base with
      | TE_Row rows | TE_Class _ rows _ _ _ | TE_Module _ rows =>
          match row_lookup rows (FK_Name attr) with
          | Some t => t  
          | None => type_top
          end
      | TE_Union ts =>
          fold_left type_join (map (fun t => subscr t attr) ts) type_bot
      | _ => type_top
      end in
    (* If it's a method (function), bind self *)
    match uncast raw_member with
    | TE_Fun _ _ _ false _ =>  (* Not a property *)
        bind_self raw_member base
    | TE_Overload _ =>
        bind_self raw_member base
    | _ => raw_member
    end.

  (* ===== Two-stage Overload Resolution with Protocol Checking ===== *)

  (* 
     VARIADIC PARAMETERS - DOCUMENTATION:
     
     Variadic parameters (*args in Python) are complex to handle correctly because:
     1. They collect multiple positional arguments into a single parameter
     2. They can be partially filled across multiple applications  
     3. They interact with keyword arguments in complex ways
     4. They require special handling in unification to track collected vs remaining args
     
     For this implementation, we simplify by:
     - Not supporting true variadic parameters in the type system
     - Treating functions with *args as having flexible arity (handled at runtime)
     - This is adequate for the pointer analysis which doesn't need precise variadic tracking
     
     Full variadic support would require:
     - Star types (TE_Star) to represent packed argument sequences
     - Special unification rules for progressive collection
     - Tracking of "saturation points" for variadic parameters
  *)

  (* Stage 1: Filter overloads that match the argument pattern *)
  Definition filter_matching_overloads (overloads : list TypeExpr) (arg_types : list TypeExpr) : list TypeExpr :=
    let arg_rows := combine (map FK_Pos (seq 0 (length arg_types))) arg_types in
    filter (fun f =>
      match uncast f with
      | TE_Fun params _ _ _ _ =>
          (* Check if params are compatible with args *)
          (* Simplified: just check arity and basic compatibility *)
          andb (Nat.leb (length arg_rows) (length params))
               (forallb (fun '(k, at) =>
                  match row_lookup params k with
                  | Some pt => 
                      (* Check type compatibility or protocol satisfaction *)
                      orb (type_is_subtype at pt)
                          (satisfies_protocol at pt)
                  | None => false
                  end
                ) arg_rows)
      | _ => false
      end
    ) overloads.

  (* Stage 2: Apply matching overloads and join their return types *)  
  Definition resolve_overload (overloads : list TypeExpr) (arg_types : list TypeExpr) : TypeExpr :=
    let matching := filter_matching_overloads overloads arg_types in
    match matching with
    | [] => type_top  (* No matches *)
    | [single] => partial single arg_types
    | multiple => 
        (* Join return types of all applicable overloads *)
        fold_left type_join (map get_return multiple) type_bot
    end
  
  with partial (f : TypeExpr) (args : list TypeExpr) : TypeExpr :=
    match uncast f with
    | TE_Fun params ret _ _ _ =>
        (* Simple partial application - if all params satisfied, return ret *)
        if Nat.eqb (length args) (length params) then ret
        else if Nat.ltb (length args) (length params) then f  (* Return partially applied function *)
        else type_top  (* Too many args *)
    | TE_Overload fs =>
        resolve_overload fs args
    | _ => type_top
    end
  
  with get_return (t : TypeExpr) : TypeExpr :=
    match uncast t with
    | TE_Fun _ ret _ _ _ => ret
    | TE_Overload fs => fold_left type_join (map get_return fs) type_bot
    | _ => type_top
    end.

  (* ===== Rest of interface implementation ===== *)
  
  Definition subscr_index (base : TypeExpr) (idx : nat) : TypeExpr :=
    match uncast base with
    | TE_Row rows =>
        match row_lookup rows (FK_Pos idx) with
        | Some t => t
        | None => type_top
        end
    | _ => type_top
    end.
    
  Definition subscr_literal (base : TypeExpr) (c : ConstV) : TypeExpr :=
    match c with
    | KString s => subscr base s
    | KInt z => subscr_index base (Z.to_nat z)
    | _ => type_top
    end.

  Definition get_unop (t : TypeExpr) (op : string) : TypeExpr :=
    subscr t ("__" ++ op ++ "__").
    
  Definition partial_binop (left right : TypeExpr) (op : string) : TypeExpr :=
    let method := subscr left ("__" ++ op ++ "__") in
    partial method [right].

  Definition type_is_immutable (t : TypeExpr) : bool :=
    match uncast t with
    | TE_Literal _ => true
    | TE_Ref s => match s with
                  | "builtins.int" | "builtins.str" | "builtins.bool" => true
                  | _ => false
                  end
    | _ => false
    end.

  Definition type_is_callable (t : TypeExpr) : bool :=
    match uncast t with
    | TE_Fun _ _ _ _ _ | TE_Overload _ => true
    | _ => false
    end.

  Definition is_overloaded (t : TypeExpr) : bool :=
    match uncast t with TE_Overload _ => true | _ => false end.
    
  Definition is_property (t : TypeExpr) : bool :=
    match uncast t with TE_Fun _ _ _ true _ => true | _ => false end.
    
  Definition is_bound_method (t : TypeExpr) : bool :=
    match uncast t with  
    | TE_Fun _ _ eff _ _ => se_bound_method eff
    | TE_Overload fs => existsb is_bound_method fs
    | _ => false
    end.
    
  Definition any_new (t : TypeExpr) : bool :=
    match uncast t with
    | TE_Fun _ _ eff _ _ => se_new eff
    | TE_Overload fs => existsb any_new fs  
    | _ => false
    end.
    
  Definition all_new (t : TypeExpr) : bool :=
    match uncast t with
    | TE_Fun _ _ eff _ _ => se_new eff
    | TE_Overload fs => forallb all_new fs
    | _ => false
    end.
    
  Definition get_side_effect (t : TypeExpr) : SideEffect :=
    match uncast t with
    | TE_Fun _ _ eff _ _ => eff
    | TE_Overload fs =>
        (* Combine effects from all overloads *)
        fold_left (fun acc f =>
          let eff := get_side_effect f in
          {| se_new := orb (se_new acc) (se_new eff);
             se_bound_method := orb (se_bound_method acc) (se_bound_method eff);
             se_update := match se_update acc, se_update eff with
                         | Some u1, Some u2 => Some (type_join u1 u2)
                         | Some u, None | None, Some u => Some u
                         | None, None => None
                         end;
             se_update_indices := se_update_indices acc ++ se_update_indices eff;
             se_points_to_args := orb (se_points_to_args acc) (se_points_to_args eff) |}
        ) fs empty_effect
    | _ => empty_effect
    end.

  (* Effects and constructors *)
  Definition empty_effect : SideEffect := {|
    se_new := false;
    se_bound_method := false;
    se_update := None;
    se_update_indices := [];
    se_points_to_args := false
  |}.

  Definition make_list_constructor : TypeExpr :=
    cast (TE_Fun [] (cast (TE_Ref "builtins.list"))
                 {| se_new := true; se_bound_method := false;
                    se_update := None; se_update_indices := [];
                    se_points_to_args := true |} false []).
                    
  Definition make_tuple_constructor : TypeExpr := 
    cast (TE_Fun [] (cast (TE_Ref "builtins.tuple"))
                 {| se_new := true; se_bound_method := false;
                    se_update := None; se_update_indices := [];
                    se_points_to_args := true |} false []).
                    
  Definition make_dict_constructor : TypeExpr :=
    cast (TE_Fun [] (cast (TE_Ref "builtins.dict"))
                 {| se_new := true; se_bound_method := false;
                    se_update := None; se_update_indices := [];
                    se_points_to_args := false |} false []).
                    
  Definition make_set_constructor : TypeExpr :=
    cast (TE_Fun [] (cast (TE_Ref "builtins.set"))
                 {| se_new := true; se_bound_method := false;
                    se_update := None; se_update_indices := [];
                    se_points_to_args := false |} false []).
                    
  Definition make_slice_constructor : TypeExpr :=
    cast (TE_Fun [(FK_Pos 0, cast TE_Any); (FK_Pos 1, cast TE_Any)]
                 (cast (TE_Ref "builtins.slice"))
                 {| se_new := true; se_bound_method := false;
                    se_update := None; se_update_indices := [];
                    se_points_to_args := false |} false []).

  Definition literal_type (c : ConstV) : TypeExpr :=
    cast (TE_Literal (match c with
                      | KInt z => L_Int z
                      | KBool b => L_Bool b
                      | KString s => L_String s
                      | KNone => L_None
                      | KStopIter => L_None
                      end)).
                      
  Definition get_type_hash (t : TypeExpr) : nat := size t.

  (* Dunder operations *)
  Definition unop_to_method (op : UnOpTag) : string :=
    match op with
    | UNeg => "neg" | UPos => "pos" | UInvert => "invert" | UNot => "bool"
    end.
    
  Definition binop_to_method (op : BinOpTag) (inplace : bool) : string :=
    let base := match op with
    | BAdd => "add" | BSub => "sub" | BMul => "mul"
    | BTrueDiv => "truediv" | BFloorDiv => "floordiv" | BMod => "mod"
    | BMatMul => "matmul" | BAnd => "and" | BOr => "or"  
    | BXor => "xor" | BLShift => "lshift" | BRShift => "rshift"
    end in
    if inplace then "i" ++ base else base.
    
  Definition cmpop_to_method (op : CmpOpTag) : string :=
    match op with
    | CEq => "eq" | CNe => "ne" | CLt => "lt"
    | CLe => "le" | CGt => "gt" | CGe => "ge"
    | CIs | CIsNot => "is" | CIn | CNotIn => "contains"
    end.
    
  Definition dunder_lookup (info : DunderInfo) : TypeExpr :=
    match info with
    | TDUnOp op arg =>
        get_unop arg (unop_to_method op)
    | TDBinOp op lhs rhs inplace =>
        partial_binop lhs rhs (binop_to_method op inplace)
    | TDCmpOp op lhs rhs =>
        partial_binop lhs rhs (cmpop_to_method op)
    end.

End CompleteTypeSystem.