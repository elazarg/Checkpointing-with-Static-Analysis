From Coq Require Import String List Bool Arith ZArith PeanoNat.
From Coq Require Import Sets.Ensembles.

Set Implicit Arguments.
Import ListNotations.

Module TAC.

  (* ===== Basic Types ===== *)

  Definition StackVar := nat.

  Inductive FieldKey :=
  | FKPos  : nat -> FieldKey
  | FKName : string -> FieldKey
  | FKBoth : nat -> string -> FieldKey.

  Definition key_named (s : string) : FieldKey := FKName s.
  Definition key_pos (n : nat) : FieldKey := FKPos n.

  Inductive ConstV : Type :=
  | KInt      : Z -> ConstV
  | KBool     : bool -> ConstV
  | KString   : string -> ConstV
  | KNone     : ConstV
  | KStopIter : ConstV.

  (* ===== Split Object Model with Mutability Lattice ===== *)

  Inductive StaticID : Type :=
  | ObjFunc  : string -> StaticID
  | ObjClass : string -> StaticID
  | ObjConst : ConstV -> StaticID.

  Inductive HeapLoc : Type :=
  | Loc     : nat -> HeapLoc
  | Locals  : HeapLoc
  | Globals : HeapLoc.

  Inductive ObjRef : Type :=
  | StaticPtr : StaticID -> ObjRef
  | HeapPtr   : HeapLoc  -> ObjRef.

  (* ===== Memory Model and Effects ===== *)

  Definition StaticStore := StaticID -> FieldKey -> option StaticID.
  Definition Heap        := HeapLoc  -> FieldKey -> option ObjRef.

  Inductive EffLoc : Type :=
  | ExLoc : HeapLoc -> EffLoc
  | Fresh : nat     -> EffLoc.

  Definition EffWrite := (EffLoc * FieldKey * ObjRef)%type.
  Definition Effect   := list EffWrite.
  
    (* ===== Opaque operator tags (no Python names in IR) ===== *)
    Inductive UnOpTag  := UNeg | UPos | UInvert | UNot.
    Inductive BinOpTag := BAdd | BSub | BMul | BTrueDiv | BFloorDiv | BMod
                        | BMatMul | BAnd | BOr | BXor | BLShift | BRShift.
    Inductive CmpOpTag := CEq | CNe | CLt | CLe | CGt | CGe | CIs | CIsNot | CIn | CNotIn.
    Inductive Inplace  := Plain | Inplace.
    
    (* Expression-like dunder node (untyped; uses stack vars) *)
    Inductive Dunder :=
    | DUnOp  (op:UnOpTag)  (arg:StackVar)
    | DBinOp (op:BinOpTag) (lhs rhs:StackVar) (mode:Inplace)
    | DCmpOp (op:CmpOpTag) (lhs rhs:StackVar).
    
    (* Optional: a tag-only view for the oracle *)
    Inductive DunderTag :=
    | DTagUnOp  (op:UnOpTag)
    | DTagBinOp (op:BinOpTag) (mode:Inplace)
    | DTagCmpOp (op:CmpOpTag).
    
  (* ===== Instructions ===== *)

  Inductive Instruction : Type :=
  (* Simple Data Movement & Loading *)
  | IMov          : StackVar -> StackVar -> Instruction
  | ILoadConst    : StackVar -> ConstV -> Instruction
  | ILoadLocal    : StackVar -> string -> Instruction
  | ILoadGlobal   : StackVar -> string -> Instruction
  | ISetLocal     : string -> StackVar -> Instruction

  (* Method Resolution and Complex Operations *)
  | ILookupDunder       : StackVar -> Dunder -> Instruction
  | IResolveOverload    : StackVar -> StackVar -> StackVar -> StackVar -> Instruction
  | IResolveTupleCtor   : StackVar -> list StackVar -> Instruction
  | IResolveDictCtor    : StackVar -> list (StackVar * StackVar) -> Instruction
  | IGetAttr            : StackVar -> StackVar -> string -> Instruction
  | ISetAttr            : StackVar -> string -> StackVar -> Instruction
  | IUnpack             : list StackVar -> StackVar -> Instruction

  (* Function Calls *)
  | ICall         : StackVar -> StackVar -> Instruction

  (* Control Flow *)
  | IAssumeValue  : StackVar -> ConstV -> Instruction
  | IExit         : Instruction.

  (* ===== Axiomatized Python Semantics ===== *)

  Section PythonSemantics.
    Variable σ : StaticStore.

    (* Pure operations returning a static object *)
    Axiom get_object_class : forall (obj: ObjRef), StaticID.
    Axiom dunder_lookup_tag : forall (tag: DunderTag) (classes: list StaticID), option StaticID.
    Axiom resolve_overload : forall (h: Heap) (func:ObjRef) (args:ObjRef) (kwargs:ObjRef), option StaticID.
    Axiom resolve_tuple_constructor : forall (h: Heap) (elems: list ObjRef), option StaticID.
    Axiom resolve_dict_constructor  : forall (h: Heap) (pairs: list (ObjRef * ObjRef)), option StaticID.

    (* Heap-reading/writing operations *)
    Axiom attribute_lookup : forall (h: Heap) (obj: ObjRef) (name: string), option ObjRef.
    Axiom attribute_assign : forall (h: Heap) (obj: ObjRef) (name: string) (val: ObjRef), option Heap.

    (* Effectful operations that may allocate memory *)
    Axiom apply_function : forall (h: Heap) (func: StaticID), option (ObjRef * Effect).
    Axiom unpack_iterable : forall (h: Heap) (obj: ObjRef) (n: nat), option (list ObjRef * Effect).

  End PythonSemantics.

  (* ===== Operational Semantics ===== *)

  Module Semantics.
    Parameter σ : StaticStore.

    Record State := {
      stack : StackVar -> option ObjRef;
      heap  : Heap
    }.

    Definition StackEnv := StackVar -> option ObjRef.

    (* Helper for comparing field keys, needed by update_heap *)
    Definition field_key_eqb (k1 k2 : FieldKey) : bool :=
      match k1, k2 with
      | FKPos n1,        FKPos n2        => Nat.eqb n1 n2
      | FKName s1,       FKName s2       => String.eqb s1 s2
      | FKBoth n1 s1,    FKBoth n2 s2    => andb (Nat.eqb n1 n2) (String.eqb s1 s2)
      | _, _ => false
      end.

    (* Helper for performing a functional update on the heap *)
    Definition update_heap (h : Heap) (obj : HeapLoc) (k : FieldKey)
                           (val : ObjRef) : Heap :=
      fun o k' =>
        if match o, obj with
           | Loc n1, Loc n2 => Nat.eqb n1 n2
           | Locals, Locals => true
           | Globals, Globals => true
           | _, _ => false
           end
        then if field_key_eqb k k' then Some val else h o k'
        else h o k'.

    (* Helper for looking up values from either store *)
    Definition memory_get (h : Heap) (obj : ObjRef) (k : FieldKey) : option ObjRef :=
      match obj with
      | StaticPtr sid =>
          match σ sid k with
          | Some sid' => Some (StaticPtr sid')
          | None => None
          end
      | HeapPtr hid => h hid k
      end.

    Definition update_stack (stk : StackEnv) (n : StackVar) (obj : ObjRef) : StackEnv :=
      fun m => if Nat.eq_dec n m then Some obj else stk m.

    Fixpoint update_stack_multi (stk: StackEnv) (vars: list StackVar) (objs: list ObjRef) : StackEnv :=
      match vars, objs with
      | v :: vs, o :: os => update_stack_multi (update_stack stk v o) vs os
      | _, _ => stk
      end.

    (* --- Effect Realization Logic --- *)

    Definition dom (h : Heap) : Ensemble nat :=
      fun n => exists k v, h (Loc n) k = Some v.

    Record FreshInjection (h : Heap) (fresh_indices : list nat) (ι : nat -> nat) := {
      finj_injective :
        forall i j, List.In i fresh_indices -> List.In j fresh_indices ->
                    ι i = ι j -> i = j;
      finj_fresh :
        forall i, List.In i fresh_indices ->
                  ~(Ensembles.In nat (dom h) (ι i))
    }.

    Definition realize_loc (ι : nat -> nat) (loc : EffLoc) : HeapLoc :=
      match loc with
      | ExLoc hid => hid
      | Fresh i => Loc (ι i)
      end.

    Definition apply_effect_write (h : Heap) (ι : nat -> nat)
                                  (w : EffWrite) : Heap :=
      match w with
      | (loc, k, val) => update_heap h (realize_loc ι loc) k val
      end.

    Fixpoint apply_effects (h : Heap) (ι : nat -> nat) (eff : Effect) : Heap :=
      match eff with
      | [] => h
      | w :: rest => apply_effects (apply_effect_write h ι w) ι rest
      end.

    Fixpoint fresh_indices (eff : Effect) : list nat :=
      match eff with
      | [] => []
      | (ExLoc _, _, _) :: r => fresh_indices r
      | (Fresh i, _, _) :: r => i :: fresh_indices r
      end.

    (* --- Execution Rules --- *)

    Inductive exec : State -> Instruction -> State -> Prop :=

    | ExecMov : forall s dst src obj,
        s.(stack) src = Some obj ->
        exec s (IMov dst src)
             {| stack := update_stack s.(stack) dst obj; heap := s.(heap) |}

    | ExecLoadConst : forall s dst k,
        exec s (ILoadConst dst k)
             {| stack := update_stack s.(stack) dst (StaticPtr (ObjConst k)); heap := s.(heap) |}

    | ExecLoadLocal : forall s dst varname obj,
        memory_get s.(heap) (HeapPtr Locals) (key_named varname) = Some obj ->
        exec s (ILoadLocal dst varname)
             {| stack := update_stack s.(stack) dst obj; heap := s.(heap) |}

    | ExecLoadGlobal : forall s dst varname obj,
        memory_get s.(heap) (HeapPtr Globals) (key_named varname) = Some obj ->
        exec s (ILoadGlobal dst varname)
             {| stack := update_stack s.(stack) dst obj; heap := s.(heap) |}

    | ExecSetLocal : forall s varname src obj,
        s.(stack) src = Some obj ->
        let h' := update_heap s.(heap) Locals (key_named varname) obj in
        exec s (ISetLocal varname src)
             {| stack := s.(stack); heap := h' |}

    | ExecLookup : forall s dst e method,
        (match e with
         | DUnOp op a =>
             exists obj cls,
               s.(stack) a = Some obj /\
               get_object_class obj = cls /\
               dunder_lookup_tag (DTagUnOp op) [cls] = Some method
         | DBinOp op l r mode =>
             exists o1 o2 c1 c2,
               s.(stack) l = Some o1 /\
               s.(stack) r = Some o2 /\
               get_object_class o1 = c1 /\
               get_object_class o2 = c2 /\
               dunder_lookup_tag (DTagBinOp op mode) [c1; c2] = Some method
         | DCmpOp op l r =>
             exists o1 o2 c1 c2,
               s.(stack) l = Some o1 /\
               s.(stack) r = Some o2 /\
               get_object_class o1 = c1 /\
               get_object_class o2 = c2 /\
               dunder_lookup_tag (DTagCmpOp op) [c1; c2] = Some method
         end) ->
        exec s (ILookup dst e)
             {| stack := update_stack s.(stack) dst (StaticPtr method);
                heap  := s.(heap) |}
    

    | ExecResolveOverload : forall s dst func_sv args_sv kwargs_sv func_obj args_obj kwargs_obj bound_func,
        s.(stack) func_sv = Some func_obj ->
        s.(stack) args_sv = Some args_obj ->
        s.(stack) kwargs_sv = Some kwargs_obj ->
        resolve_overload s.(heap) func_obj args_obj kwargs_obj = Some bound_func ->
        exec s (IResolveOverload dst func_sv args_sv kwargs_sv)
             {| stack := update_stack s.(stack) dst (StaticPtr bound_func); heap := s.(heap) |}

    | ExecResolveTupleCtor : forall s dst items item_objs bound_func,
        map (fun n => s.(stack) n) items = map (@Some ObjRef) item_objs ->
        resolve_tuple_constructor s.(heap) item_objs = Some bound_func ->
        exec s (IResolveTupleCtor dst items)
             {| stack := update_stack s.(stack) dst (StaticPtr bound_func); heap := s.(heap) |}

    | ExecResolveDictCtor : forall s dst items key_objs val_objs kv_pairs bound_func,
        map (fun '(k,_) => s.(stack) k) items = map (@Some ObjRef) key_objs ->
        map (fun '(_,v) => s.(stack) v) items = map (@Some ObjRef) val_objs ->
        List.combine key_objs val_objs = kv_pairs ->
        resolve_dict_constructor s.(heap) kv_pairs = Some bound_func ->
        exec s (IResolveDictCtor dst items)
             {| stack := update_stack s.(stack) dst (StaticPtr bound_func); heap := s.(heap) |}

    | ExecGetAttr : forall s dst obj_sv attr obj result,
        s.(stack) obj_sv = Some obj ->
        attribute_lookup s.(heap) obj attr = Some result ->
        exec s (IGetAttr dst obj_sv attr)
             {| stack := update_stack s.(stack) dst result; heap := s.(heap) |}

    | ExecSetAttr : forall s obj_sv attr val_sv obj val h',
        s.(stack) obj_sv = Some obj ->
        s.(stack) val_sv = Some val ->
        attribute_assign s.(heap) obj attr val = Some h' ->
        exec s (ISetAttr obj_sv attr val_sv)
             {| stack := s.(stack); heap := h' |}

    | ExecUnpack : forall s vars src_sv src_obj objs eff ι h',
        s.(stack) src_sv = Some src_obj ->
        unpack_iterable s.(heap) src_obj (length vars) = Some (objs, eff) ->
        length vars = length objs ->
        FreshInjection s.(heap) (fresh_indices eff) ι ->
        h' = apply_effects s.(heap) ι eff ->
        let stk' := update_stack_multi s.(stack) vars objs in
        exec s (IUnpack vars src_sv)
             {| stack := stk'; heap := h' |}

    | ExecCall : forall s dst func_sv func_sid res eff ι h',
        s.(stack) func_sv = Some (StaticPtr func_sid) ->
        apply_function s.(heap) func_sid = Some (res, eff) ->
        FreshInjection s.(heap) (fresh_indices eff) ι ->
        h' = apply_effects s.(heap) ι eff ->
        exec s (ICall dst func_sv)
             {| stack := update_stack s.(stack) dst res; heap := h' |}

    | ExecAssumeValue : forall s x k,
        s.(stack) x = Some (StaticPtr (ObjConst k)) ->
        exec s (IAssumeValue x k) s

    | ExecExit : forall s,
        exec s IExit s.

  End Semantics.

End TAC.
