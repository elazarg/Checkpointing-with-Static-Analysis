(******************************************************************************)
(*                                                                            *)
(*  Lowering.v                                                                *)
(*                                                                            *)
(*  Purpose: A readable COQ specification of the source-to-source lowering    *)
(*  from CPython bytecode (as per Python 3.12 'dis' prose) to our TAC IR.     *)
(*                                                                            *)
(*  This file is for scrutiny/communication, not for execution or proofs.     *)
(*  We rely on axioms (stack-shape, KW decoding, etc.) to keep the mapping    *)
(*  focused on semantics. The core change versus prior versions: all unary,   *)
(*  binary (incl. inplace), and comparison/membership/identity operations     *)
(*  lower through ILookupDunder with opaque tags (no Python names).           *)
(*                                                                            *)
(******************************************************************************)

From Coq Require Import String List.
Import ListNotations.
Local Open Scope string_scope.

Require Import IR.
Require Import cpython_bytecode_coq.

Module Lowering.
  Module B := CPythonBytecode.
  Module T := TAC.
  
  (**************************************************************************)
  (** Scope and axiomatized front-end facts                                 *)
  (**************************************************************************)

  (* Scope: intraprocedural blocks; CFG/joins/exceptions handled elsewhere.
     No exceptions/generators/async/closures/dynamic class/function creation.
     Star-calls must be pre-desugared (see Unsupported). *)

  Definition StackVar := T.StackVar.

  Axiom dest_of      : B.Instruction -> StackVar.
  Axiom args_of      : B.Instruction -> list StackVar.
  Axiom name_of      : B.Instruction -> string.
  Axiom fresh_tmp    : B.Instruction -> StackVar.
  Axiom kw_pairs_of  : B.Instruction -> list (StackVar * StackVar).
  Axiom unpack_dests_of : B.Instruction -> list StackVar.
  Axiom const_key_map_args : B.Instruction -> (list StackVar (*keys*), list StackVar (*vals*)).

  (**************************************************************************)
  (** Mapping CPython opcode enums to opaque IR tags                         *)
  (**************************************************************************)

  (* Unaries *)
  Definition lower_unop (u : B.UnOpType) : T.UnOpTag :=
    match u with
    | B.UNegative => T.UNeg
    | B.UPositive => T.UPos
    | B.UInvert   => T.UInvert
    | B.UNot      => T.UNot
    end.

  (* Binary core op tag (ignores inplace bit) *)
  Definition lower_binop_tag (b : B.BinOpType) : T.BinOpTag :=
    match b with
    | B.BAdd | B.BInplaceAdd => T.BAdd
    | B.BSub | B.BInplaceSub => T.BSub
    | B.BMul | B.BInplaceMul => T.BMul
    | B.BTrueDiv | B.BInplaceTrueDiv => T.BTrueDiv
    | B.BFloorDiv | B.BInplaceFloorDiv => T.BFloorDiv
    | B.BMod | B.BInplaceMod => T.BMod
    | B.BMatMul | B.BInplaceMatMul => T.BMatMul
    | B.BAnd | B.BInplaceAnd => T.BAnd
    | B.BOr | B.BInplaceOr => T.BOr
    | B.BXor | B.BInplaceXor => T.BXor
    | B.BLShift | B.BInplaceLShift => T.BLShift
    | B.BRShift | B.BInplaceRShift => T.BRShift
    end.

  (* Inplace flag *)
  Definition lower_inplace (b : B.BinOpType) : T.Inplace :=
    match b with
    | B.BInplaceAdd | B.BInplaceSub | B.BInplaceMul
    | B.BInplaceTrueDiv | B.BInplaceFloorDiv | B.BInplaceMod
    | B.BInplaceMatMul | B.BInplaceAnd | B.BInplaceOr
    | B.BInplaceXor | B.BInplaceLShift | B.BInplaceRShift => T.Inplace
    | _ => T.Plain
    end.

  (* Rich comparisons *)
  Definition lower_cmp (c : B.CmpOpType) : T.CmpOpTag :=
    match c with
    | B.CEq => T.CEq | B.CNe => T.CNe
    | B.CLt => T.CLt | B.CLe => T.CLe
    | B.CGt => T.CGt | B.CGe => T.CGe
    end.

  (* Identity *)
  Definition lower_is (invert: bool) : T.CmpOpTag :=
    if invert then T.CIsNot else T.CIs.

  (* Containment *)
  Definition lower_contains (invert: bool) : T.CmpOpTag :=
    if invert then T.CNotIn else T.CIn.

  (**************************************************************************)
  (** Small TAC idiom helpers                                                *)
  (**************************************************************************)

  Definition Args (dst : StackVar) (vs : list StackVar) : T.Instruction :=
    T.IConstructTuple dst vs.
  Definition Kw (dst : StackVar) (kvs : list (StackVar * StackVar)) : T.Instruction :=
    T.IConstructDict dst kvs.
  Definition Bind (dst f a k : StackVar) : T.Instruction := T.IBind dst f a k.
  Definition Call (dst b : StackVar) : T.Instruction := T.ICall dst b.

  Fixpoint pair_up (xs : list StackVar) : list (StackVar * StackVar) :=
    match xs with
    | k :: v :: tl => (k,v) :: pair_up tl
    | _ => []
    end.

  (** Attribute-based call: getattr → args/kwargs → bind → call *)
  Definition AttrCall
             (dst obj : StackVar) (attr : string)
             (pos : list StackVar) (kws : list (StackVar*StackVar))
             (i   : B.Instruction) : list T.Instruction :=
    let m  := fresh_tmp i in
    let ta := fresh_tmp i in
    let tk := fresh_tmp i in
    let b  := fresh_tmp i in
    [ T.IGetAttr m obj attr
    ; Args ta pos
    ; Kw   tk kws
    ; Bind b  m  ta  tk
    ; Call dst b
    ].

  (** Dunder-based call: ILookupDunder(tagged) → args/kwargs → bind → call *)
  Definition DunderCall
             (dst : StackVar) (d : T.Dunder)
             (i   : B.Instruction) : list T.Instruction :=
    let m  := fresh_tmp i in
    let ta := fresh_tmp i in
    let tk := fresh_tmp i in
    let b  := fresh_tmp i in
    let pos :=
      match d with
      | T.DUnOp _ a         => [a]
      | T.DBinOp _ l r _    => [l; r]
      | T.DCmpOp _ l r      => [l; r]
      end in
    [ T.ILookupDunder m d
    ; Args ta pos
    ; Kw   tk []
    ; Bind b  m  ta  tk
    ; Call dst b
    ].

  (** Build a slice object via builtin 'slice'. *)
  Definition BuildSlice (dst : StackVar) (svs : list StackVar) (i : B.Instruction)
    : list T.Instruction :=
    let f  := fresh_tmp i in
    let ta := fresh_tmp i in
    let tk := fresh_tmp i in
    let b  := fresh_tmp i in
    [ T.ILoadGlobal f "slice"
    ; Args          ta svs
    ; Kw            tk []
    ; Bind          b  f  ta  tk
    ; Call          dst b
    ].

  (**************************************************************************)
  (** The lowering itself                                                    *)
  (**************************************************************************)

  Definition lower_instruction (i : B.Instruction) : list T.Instruction :=
    match i with

    (* ======================== A. Data movement / names ==================== *)
    | B.POP_TOP => []
    | B.COPY _ =>
        match args_of i with a :: _ => [ T.IMov (dest_of i) a ] | _ => [] end
    | B.SWAP _ =>
        match args_of i with
        | a :: b :: _ =>
            let t := fresh_tmp i in [ T.IMov t a ; T.IMov a b ; T.IMov b t ]
        | _ => []
        end
    | B.NOP | B.CACHE | B.END_FOR | B.END_SEND => []
    | B.LOAD_CONST c => [ T.ILoadConst (dest_of i) c ]
    | B.LOAD_FAST _ | B.LOAD_FAST_CHECK _ => [ T.ILoadLocal (dest_of i) (name_of i) ]
    | B.STORE_FAST _ =>
        match args_of i with a :: _ => [ T.ISetLocal (name_of i) a ] | _ => [] end
    | B.LOAD_GLOBAL _ => [ T.ILoadGlobal (dest_of i) (name_of i) ]
    | B.LOAD_NAME _   => [ T.ILoadLocal  (dest_of i) (name_of i) ]
    | B.STORE_NAME _  =>
        match args_of i with a :: _ => [ T.ISetLocal (name_of i) a ] | _ => [] end

    (* ============================= B. Attributes ========================== *)
    | B.LOAD_ATTR _ =>
        match args_of i with o :: _ => [ T.IGetAttr (dest_of i) o (name_of i) ] | _ => [] end
    | B.STORE_ATTR _ =>
        match args_of i with o :: v :: _ => [ T.ISetAttr o (name_of i) v ] | _ => [] end

    (* ========================== C. Unary operations ======================= *)
    | B.UNARY_NEGATIVE =>
        match args_of i with
        | x :: _ => DunderCall (dest_of i) (T.DUnOp (lower_unop B.UNegative) x) i
        | _ => []
        end
    | B.UNARY_POSITIVE =>
        match args_of i with
        | x :: _ => DunderCall (dest_of i) (T.DUnOp (lower_unop B.UPositive) x) i
        | _ => []
        end
    | B.UNARY_NOT =>
        match args_of i with
        | x :: _ => DunderCall (dest_of i) (T.DUnOp (lower_unop B.UNot) x) i
        | _ => []
        end
    | B.UNARY_INVERT =>
        match args_of i with
        | x :: _ => DunderCall (dest_of i) (T.DUnOp (lower_unop B.UInvert) x) i
        | _ => []
        end

    (* ================== D. Binary (incl. in-place) operations ============= *)
    | B.BINARY_OP bop =>
        match args_of i with
        | l :: r :: _ =>
            DunderCall (dest_of i) (T.DBinOp (lower_binop_tag bop) l r (lower_inplace bop)) i
        | _ => []
        end

    (* ====== E. Comparisons / identity / containment via DCmpOp tags ====== *)
    | B.COMPARE_OP cop =>
        match args_of i with
        | l :: r :: _ => DunderCall (dest_of i) (T.DCmpOp (lower_cmp cop) l r) i
        | _ => []
        end
    | B.IS_OP invert =>
        match args_of i with
        | l :: r :: _ => DunderCall (dest_of i) (T.DCmpOp (lower_is invert) l r) i
        | _ => []
        end
    | B.CONTAINS_OP invert =>
        (* x in y => DCmpOp CIn x y (no manual swapping; oracle decides). *)
        match args_of i with
        | x :: y :: _ => DunderCall (dest_of i) (T.DCmpOp (lower_contains invert) x y) i
        | _ => []
        end

    (* =================== F. Subscription and slicing (attrs) ============== *)
    | B.BINARY_SUBSCR =>
        (* obj[key] via __getitem__ *)
        match args_of i with
        | obj :: key :: _ => AttrCall (dest_of i) obj "__getitem__" [key] [] i
        | _ => []
        end
        
    (* STORE_SUBSCR *)
    | B.STORE_SUBSCR =>
      match args_of i with
      | obj :: key :: value :: _ =>
          AttrCall (fresh_tmp i) obj "__setitem__" [key; value] [] i
      | _ => []
      end
    
    (* BINARY_SLICE *)
    | B.BINARY_SLICE =>
      match args_of i with
      | obj :: start :: stop :: _ =>
          let s := fresh_tmp i in
          BuildSlice s [start; stop] i ++ AttrCall (dest_of i) obj "__getitem__" [s] [] i
      | _ => []
      end
    
    (* STORE_SLICE *)
    | B.STORE_SLICE =>
      match args_of i with
      | obj :: start :: stop :: value :: _ =>
          let s := fresh_tmp i in
          BuildSlice s [start; stop] i ++ AttrCall (fresh_tmp i) obj "__setitem__" [s; value] [] i
      | _ => []
      end
        

    (* ================== G. Tuple/dict constructors (asymmetric) =========== *)
    | B.BUILD_TUPLE _ => T.IConstructTuple (dest_of i) (args_of i) :: nil
    | B.BUILD_MAP _   => T.IConstructDict (dest_of i) (pair_up (args_of i)) :: nil
    | B.BUILD_CONST_KEY_MAP _ =>
        let '(ks,vs) := const_key_map_args i in T.IConstructDict (dest_of i) (combine ks vs) :: nil

    (* ==================== H. List / set via builtin calls ================= *)
    | B.BUILD_LIST _ =>
        let t := fresh_tmp i in
        let f := fresh_tmp i in
        let ta := fresh_tmp i in
        let tk := fresh_tmp i in
        let b := fresh_tmp i in
        [ T.IConstructTuple t (args_of i)
        ; T.ILoadGlobal     f "list"
        ; Args              ta [t]
        ; Kw                tk []
        ; Bind              b  f  ta  tk
        ; Call              (dest_of i) b
        ]
    | B.BUILD_SET _ =>
        let t := fresh_tmp i in
        let f := fresh_tmp i in
        let ta := fresh_tmp i in
        let tk := fresh_tmp i in
        let b := fresh_tmp i in
        [ T.IConstructTuple t (args_of i)
        ; T.ILoadGlobal     f "set"
        ; Args              ta [t]
        ; Kw                tk []
        ; Bind              b  f  ta  tk
        ; Call              (dest_of i) b
        ]

    (* ================================ I. Unpack =========================== *)
    | B.UNPACK_SEQUENCE _ =>
        let ds := unpack_dests_of i in
        match args_of i with s :: _ => [ T.IUnpack ds s ] | _ => [] end

    (* ============================= J. BUILD_SLICE ========================= *)
    | B.BUILD_SLICE _ => BuildSlice (dest_of i) (args_of i) i

    (* ============================== K. CALL =============================== *)
    | B.CALL _ =>
        (* CALL uses preceding KW_NAMES; we assume kw_pairs_of has decoded them. *)
        match args_of i with
        | f :: pos =>
            let ta := fresh_tmp i in
            let tk := fresh_tmp i in
            let b  := fresh_tmp i in
            let f' := fresh_tmp i in
            [ Args ta pos
            ; Kw   tk (kw_pairs_of i)
            ; T.ILookupOverload f' f ta tk  (* callee selection only *)
            ; Bind b  f' ta tk
            ; Call (dest_of i) b
            ]
        | _ => []
        end
    | B.KW_NAMES _ => []
    | B.PUSH_NULL  => []

    (* ======= L. Iteration protocol (optional; StopIteration via CFG) ====== *)
    | B.GET_ITER =>
        match args_of i with
        | o :: _ => AttrCall (dest_of i) o "__iter__" [] [] i
        | _ => []
        end
    | B.FOR_ITER _ =>
        match args_of i with
        | it :: _ => AttrCall (dest_of i) it "__next__" [] [] i
        | _ => []
        end

    (* ========================= M. Control/termination ===================== *)
    | B.JUMP_FORWARD _ | B.JUMP_BACKWARD _ | B.JUMP_BACKWARD_NO_INTERRUPT _
    | B.POP_JUMP_IF_TRUE _ | B.POP_JUMP_IF_FALSE _
    | B.POP_JUMP_IF_NOT_NONE _ | B.POP_JUMP_IF_NONE _ => []
    | B.RETURN_VALUE | B.RAISE_VARARGS _ => [ T.IExit ]

    (* ===================================================================== *)
    (* Unsupported groups (explicitly documented)                             *)
    (* ===================================================================== *)

    | B.STORE_GLOBAL _ =>
        (* Rationale: TAC currently lacks ISetGlobal; modeling global mutation
           is out of scope. Could be added analogously to ISetLocal. *)
        []

    | B.DELETE_FAST _ | B.DELETE_NAME _ | B.DELETE_GLOBAL _ | B.DELETE_SUBSCR =>
        (* Rationale: 'del' operations remove bindings or entries; TAC provides
           no deletion primitive. A future extension could lower to __delitem__
           calls (for subscr) and heap updates that remove fields. *)
        []

    | B.GET_YIELD_FROM_ITER | B.GET_AWAITABLE _ | B.GET_AITER | B.GET_ANEXT
    | B.END_ASYNC_FOR | B.CLEANUP_THROW | B.BEFORE_ASYNC_WITH
    | B.YIELD_VALUE | B.RETURN_GENERATOR | B.SEND _ =>
        (* Rationale: Generators/coroutines/async are outside our intraprocedural,
           exception-free scope. *)
        []

    | B.MAKE_FUNCTION _ | B.LOAD_BUILD_CLASS =>
        (* Rationale: Function/class creation at runtime is unsupported; the
           static store in TAC models immutable functions/classes. *)
        []

    | B.POP_EXCEPT | B.RERAISE _ | B.PUSH_EXC_INFO | B.CHECK_EXC_MATCH
    | B.CHECK_EG_MATCH | B.WITH_EXCEPT_START | B.LOAD_ASSERTION_ERROR | B.BEFORE_WITH =>
        (* Rationale: Exceptions are not modeled; we follow 'happy path only'. *)
        []

    | B.GET_LEN | B.MATCH_MAPPING | B.MATCH_SEQUENCE | B.MATCH_KEYS | B.MATCH_CLASS _ =>
        (* Rationale: Structural pattern matching opcodes are not lowered here; the
           translation would need explicit control and guards. *)
        []

    | B.SETUP_ANNOTATIONS =>
        (* Rationale: Runtime manipulation of __annotations__ is out of scope. *)
        []

    | B.MAKE_CELL _ | B.LOAD_CLOSURE _ | B.LOAD_DEREF _ | B.LOAD_FROM_DICT_OR_DEREF _
    | B.STORE_DEREF _ | B.DELETE_DEREF _ | B.COPY_FREE_VARS _ =>
        (* Rationale: Closures/cell variables and their indirections are not modeled.
           Our IR assumes no closures for numerical code. *)
        []

    | B.EXTENDED_ARG _ | B.RESUME _ =>
        (* Rationale: Interpreter-level prefixes/tracing; no lowering effect. *)
        []

    | B.FORMAT_VALUE _ | B.BUILD_STRING _ =>
        (* Rationale: f-string formatting and optimized string ops are modeled
           as runtime calls in the type/pointer analyses, not specialized in TAC. *)
        []

    | B.LOAD_LOCALS | B.LOAD_FROM_DICT_OR_GLOBALS _ =>
        (* Rationale: direct locals dict access and annotation scopes are not modeled. *)
        []

    | B.CALL_FUNCTION_EX _ =>
        (* Rationale: star-args/kwargs call. We do not synthesize the star-merge
           of positional/keyword collections at lowering time. A front-end desugaring
           could translate this to explicit tuple/dict construction plus CALL. *)
        []

    end.

  Definition lower_block (code : list B.Instruction) : list T.Instruction :=
    List.concat (List.map lower_instruction code).

  (**************************************************************************)
  (** Informal adequacy notes                                                *)
  (**************************************************************************)

  (*
    - All unary/binary/compare/identity/membership opcodes are routed through
      ILookupDunder with opaque tags and explicit argument tuples [self] / [l;r],
      preserving purity of lookup and separating binding/invocation.
    - Subscription/slicing remain via attribute protocol (__getitem__/__setitem__)
      because they are not covered by Dunder tags.
    - Tuple/dict literals are direct constructors (asymmetric handling).
      List/set go through builtin calls for uniformity with general calls.
    - CALL lowers to LookupOverload→Bind→Call with a pre-decoded KW mapping.
    - GET_ITER/FOR_ITER lower to __iter__/__next__; loop exits via CFG guards.
    - Unsupported groups are explicitly listed (exceptions, closures, star-calls,
      dynamic function/class creation, pattern matching, etc.).
  *)

End Lowering.
