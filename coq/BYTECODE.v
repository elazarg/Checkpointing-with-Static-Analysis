(*
  Bytecode.v
  Stub for CPython bytecode definitions
*)

From Stdlib Require Import String List ZArith.
Import ListNotations.

Module Bytecode.

  Inductive UnOpType := UNegative | UPositive | UInvert | UNot.
  
  Inductive BinOpType := 
    | BAdd | BSub | BMul | BTrueDiv | BFloorDiv | BMod | BMatMul
    | BAnd | BOr | BXor | BLShift | BRShift
    | BInplaceAdd | BInplaceSub | BInplaceMul | BInplaceTrueDiv
    | BInplaceFloorDiv | BInplaceMod | BInplaceMatMul
    | BInplaceAnd | BInplaceOr | BInplaceXor 
    | BInplaceLShift | BInplaceRShift.
  
  Inductive CmpOpType := CEq | CNe | CLt | CLe | CGt | CGe.
  
  Inductive Instruction :=
    (* Data movement *)
    | POP_TOP | COPY (n:nat) | SWAP (n:nat) | NOP | CACHE
    | END_FOR | END_SEND | LOAD_CONST (c:Z)
    | LOAD_FAST (n:nat) | LOAD_FAST_CHECK (n:nat)
    | STORE_FAST (n:nat) | LOAD_GLOBAL (s:string)
    | LOAD_NAME (s:string) | STORE_NAME (s:string)
    | STORE_GLOBAL (s:string)
    
    (* Attributes *)
    | LOAD_ATTR (s:string) | STORE_ATTR (s:string)
    
    (* Unary/Binary/Compare *)
    | UNARY_NEGATIVE | UNARY_POSITIVE | UNARY_NOT | UNARY_INVERT
    | BINARY_OP (op:BinOpType)
    | COMPARE_OP (op:CmpOpType)
    | IS_OP (invert:bool)
    | CONTAINS_OP (invert:bool)
    
    (* Subscript/Slice *)
    | BINARY_SUBSCR | STORE_SUBSCR
    | BINARY_SLICE | STORE_SLICE
    | BUILD_SLICE (n:nat)
    
    (* Collections *)
    | BUILD_TUPLE (n:nat) | BUILD_LIST (n:nat)
    | BUILD_MAP (n:nat) | BUILD_SET (n:nat)
    | BUILD_CONST_KEY_MAP (n:nat)
    | UNPACK_SEQUENCE (n:nat)
    
    (* Calls *)
    | CALL (n:nat) | KW_NAMES (s:string) | PUSH_NULL
    | CALL_FUNCTION_EX (flags:nat)
    
    (* Iteration *)
    | GET_ITER | FOR_ITER (target:nat)
    
    (* Control flow *)
    | JUMP_FORWARD (n:nat) | JUMP_BACKWARD (n:nat)
    | JUMP_BACKWARD_NO_INTERRUPT (n:nat)
    | POP_JUMP_IF_TRUE (n:nat) | POP_JUMP_IF_FALSE (n:nat)
    | POP_JUMP_IF_NOT_NONE (n:nat) | POP_JUMP_IF_NONE (n:nat)
    | RETURN_VALUE | RAISE_VARARGS (n:nat)
    
    (* Delete operations *)
    | DELETE_FAST (n:nat) | DELETE_NAME (s:string)
    | DELETE_GLOBAL (s:string) | DELETE_SUBSCR
    
    (* Generators/Async *)
    | GET_YIELD_FROM_ITER | GET_AWAITABLE (n:nat)
    | GET_AITER | GET_ANEXT | END_ASYNC_FOR
    | CLEANUP_THROW | BEFORE_ASYNC_WITH
    | YIELD_VALUE | RETURN_GENERATOR | SEND (n:nat)
    
    (* Function/Class creation *)
    | MAKE_FUNCTION (flags:nat) | LOAD_BUILD_CLASS
    
    (* Exceptions *)
    | POP_EXCEPT | RERAISE (n:nat) | PUSH_EXC_INFO
    | CHECK_EXC_MATCH | CHECK_EG_MATCH
    | WITH_EXCEPT_START | LOAD_ASSERTION_ERROR | BEFORE_WITH
    
    (* Pattern matching *)
    | GET_LEN | MATCH_MAPPING | MATCH_SEQUENCE
    | MATCH_KEYS | MATCH_CLASS (n:nat)
    
    (* Misc *)
    | SETUP_ANNOTATIONS
    | MAKE_CELL (n:nat) | LOAD_CLOSURE (n:nat)
    | LOAD_DEREF (n:nat) | LOAD_FROM_DICT_OR_DEREF (n:nat)
    | STORE_DEREF (n:nat) | DELETE_DEREF (n:nat) | COPY_FREE_VARS (n:nat)
    | EXTENDED_ARG (n:nat) | RESUME (n:nat)
    | FORMAT_VALUE (flags:nat) | BUILD_STRING (n:nat)
    | LOAD_LOCALS | LOAD_FROM_DICT_OR_GLOBALS (n:nat).

End Bytecode.
