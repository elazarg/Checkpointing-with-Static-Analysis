
From Stdlib Require Import String List Bool Arith ZArith PeanoNat.

Module Python.

Inductive UnOpTag  := UNeg | UPos | UInvert | UNot.
Inductive BinOpTag := BAdd | BSub | BMul | BTrueDiv | BFloorDiv | BMod
                    | BMatMul | BAnd | BOr | BXor | BLShift | BRShift.
Inductive CmpOpTag := CEq | CNe | CLt | CLe | CGt | CGe | CIs | CIsNot | CIn | CNotIn.

Inductive DunderTag :=
| DTagUnOp  (op:UnOpTag)
| DTagBinOp (op:BinOpTag) (inplace:bool)
| DTagCmpOp (op:CmpOpTag).

Inductive Dunder (T : Set) :=
| DUnOp  (op:UnOpTag)  (arg:T)
| DBinOp (op:BinOpTag) (lhs rhs:T) (inplace:bool)
| DCmpOp (op:CmpOpTag) (lhs rhs:T).

End Python.
