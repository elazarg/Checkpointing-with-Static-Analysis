(*
  Main.v
  Top-level module instantiation
*)

Require Import IR.
Require Import SIGS.
Require Import TYPE.
Require Import PTR.
Require Import LOWER.

Module MyAnalysis := PointerAnalysis TypeSystem.
