From mathcomp Require Import all_ssreflect ssralg ssrint ssrnum finmap matrix.
From mathcomp Require Import rat interval zmodp vector fieldext falgebra.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality set_interval Rstruct.
From mathcomp Require Import ereal reals signed topology prodnormedzmodule normedtype.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

(*Demo File for the 9:00 - 10:15 lesson :Coq/Rocq Tutorial: ssreflect tactics
and the MathComp library *)

(* Feel free to play with file while I'm talking !*)