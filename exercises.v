From mathcomp Require Import all_ssreflect ssralg ssrint ssrnum finmap matrix.
From mathcomp Require Import rat interval zmodp vector fieldext falgebra.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality set_interval Rstruct.
From mathcomp Require Import ereal reals signed topology prodnormedzmodule.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Lemma closed_diag_hausdorff (T : topologicalType) :
  closed [set (x, x) | x in [set: T]] <-> hausdorff_space T.
Proof.
split.
  move=> + x y xy_close => /(_ (x, y))[]; last by move=> ? _ [<- <-].
  move=> /= A [[/= A1 A2] [Ax Ay]] A12.
  have [z [/= A1z A2z]] := xy_close A1 A2 Ax Ay.
  by exists (z, z); split=> //; apply: A12.
admit.
Admitted.