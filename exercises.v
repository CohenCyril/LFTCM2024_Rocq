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

Lemma square_and_cube_modulo7 (m n p : nat) : m = n ^ 2 -> m = p ^ 3 ->
  (m == 0 %[mod 7]) || (m == 1 %[mod 7]).
Proof.
move=> -> /(congr1 (modn^~ 7)); rewrite -modnXm -[in RHS]modnXm.
move: (n %% 7) (p %% 7) (@ltn_pmod n 7 isT) (@ltn_pmod p 7 isT).
by do 7?[case=> //]; do 7?[case=> //].
Qed.

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
move=> T_hausdorff [x y] xydiag; rewrite -(T_hausdorff x y)//.
move=> A B Ax By; have [] := xydiag (A `*` B); first by exists (A, B).
by move=> [a b] [[_ _ [-> <-]] [/=]]; exists a.
Qed.