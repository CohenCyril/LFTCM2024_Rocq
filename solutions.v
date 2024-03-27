From mathcomp Require Import all_ssreflect ssralg ssrint ssrnum finmap matrix.
From mathcomp Require Import fingroup action.
From mathcomp Require Import rat interval zmodp vector fieldext falgebra galois.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality set_interval Rstruct.
From mathcomp Require Import ereal reals signed topology prodnormedzmodule normedtype.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports.

Lemma square_and_cube_modulo7 (m n p : nat) : m = n ^ 2 -> m = p ^ 3 ->
  (m == 0 %[mod 7]) || (m == 1 %[mod 7]).
Proof.
(* Proof suggestion. *)
(* 1. First subsitute the first equality inside the rest and get rid of m *)
(*    see rewrite or intro patterns (after the move=>) *)
move=> ->.
(* 2. Take the modulo of the equation n ^ 2 = p ^ 2. *)
(*    You can use have: to pose an intermediate statement. *)
(*    Or you can use a congr1 in a forward view. *)
move=> /(congr1 (modn^~ 7)).
(* 3. Then push the modulo "to the leaves" / inside *)
(*    Hint: *) Search modn expn.
rewrite -modnXm -[in RHS]modnXm.
(* 4. Generalize using the fact that a modulo 7 is smaller than 7 *)
(*    Hint: *) Search leq modn in div.
move: (n %% 7) (p %% 7) (@ltn_pmod n 7 isT) (@ltn_pmod p 7 isT).
(* 5. Perform 7 case analysis for each modulo 7 *)
(*    Use repeated case or repeated [] inside move=> *)
by do 7?[case=> //]; do 7?[case=> //].
Qed.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section Galois.
Import GroupScope.

Lemma galNorm_fixedField {F : fieldType} {L : splittingFieldType F}
    (K E : {subfield L}) a :
  a \in E -> galNorm K E a \in fixedField 'Gal(E / K).
Proof.
(* Use the characteristic property of fixed fields, do not unfold *)
Search fixedField "P". (* this is an equivalence (reflect), so use apply/ *)
(* You might need the following to complete the proof: *)
move=> Ea; apply/fixedFieldP=> [|x galEx].
  by apply: rpred_prod => x _; apply: memv_gal.
rewrite [in RHS]/galNorm (reindex_acts 'R _ galEx) ?astabsR //=.
by rewrite rmorph_prod; apply: eq_bigr => y _; rewrite galM ?lfunE.
Qed.

End Galois.

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

Lemma closed_graph_function (T U : topologicalType) (f  : T -> U): 
  hausdorff_space U -> continuous f -> closed [set xy | f(xy.1) = xy.2].
Proof.
move=> U_hausdorff f_cont [x y] /= graph; rewrite (U_hausdorff (f x) y) //=.
move => A B Afx By. have [] := graph ((f @^-1` A)`*`B). 
 by exists ((f @^-1` A),B); first by split => //=; first by apply: f_cont. 
by move => [a b] /= [<-] []; exists (f a). 
Qed. 



Lemma continuous_linear_bounded_at0 (R : numFieldType) (V W : normedModType R)
    (f : {linear V -> W}) :
  {for 0, continuous f} -> bounded_near f (nbhs 0).
Proof.
move=> f0.
(* do not unfold bounded_near! *)
Search bounded_near.
rewrite ex_bound.
(* Pick a bound *)
exists 1.
(* Use a domain specific simplification lemma *)
rewrite near_simpl/=.
(* Use the continuity hypothesis *)
apply: (f0 [set z | `|z| <= 1]).
(* Use linearity *)
rewrite linear0.
apply: nbhs0_le.
done.
Qed.

Lemma with_near (R : numFieldType) (V W : normedModType R)
    (x : V) (f : {linear V -> W}) :
  {for 0, continuous f} -> bounded_near f (nbhs x).
Proof.
rewrite /prop_for /continuous_at linear0 /bounded_near => f0.
near=> M; apply/nbhs0P.
 near do rewrite /= linearD (le_trans (ler_normD _ _))// -lerBrDl.
by apply: cvgr0_norm_le; rewrite // subr_gt0.
Unshelve. all: by end_near. Qed.
 
