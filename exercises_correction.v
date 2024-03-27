From mathcomp Require Import all_ssreflect ssralg ssrint ssrnum finmap matrix.
From mathcomp Require Import fingroup action.
From mathcomp Require Import rat interval zmodp vector fieldext falgebra galois.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality set_interval Rstruct.
From mathcomp Require Import ereal reals signed topology prodnormedzmodule normedtype.

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

Section Galois.
Import GroupScope.

Lemma galNorm_fixedField {F : fieldType} {L : splittingFieldType F}
    (K E : {subfield L}) a :
  a \in E -> galNorm K E a \in fixedField 'Gal(E / K).
Proof.
move=> Ea; apply/fixedFieldP=> [|x galEx].
  by apply: rpred_prod => x _; apply: memv_gal.
rewrite {2}/galNorm (reindex_acts 'R _ galEx) ?astabsR //=.
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



Lemma continuous_linear_bounded (R : numFieldType) (V W : normedModType R)
    (x : V) (f : {linear V -> W}) :
  {for 0, continuous f} -> bounded_near f (nbhs 0).
Proof.
rewrite /prop_for /continuous_at /(_ @ _) /bounded_near //=.
(*You will witness the notation F --> x where F is a filter. 
This is a notation for (nbhs x) `<=` F,
the canonical filter of neighborhoods of x is included in F  *)
rewrite linear0 => f0.
(* The notation "\near" is used in mathcomp-analysis
to represent filter inclusion:
  \forall x \near F, P x <-> F (fun x => P x). 
A whole set of tactics and lemmas are available to reason with near.
 For now, you can get back to filter reasoning with near E*)
rewrite nearE //=  /+oo. 
move: (f0 (ball 0 1)).
move => /(_ (nbhsx_ballx 0 1 ltr01)) //= /nbhs_norm0P [] /= M M0 H.
exists M; split. 
 by rewrite realE; apply/orP; left; rewrite le0r; apply/orP;right. 
move => r Mr; apply/nbhs_norm0P=>/=.
have r0 : 0 <r by apply: lt_trans; first by apply: M0.
exists (M * r) => //=; first by apply: mulr_gt0; rewrite // invr_gt0.
move => z /= zMr.
have -> : z = r*:(r^-1*:z).
  by rewrite scalerA mulfV ?scale1r //; apply:lt0r_neq0.
rewrite linearE normrZ gtr0_norm // ger_pMr //. 
move: (H (r^-1 *: z)) => //=; rewrite -ball_normE /= normrZ. 
rewrite mulrC  -[X in (`|X| <1)]opprB normrE subr0.
rewrite -ltr_pdivlMr normrV ?invr_gt0 ?normr_gt0.
have -> :`|r| =r  by rewrite gtr0_norm. 
rewrite invrK => /(_ zMr) H0; rewrite le_eqVlt;apply/orP; right => //.
by apply: unitf_gt0.
by apply: lt0r_neq0. 
by apply: unitf_gt0.
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
 
