From mathcomp Require Import all_ssreflect ssralg ssrint ssrnum finmap matrix.
From mathcomp Require Import rat interval zmodp vector fieldext falgebra.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality set_interval Rstruct.
From mathcomp Require Import ereal reals signed topology prodnormedzmodule normedtype.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* This sheets feature one exercice on basic number theory, two exercises on
 basic topology, and one exercice on boundedness in normed spaces *)

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Lemma square_and_cube_modulo7 (m n p : nat) : m = n ^ 2 -> m = p ^ 3 ->
  (m == 0 %[mod 7]) || (m == 1 %[mod 7]).
Proof.
(* Proof suggestion *)
(* 1. first subsitute the first equality inside the rest and get rid of m *)
(*    see rewrite or intro patterns (after the move=>) *)
(* 2. the push the modulo "to the leaves" / "inside" *)
(*    Hint: *) Search modn expn.
(* 3. Generalize using the fact that a modulo 7 is smaller than 7 *)
(*    Hint: *) Search leq modn in div.
(* 4. Perform 7 case analysis for each modulo 7 *)
(*    Use repeated case or repeated [] inside move=> *)
Admitted.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(* Remember our basic sets of tactics: 
- "move => H" and "move: H" to put an hypothesis from the goal to context, and
  vice-versa. To break H, use move => [A B]
- The signs // /= can be use to refer to an hypothesis in the context and to
  apply basic computations.  When in doubt, keep calm and try " move => //="/.
- have lem := .... allows you to introduce an intermediate goal. Insteas of
  "lem", you can also write "->" or "<-" to rewrite, or "[]"to break the lemma
  in its sub logical parts.
  - exists: x  allows to prove an existential goal
  - rewrite (with all its patterns) does rewriting.
  - appply: H. applies the hypothesis or lemma H. 
  - A "view" is a lemma of the form T : H -> H' or T: H <-> H'. 
  
  *)

(* Basic and advanced cheat sheets  *)
(* http://www-sop.inria.fr/marelle/math-comp-tut-16/MathCompWS/basic-cheatsheet.pdf *)
(*  http://www-sop.inria.fr/marelle/math-comp-tut-16/MathCompWS/cheatsheet.pdf *)


(* Information about notations and theorem can be found in the header of 
https://github.com/math-comp/analysis/blob/master/theories/topology.v 
 But should not be needed for the next two exercises *)  

Lemma closed_diag_hausdorff (T : topologicalType) :
  closed [set (x, x) | x in [set: T]] <-> hausdorff_space T.
Proof.
Admitted.

(* Continuity uses the limits --> notation, wich is just about filter inclusion.  *)
About continuous.
(*You will witness the notation F --> x where F is a filter. This is a notation
for (nbhs x) `<=` F, the canonical filter of neighborhoods of x is included in F
*)

(* The notation f @^-1` A is used to denote the reverse image of A (included in
F) by f : E -> F *)
Lemma closed_graph_function (T U : topologicalType) (f  : T -> U): 
  hausdorff_space U -> continuous f -> closed [set xy | f(xy.1) = xy.2].
Proof.
Admitted. 

(* The next exercise concerns normed spaces.*) 
(* The notation "\near" is used in mathcomp-analysis to represent filter
inclusion: \forall x \near F, P x <-> F (fun x => P x). A whole set of tactics
and lemmas are available to reason with near.

In normed spaces, these tactics allow to avoid giving the explicit distance
between two points, and reasoning with explicit epsilon.

For now, you can get back to filter reasoning with nearE, and explicit handling
of epsilon thanks to a whole set of rewriting lemmas*)

(* Notations :
 - _ *: _ : scalar multiplication, search for "scale" in lemmas' names.
 - _ * _ , _ + _, as usual, called "mult" and "add" *)

(* Searching lemmas : 
-  By name : Search "scale".
-  By pattern : Search _ "1*:_". The first _ is the space to be used of a
   pattern that needs to be in the conclusion of the lemma.
-  Both: Search "scale" (_+_) (_*:_).
-  Somme lemmas use predicate instead of notations and are harder to find. For example :    *)
Check scale1r.
(* uses "left_id" to denote "1*:r=r". *)

(*Here's a set of lemmas that might be useful. *)
(* TODO *)
(*TODO : find a simpler proof without orP *)
Lemma continuous_linear_bounded (R : realFieldType) (V W : normedModType R)
    (x : V) (f : {linear V -> W}) :
  {for 0, continuous f} -> bounded_near f (nbhs 0).
Proof.
rewrite /prop_for /continuous_at /(_ @ _) /bounded_near //= /=.
rewrite linear0 => f0.
rewrite nearE //=  /+oo. 
move: (f0 (ball 0 1)) => /(_ (nbhsx_ballx 0 1 ltr01)) //=.
move=> /nbhs_norm0P [] /= M M0 H.
exists M; split => //=.
move => r Mr; apply/nbhs_norm0P=>/=.
have r0 : 0 <r by apply: lt_trans; first by apply: M0.
exists (M * r) => /=; first by apply: mulr_gt0; rewrite // invr_gt0.
move => z /= zMr.
have -> : z = r*:(r^-1*:z). 
  rewrite scalerA mulrV //= ?scale1r ?unitf_gt0 //.
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
 
