From mathcomp Require Import all_ssreflect ssralg ssrint ssrnum finmap matrix.
From mathcomp Require Import fingroup action.
From mathcomp Require Import rat interval zmodp vector fieldext falgebra galois.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality set_interval Rstruct.
From mathcomp Require Import ereal reals signed topology prodnormedzmodule normedtype.
From mathcomp Require Import ring lra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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
  - A "view" is a lemma of the form T : H -> H' or T: H <-> H', which transforms
    an hypothesis on the top of the stack when we do  move=> /H.. 

  *)

(* Dictionnary *)
(* SSreflect /  Approximate Lean *)

(* move=>    | rintros *)
(* move:     | revert  *)
(* rewrite   | rw      *)
(*           | simp    *)
(* rewrite / | dsimp   *)
(* apply:    | apply   *)
(*   ;       |   <;>   *)
(*   ; first |    ;    *)
(*    /=     |         *)
(*    //     |         *)
(*    []     |   〈 〉    *)

(* Invariants between Lean and Ssreflect *)
(*  left right exists split ...   *)

(* Basic and advanced cheat sheets  *)
(* http://www-sop.inria.fr/marelle/math-comp-tut-16/MathCompWS/basic-cheatsheet.pdf *)
(*  http://www-sop.inria.fr/marelle/math-comp-tut-16/MathCompWS/cheatsheet.pdf *)

(* This sheets feature one exercice on basic number theory, two exercises on
 basic topology, and one exercice on boundedness in normed spaces *)

Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports.

Lemma square_and_cube_modulo7 (m n p : nat) : m = n ^ 2 -> m = p ^ 3 ->
  (m == 0 %[mod 7]) || (m == 1 %[mod 7]).
Proof.
(* Proof suggestion. *)
(* 1. First subsitute the first equality inside the rest and get rid of m *)
(*    see rewrite or intro patterns (after the move=>) *)
(* 2. Take the modulo of the equation n ^ 2 = p ^ 2. *)
(*    You can use have: to pose an intermediate statement. *)
(*    Or you can use a congr1 in a forward view. *)
(* 3. Then push the modulo "to the leaves" / inside *)
(*    Hint: *) Search modn expn.
(* 4. Generalize using the fact that a modulo 7 is smaller than 7 *)
(*    Hint: *) Search leq modn in div.
(* 5. Perform 7 case analysis for each modulo 7 *)
(*    Use repeated case or repeated [] inside move=> *)
Admitted.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section Galois.
Import GroupScope.

Lemma galNorm_fixedField {F : fieldType} {L : splittingFieldType F}
    (K E : {subfield L}) a :
  a \in E -> galNorm K E a \in fixedField 'Gal(E / K).
Proof.
move=> Ea.
(* Use the characteristic property of fixed fields, do not unfold *)
Search fixedField "P". (* this is an equivalence (reflect), so use apply/ *)
(* You might need the following to complete the proof: *)
About rpred_prod.
About memv_gal.
About reindex_acts.
About astabsR.
About rmorph_prod.
About eq_bigr.
About galM.
About lfunE.
Admitted.

End Galois.

(* Information about notations and theorem can be found in the header of 
https://github.com/math-comp/analysis/blob/master/theories/topology.v 
 But should not be needed for the next two exercises *)  

(*Let us show that a Topological space is hausdorff if and only if its diagonal
is closed. You might want to unfold definitions to understand how they are
structured, but it is not necessary to unfold them in the final version of the
proof. Otherwise, no search nor any external lemmas are needed.  *)

(*Here's the idea for the proof: a space is hausdorff by definition if any two
different points x y can always be separated by a neighborhood V *)
Print hausdorff_space.
(* Another way to state that, which is what is defined above,
 is that if x is is every neighborhood of y, then x=y *)
 (* Now supposed the diagonal is closed. Then if y is in every neighborhood that
 contains x, then (y,x) is in the closure of the diagonal, and thus y=x*)
 
 (* More formally, the diagonal is  [set (x, x) | x in [set: T]]. 
Neigborhoods in the products are exactly product of neighborhoods.*)
Print closed.
Print closure.

(* A set C is closed if it contains its closure, that is if its contains all the
points p such that all neighborhood of p intersects C .*)

Lemma closed_diag_hausdorff (T : topologicalType) : closed [set (x, x) | x in [set: T]] <-> hausdorff_space T. 
Proof. 
split. 
Admitted.

(* Continuity uses the limits --> notation, wich is just about filter inclusion.
*)
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


(*THe following is another exercise to use continuity. 
These are the lemmas to be used:*)
About ex_bound.
About linear0.
About nbhs_le.

Lemma continuous_linear_bounded_at0 (R : numFieldType) (V W : normedModType R)
    (f : {linear V -> W}) :
  {for 0, continuous f} -> bounded_near f (nbhs 0).
Proof.
Admitted.

(* The following is the generalized version at any point x. If you want, you can
try to do it without near *)
(* Then we still suggest to use a structure that allow automation on positive
numbers: https://github.com/math-comp/analysis/blob/master/theories/signed.v *)
Lemma with_near (R : numFieldType) (V W : normedModType R)
    (x : V) (f : {linear V -> W}) :
  {for 0, continuous f} -> bounded_near f (nbhs x).
Proof.
rewrite /prop_for /continuous_at linear0 /bounded_near => f0.
near=> M; apply/nbhs0P.
 near do rewrite /= linearD (le_trans (ler_normD _ _))// -lerBrDl.
apply: cvgr0_norm_le; rewrite // subr_gt0.
by []. (* This is were it happens*)
Unshelve. all: by end_near. Qed.
