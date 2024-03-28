Require Import Rdefinitions.
From mathcomp Require Import all_ssreflect ssralg ssrint ssrnum finmap matrix.
From mathcomp Require Import rat interval zmodp vector fieldext falgebra.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality set_interval Rstruct.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

(* Demo File for the 9:00 - 10:15 lesson :Coq/Rocq Tutorial: ssreflect tactics
and the MathComp library *)

(* Feel free to play with file while I'm talking !*)

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



(** MOVES **)


Lemma divand : forall (m n : nat), 2 %| n /\ 3 %| m -> 6 %| n * m .
Proof.
move=> m n. move=> H.
move: H. move=> [A B].
Admitted.

Lemma divor : forall (m n : nat), 2 %| n \/ 3 %| m -> 6 %| n * m .
Proof.
move=> m n. move=> H.
move: H. move=> [A | B].
Admitted.


Lemma div1 : forall (n : nat), 6 %| n -> 2 * 3 %| n .
Proof.
move=> n n6.
have H : 2 * 3 = 6. move=> //=.
move=> {H}. (* let's forget about H to prove H in another way *)
have H : 2 * 3 = 6 by []. (* even quicker *)
rewrite H.
move=> //.
Admitted.


Lemma div2 : forall (n m : nat), 6 %| n -> 2*3 %| n .
Proof.
move=> n m n6. move=> {m}. (* m is not needed *)
Admitted.

Lemma div3: forall (n m : nat), 6 %| n -> 2*3 %| n .
Proof.
move=> n _ n6. (* m is not needed, let's forget about it *)
Admitted.

(** REWRITES **)

(* As in Lean, one can rewrite thanks to an equality, going forward or backward *)
Lemma rewrite1 (n m : nat) : n = m -> 1 + n = 1 + m.
Proof.
move=> H. rewrite H. by []. (* n is replaced by m *)
Qed.

Lemma rewrite_1 (n m : nat) : n = m -> 1 + n = 1 + m.
Proof.
move=> H. rewrite -H. by []. (* now m is replaced by n *)
Qed.

(* We can start using ; to chain several commands on the same goal *)
Lemma rewrite2 (n m : nat) : n = m -> 1 + n = 1 + m.
Proof.
move=> H; rewrite H => //=.
Qed.

(* Notice that //= can be put directly after a rewrite in place *)
Lemma rewrite3 (n m : nat) : n = m -> 1 + n =  1 + m.
Proof.
move=> H; rewrite H //=.
Qed.

(* The prefered way is to conclude a proof writing "by ..." *)
Lemma rewrite4 (n m : nat) : n = m -> 1 + n =  1 + m.
Proof.
by move=> H; rewrite H.
Qed.

(* In fact, we do not want to bother introducing H, just write "->" instead of H*)
Lemma rewrite_directly (n m : nat) : n = m -> 1 + n =  1 + m.
Proof.
by move=> ->.
Qed.

(* And it works backward also "<-" *)
Lemma rewrite_directly_backward (n m : nat) : n = m -> 1 + n = 1 + m.
Proof.
by move=> <-.
Qed.

(* Sometimes we want to chain several lemmas, and we can*)

Lemma rewrite_a_lot (n m p q : nat) : n = m -> q = p -> p + n = q + m.
Proof.
by move=> -> ->.
Qed.

(* This is not the only thing you might want to do. Sometimes you do need to
rewrite thanks to an auxiliary hypothesis or lemma. You might need to
explicitely name the lemma, but for maintenance purpose you might not want to *)
Local Open Scope ring_scope.

Lemma subterm_selection (R : ringType) (p q : R) :
  (p + q + 1) * q = q * (q + p) + q.
Proof.
rewrite addrC.
rewrite (addrC q).
rewrite [_ + q]addrC.
rewrite [in q * _]addrC.
rewrite [X in _ = _ * X + _]addrC.
rewrite [in RHS]addrC.
Abort.


(* Let's go into vector spaces for a bit, and let's learn how to use "Search" *)
Lemma scalar_mult (R : fieldType) (E : lmodType R) (z : E) (r : R) :
r != 0 -> z = r *: (r^-1 *: z).
Proof.
move=> r0.
rewrite /(_ *: _). (*we might now want to do that, let's wrap it again*)
rewrite -/(_ *: _). (*and again*)
rewrite -!/(_ *: _).
(*we could just have written :rewrite -!/(_ *: _).*)
(* But now we know how this is called "scale". It is likely to be present in the
lemmas on that notion *)
Search "scale" (_ *: _).
Search (_ *: (_ *: _)).
rewrite scalerA.
Search (_ / _ = 1).
rewrite mulfV.
rewrite scale1r //.
by [].
(* In short, one could have used the ? sign to try to rewrite scale1r on all
subgoals before concluding with //*)

(*by move=> r0; rewrite scalerA mulfV ?scale1r.*)
Qed.

(*Now thanks to rewrite and to an externa lemma we can proove our first lemma*)
Check Gauss_dvd.
Check dvdn_mulr.
Check dvdn_mull.

Lemma divand_full m n : 2 %| n /\ 3 %| m -> 6 %| n * m .
Proof.
move=> [dvd2n dvd3n].
rewrite (@Gauss_dvd 2 3)//.
by rewrite dvdn_mulr// dvdn_mull.
Qed.


(** SEARCH **)

Search
(* Maybe on words I may want to find in the name of the lemma *) "mul"
(* then maybe a list of patterns I want to find *)(_ * _) (2 + _ = 1 +_)
(* then maybe a library into which I want to specifically look *) in topology.

Close Scope ring_scope.

(** VIEWS AND APPLY **)


Lemma applied (P Q : Prop): (P -> Q) -> P -> Q.
Proof.
move=> H HP; apply: H. by [].
(* by move=> H HP; apply: H *)
Qed.

(* One can also use views, meaning applying lemmas directly to hypothesis, while
introducing them. This is done thanks to "/lemma" *)

Lemma applied_view (P Q : Prop): (P -> Q) -> P -> Q.
Proof.
move=> H. move=> /H. by [].
(* by move=> H /H.*)
Qed.

(*Views can also be used with equivalences. You don't need to chose implication to use*)
Lemma applied_eq (P Q : Prop): (P <-> Q) -> P -> Q.
Proof.
by move=> H /H.
Qed.

(* Sometimes it's easier to feed an argument to a lemma than to apply the lemma.
This is done thanks to /(_ a) when the lemma is on top of the stack *)
Lemma applied_arg (P Q : Prop): P -> (P -> Q) -> Q.
Proof.
move=> HP /(_ HP).
by [].
Qed.

(* Look at what + is doing *)

Lemma applied_plus (P Q : Prop): (P -> Q) -> P -> Q.
Proof.
move=> + HP. move=> /(_ HP).
by [].
Qed.

(** CASE **)

(* case=> destructs an hypothesis while putting it in the context,
case:_ destruct inductive proposition while taking it from the context *)

Lemma ex_elim (m : nat) : (exists n : nat, m = S n) -> 0 < m.
Proof.
move=> [k hk]. (* `k` is the witness, `hk` is its property *)
rewrite hk. by []. (* That's something hard encoded in the ssrnat library *)
Qed.

Lemma case_bool (b1 b2 : bool) : b1 || ~~ b1.
Proof. by case: b1. Qed.

Lemma case_nat (n: nat) : (n= 0) \/ (0<n).
Proof. case: n; first by left. by move=> n; right. Qed.

(* Let's switch to more intricate objects *)
From mathcomp Require Import intdiv Rstruct reals exp.
Local Open Scope nat_scope.
Local Open Scope ring_scope.
Notation sqrt := Num.sqrt.
Notation rational := (range (@ratr R)).
Notation irrational := [predC rational].

(* In the proof for the irrationality of sqrt 2, we use case to destruct several hypotheses*)
Theorem sqrt2_irrational : sqrt 2 \in irrational.
Proof.
apply/negP; rewrite inE /=.
(* we use case on the first assumption to extract the witness x *)
case => x _ .
(*and then we use case on a newly introduced hypothesis, namely a good
characterization of rationals *)
(*move: (ratP x); case => p q _*)
case: (ratP x) => p q _.
rewrite rmorphM fmorphV/= !ratr_int.
move=> /(congr1 (fun x : R => (x ^+ 2))).
rewrite sqr_sqrtr// exprMn exprVn -!rmorphXn/= => /(canRL (mulfVK _)).
rewrite pnatr_eq0 => /(_ isT); rewrite -rmorphM/=; apply/eqP.
suff : (`|p|%N ^ 2 != 2 * q.+1 ^ 2)%N.
  apply: contra_neq => ?; apply: (mulrIn (@oner_neq0 R)).
  by rewrite -abszX natr_absz ger0_norm ?sqr_ge0.
apply/eqP => /(congr1 (odd \o logn 2))/=.
by rewrite lognM// !lognX/= !oddM/=.
Qed.

(* Fun *) Fact exists_rat_pow_of_irrat : exists a b : R,
  [&& a \in irrational, b \in irrational & a `^ b \in rational].
Proof.
pose x : R := sqrt 2; pose y := x `^ x.
have [yrat|/negP yNrat] := EM (y \in rational).
  by exists x, x; rewrite sqrt2_irrational.
exists y, x; rewrite [y \in _]yNrat sqrt2_irrational/=.
rewrite -powRrM -expr2 sqr_sqrtr// powR_mulrn// ?sqrtr_ge0//.
by rewrite sqr_sqrtr// inE/=; exists 2 => //=; rewrite ratr_nat.
Qed.

(** Near  notations and tactics **)
From mathcomp Require Import ereal reals signed topology prodnormedzmodule normedtype.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(* Continuity uses the limits --> notation, wich is just about filter inclusion.
The notation F --> x where F is a filter. This is a notation for (nbhs x) `<=`
F, the canonical filter of neighborhoods of x is included in F *)

(* The notation f @` A is used to denote the image of A : set E by f : E -> F *)

(* Continuity at x for a function f is defined as : f `@ x --> f x, meaning the
filter of neighborhoods of (f x) is included in the image by f of the filter of
neighborhoods of x *)

Lemma add_continuous_without_near (R : numFieldType)  (V : normedModType R): 
continuous (fun z : V * V => z.1 + z.2).
Proof.
move=> []. (* Let's destruct the continuous predicate*)
move=> x y /=. (* Let's introduce points*)
move=>A.
(* I'm just introdcing the appropriate neighborhood as I want to work on the statement
 that it is a neighborhood *)
move=>/nbhs_ballP. (* This allows me to say that A contains a ball around (x,y)*)
move=> [] /=.  (*And I just destruct the statement *)
move=> r r0 H.
apply/nbhs_ballP=>/=.
exists (r/2).
   Search ( 0 < _ /_). (* now I see that all I need is divr_gt0, 
   and that the other results should be infered from the context or computed.*)
   by apply: divr_gt0.
(* Now we need to prove an inclusion of sets: this is what the notaion `<=` is for*)
move=> /= z. 
(* Let's destruct what a ball is a product space is*)
move=> [] /=. 
(* We might want to rewrite this ball with a norm. This is done trough the
ball_normE lemma and computation *) 
Check ball_normE.
rewrite -ball_normE /=.
move=> Bx By.
apply: H. 
rewrite -ball_normE /=.
(* Now I'll use a lemma allowing me to split the norm in two, but before that
I'll need to do some rewriting *)
rewrite opprD.
rewrite addrACA.
by rewrite normm_lt_split.
Qed.

(* In short and without near, this would give:*)
Lemma add_continuous_short (R : numFieldType)  (V : normedModType R): 
continuous (fun z : V * V => z.1 + z.2).
Proof.
move=> [x y /=] A => /nbhs_ballP [/= r r0] H.
apply/nbhs_ballP=>/=.
exists (r/2); first by apply: divr_gt0.
move=> /= z []; rewrite -ball_normE /= => Bx By. 
by apply: H; rewrite -ball_normE /= opprD addrACA normm_lt_split.
Qed.

(* With near, we avoir or delay the explicit handling of (r/2)*)
Lemma add_continuous_with_near (R : numFieldType)  (V : normedModType R): 
continuous (fun z : V * V => z.1 + z.2).
Proof.
move=> [/= x y]; apply/cvgrPdist_lt =>/= e e0.
near=> a b => /=.
rewrite opprD addrACA normm_lt_split //.
  by near:a; apply: cvgr_dist_lt => //; apply: divr_gt0.
by near:b; apply: cvgr_dist_lt => //; apply: divr_gt0.
(*[near: a|near: b]; apply: cvgr_dist_lt => //; apply: divr_gt0.*)
Unshelve. all: by end_near. Qed.

(*For this short proof, we have not gained a lot. The posNum type allows to
automatically infer positivity and to avoir the two last lines*)

Lemma add_continuous_with_near_and_pos (R : numFieldType)  (V : normedModType R): 
continuous (fun z : V * V => z.1 + z.2).
Proof.
move=> [/= x y]; apply/cvgrPdist_lt=> _/posnumP[e]; near=> a b => /=.
by rewrite opprD addrACA normm_lt_split.
Unshelve. all: by end_near. Qed.


(*For short proofs this might not seem important. 
For long proofs, it makes a huge difference*)

Lemma continuous_bounded (R : numFieldType) (V W : normedModType R)
    (x : V) (f : {linear V -> W}) :
  {for 0, continuous f} -> bounded_near f (nbhs x).
Proof.
rewrite /prop_for /continuous_at linear0 /bounded_near => f0.
near=> M; apply/nbhs0P.
 near do rewrite /= linearD (le_trans (ler_normD _ _))// -lerBrDl.
apply: cvgr0_norm_le; rewrite // subr_gt0.
by []. (* This is were it happens*)
Unshelve. all: by end_near. Qed.

