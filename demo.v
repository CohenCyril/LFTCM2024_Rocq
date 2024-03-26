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

(*SSreflect / Lean cheat sheet *)

(** MOVES **)



Lemma divand : forall (m n : nat), 2 %| n /\  3 %| m -> 6 %| n * m .
Proof. 
move=> m n. move=> H.
move: H. move=>[A B].
Admitted.

Lemma divor : forall (m n : nat), 2 %| n \/  3 %| m -> 6 %| n * m .
Proof. 
move=> m n. move=> H.
move: H. move=>[A | B].
Admitted.


Lemma div1 : forall (n : nat), 6 %| n  -> 2*3 %| n .
Proof. 
move=> n n6.
have H : 2*3 = 6. move => //=.
move => {H} (*let's forget about H to prove H in another way*)
have H : 2*3 = 6 by []. (*evenx quicker*)
rewrite H.
move => //.
Admitted.


Lemma div2 : forall (n m : nat), 6 %| n  -> 2*3 %| n .
Proof. 
move=> n m n6. move=> {m}. (*m is not needed*)
Admitted.

Lemma div3: forall (n m : nat), 6 %| n  -> 2*3 %| n .
Proof. 
move=> n _ n6. (*m is not needed, let's forget about it*)
Admitted.

(** Rewrites **)

(*As is Lean, one can rewrite thanks to an equality, going forward or backward*)
Lemma rewrite1 (n m : nat) : n = m -> 1 + n = 1+ m.
Proof.
move => H. rewrite H. by [].  (* n is replaced by m*)
Qed.

Lemma rewrite_1 (n m : nat) : n = m -> 1 + n = 1+ m.
Proof.
move => H. rewrite -H. by []. (* now m is replaced by n*) 
Qed.

(* we can start using ; to chain several commands on the same goal *)
Lemma rewrite2 (n m : nat) : n = m -> 1 + n = 1+ m.
Proof.
move => H; rewrite H => //=.  
Qed.

(* Notice that  //= can be put directly after a rewrite in place *)
Lemma rewrite3 (n m : nat) : n = m -> 1 + n = 1+ m.
Proof.
move => H; rewrite H //=.  
Qed.

(* The prefered way is to conclude a proof writing "by ..."  *)
Lemma rewrite4 (n m : nat) : n = m -> 1 + n = 1+ m.
Proof.
by move => H; rewrite H.  
Qed.

(* To be honest, we do not want to bother introducing H, just write "->" instead of H*)

Lemma rewrite_directly (n m : nat) : n = m -> 1 + n = 1+ m.
Proof.
by move =>  ->.  
Qed.

(* And it works backward also "<-" *)
Lemma rewrite_directly_backward (n m : nat) : n = m -> 1 + n = 1+ m.
Proof.
by move =>  <-.  
Qed.

(* Sometimes we want to chain several lemmas, and we can*)

Lemma rewrite_a_lot (n m p q: nat) : n = m -> q=p -> p + n = q+ m.
Proof.
by move =>  -> ->.  
Qed.

(*This is not the only thing you might want to do. Sometimes you do need to
rewrite thanks to an auxiliary hypothesis or lemma. You might need to
explicitely name the lemma, but for maintenance purpose you might not want to*)
Local Open Scope ring_scope. 

Lemma subterm_selection  (R : ringType) (p q : R) :
  (p + q +1 )*q = q * (q + p) +q.
Proof.
rewrite addrC.
rewrite (addrC q).
rewrite [_ + q]addrC.
rewrite [in  q*_]addrC.
rewrite [X in _ = _ * X + _]addrC.
rewrite [in RHS]addrC.
Abort.


(*Let's go into vector spaces for a bit, and let's learn how to use "Search"*)
Lemma scalar_mult (R : fieldType) (E : lmodType R) (z : E) (r : R) : 
r != 0 ->z = r*:(r^-1*:z).
Proof. 
move=> r0.
rewrite /(_*:_). (*we might now want to do that, let's wrap it again*)
rewrite -/(_*:_). (*and again*)
rewrite -/(_*:_). 
(*we could just have written :rewrite -/!(_*:_).*)
(* But now we know how this is called "scale". It is likely to be present in the
lemmas on that *)
 Search "scale" (_*:_). Search (_*:(_*:_)).
rewrite scalerA. 
Search (_/_ = 1).
rewrite mulfV.
rewrite scale1r //.
by [].
(* In short, one could have used the ? sign to try to rewrite scale1r on all
subgoals before concluding with //*)

(*by move=> r0; rewrite scalerA mulfV ?scale1r.*)
Qed.

(** Search **)

Search 
(*smaybe ome words I may want to find in the name of the lemma*) "mul" "spring"
(*then maybe a list of patterns I want to find*)(_*_) (2 + _ = 1 +_)
(* then maybe a library I want to specifically look in*) in topology.

Close Scope ring_scope.

(** An Apply a day **)


Lemma applied  (P Q : Prop): (P -> Q) -> P -> Q.
Proof.
move=> H HP; apply: H. by [].  
(* by move=> H HP; apply: H*)
Qed.

(* One can also use views, meaning applying lemmas directly to hypothesis, while
introducing them. This is done thanks to "/lemma"*)

Lemma applied_view  (P Q : Prop): (P -> Q) -> P -> Q.
Proof.
move=> H. move => /H. by [].  
(* by move=> H /H.*)
Qed.

(*Views can also be used with equivalences*)

Lemma applied_eq (P Q : Prop): (P <-> Q) -> P -> Q.
Proof.
by move=> H /H.
Qed.

(* Sometimes it's easier to feed an argument to a lemma than to apply the lemma.
This is done thanks to /(_ a) when the lemma is on top of the stack*)

Lemma applied_arg  (P Q : Prop): P -> (P -> Q) -> Q.
Proof.
move=> HP /(_ HP).
by []. 
Qed.

(* Look at what + is doing *)

Lemma applied_plus  (P Q : Prop): (P -> Q) -> P -> Q.
Proof.
move=> + HP. move => /(_ HP).
by []. 
Qed.

(** Case **)

(*case=> destructs an hypothesis while putting it in the context,
case:_ destruct inductive proposition while taking it from the context *)

Lemma ex_elim (m : nat) : (exists n : nat, m = S n) -> 0 < m.
Proof.
move=> [k hk]. (* `k` is the witness, `hk` is its property *)
rewrite hk. by []. (* That's something hard encoded in the ssrnat library *)
Qed.

Lemma EM_bool (b1 b2 : bool) : b1 || ~~ b1.
Proof. by case: b1. Qed.

Lemma using_EM  (n: nat): n=n.
Proof.
Check EM.
case: (EM (n = 0)).
Abort.


(* suff, wlog *)


(* near *)