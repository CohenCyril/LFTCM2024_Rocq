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


(** MOVES **)

(*Lemma div6 : forall (m : nat), 2 %| m /\  3 %| m -> 6 %| m.
Proof. 
move=> m. move=> H.
move: H. move=>[A B].
Search _ (_*_ %| _).*)

Lemma div0 : forall (m n : nat), 2 %| n /\  3 %| m -> 6 %| n * m .
Proof. 
move=> m n. move=> H.
move: H. move=>[A B].
Admitted.


Lemma div1 : forall (n : nat), 6 %| n  -> 2*3 %| n .
Proof. 
move=> n n6.
have H : 2*3 = 6 by [].
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

(** Apply **)




Le
Search _ (_*_ %| _).
rewrite -[6]/(2*3).
apply: dvdn_mul => //=. (* Or use dvndP *)