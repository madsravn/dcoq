(* week_35.v *)
(* dIFP 2014-2015, Q1 *)
(* Olivier Danvy <danvy@cs.au.dk> *)

(* **********

   (0) download and install on your computer:
       - Coq
       - Emacs with Proof General (tick "3 Windows mode layout" in the Coq top menu;
         use the hybrid mode if your screen is not wide enough)

   (1) edit the present file, and step through it with Coq,
       proving the lemmas as you go

   ********** *)

Check O.

Check 0.

Check 1.

Check S O.

Check S 1.

Check S (S (S O)).

Check (fun x => S x).

Check S.

Check (fun x => S (S x)).

Check (fun f => fun x => S (f (S x))).

Check (fun f x => S (f (S x))).

Check 1 + 2.

Compute 1 + 2.

Check
  (fun (P : Prop) (p : P) => p).

Check
  (fun (P Q : Prop) (p : P) (q : Q) => p).

Check
  (fun (P Q : Prop) (p : P) (q : Q) => q).

(* ********** *)

(* Propositional logic:

   P ::= X
       | P -> P
       | P /\ P
       | P \/ P

   X ::= A | B | C | D | E | ...

   forall A B C ... : Prop, p
*)

(*
   intro and apply
*)

Lemma La :
  forall P : Prop,
    P -> P.
Proof.
  intro P.
  intro H_P.
  apply H_P.
Qed.

(*
   intros
*)

Lemma La' :
  forall P : Prop,
    P -> P.
Proof.
  intros P H_P.
  apply H_P.
Qed.

Lemma Lb :
  forall P Q : Prop,
    P -> Q -> P.
Proof.
  intro P.
  intro Q.
  intro H_P.
  intro H_Q.
  apply H_P.
Qed.

Lemma Lb' :
  forall P Q : Prop,
    P -> Q -> P.
Proof.
  intros P Q.
  intros H_P H_Q.
  apply H_P.
Qed.

Lemma Lb'' :
  forall P Q : Prop,
    P -> Q -> P.
Proof.
  intros P Q H_P H_Q.
  apply H_P.
Qed.

Lemma Lc :
  forall P Q : Prop,
    P -> Q -> Q.
Proof.
  intros P Q.
  intros H_P H_Q.
  apply H_Q.
Qed.


Lemma Ld :
  forall P1 P2 P3 P4 P5 : Prop,
    P1 -> P2 -> P3 -> P4 -> P5 -> P3.
Proof.
  intros P1 P2 P3 P4 P5.
  intros H_P1 H_P2 H_P3 H_P4 H_P5.
  apply H_P3.
Qed.

(* ********** *)

(* conjunction in an assumption: use destruct *)

Lemma Ca :
  forall P1 P2 : Prop,
    P1 /\ P2 -> P2.
Proof.
  intros P1 P2.
  intros H_P1_and_P2.
  destruct H_P1_and_P2 as [H_P1 H_P2].
  apply H_P2.
Qed.

Lemma Ca' :
  forall P1 P2 : Prop,
    P1 /\ P2 -> P2.
Proof.
  intros P1 P2.
  intros [H_P1 H_P2].
  apply H_P2.
Qed.

Lemma Ca'' :
  forall P1 P2 : Prop,
    P1 /\ P2 -> P1.
Proof.
  intros P1 P2.
  intros [H_P1 H_P2].
  apply H_P1.
Qed.


Lemma Cb :
  forall P1 P2 P3 : Prop,
    P1 /\ (P2 /\ P3) -> P3.
Proof.
  intros P1 P2 P3.
  intros [H_P1 [H_P2 H_P3]].
  apply H_P3.
Qed.

Lemma Cb' :
  forall P1 P2 P3 : Prop,
    P1 /\ P2 /\ P3 -> P3.
Proof.
  intros P1 P2 P3.
  intros [H_P1 [H_P2 H_P3]].
  apply H_P3.
Qed.

Lemma Cc :
  forall P1 P2 P3 P4 : Prop,
    (P1 /\ P2) /\ (P3 /\ P4) -> P3.
Proof.
  intros P1 P2 P3 P4.
  intros [[H_P1 H_P2] [H_P3 H_P4]].
  apply H_P3.
Qed.
(* ********** *)

(* conjunction in the goal: use split *)

Lemma conjunction_is_commutative :
  forall P Q : Prop,
    P /\ Q -> Q /\ P.
Proof.
  intros P Q.
  intros [H_P H_Q].
  split.
    apply H_Q.
    apply H_P.
Qed.

Lemma conjunction_is_commutative' :
  forall P Q : Prop,
    P /\ Q -> Q /\ P.
Proof.
  intros P Q [H_P H_Q].
  split.
    apply H_Q.
    apply H_P.
Qed.

(*
   Notation: "X <-> Y" is the same as "(X -> Y) /\ (Y -> X)"
*)

Lemma conjunction_is_commutative_either_way :
  forall P Q : Prop,
    P /\ Q <-> Q /\ P.
Proof.
  intros P Q.
  split.
    intros [H_P H_Q].
    split.
    apply H_Q.
    apply H_P.

    intros [H_Q H_P].
    split.
    apply H_P.
    apply H_Q.
Qed.

(* Simpler: apply conjunction_is_commutative instead of repeating its proof *)

Lemma conjunction_is_commutative_either_way' :
  forall P Q : Prop,
    P /\ Q <-> Q /\ P.
Proof.
  intros P Q.
  split.
  apply (conjunction_is_commutative P Q).
  apply (conjunction_is_commutative Q P).
Qed.

Lemma conjunction_is_associative_from_left_to_right :
  forall P1 P2 P3 : Prop,
    (P1 /\ P2) /\ P3 -> P1 /\ (P2 /\ P3).
Proof.
  intros P1 P2 P3.
  intros [[H_P1 H_P2] H_P3].
  split.
    apply H_P1.
    split.
      apply H_P2.
      apply H_P3.
Qed.

Lemma conjunction_is_associative_from_right_to_left :
  forall P1 P2 P3 : Prop,
    P1 /\ (P2 /\ P3) -> (P1 /\ P2) /\ P3.
Proof.
  intros P1 P2 P3.
  intros [H_P1 [H_P2 H_P3]].
  split.
  split.
  apply H_P1.
  apply H_P2.
  apply H_P3.
Qed.

Lemma conjunction_is_associative_either_way :
  forall P1 P2 P3 : Prop,
    P1 /\ (P2 /\ P3) <-> (P1 /\ P2) /\ P3.
Proof.
  intros P1 P2 P3.
  split.
  apply conjunction_is_associative_from_right_to_left.
  apply conjunction_is_associative_from_left_to_right.
Qed.



Lemma conjunction_is_associative_4_from_left_to_right :
  forall P1 P2 P3 P4 : Prop,
    P1 /\ (P2 /\ (P3 /\ P4)) -> ((P1 /\ P2) /\ P3) /\ P4.
Proof.
  intros P1 P2 P3 P4.
  intros [H_P1 [H_P2 [H_P3 H_P4]]].
  split.
  split.
  split.
  apply H_P1.
  apply H_P2.
  apply H_P3.
  apply H_P4.
Qed.

Lemma conjunction_is_associative_4_from_right_to_left :
  forall P1 P2 P3 P4 : Prop,
    ((P1 /\ P2) /\ P3) /\ P4 -> P1 /\ (P2 /\ (P3 /\ P4)).
Proof.
  intros P1 P2 P3 P4.
  intros [[[H_P1 H_P2] H_P3] H_P4].
  split.
  apply H_P1.
  split.
  apply H_P2.
  split.
  apply H_P3.
  apply H_P4.
Qed.


Lemma conjunction_is_associative_4_either_way :
  forall P1 P2 P3 P4 : Prop,
    P1 /\ (P2 /\ (P3 /\ P4)) <-> ((P1 /\ P2) /\ P3) /\ P4.
Proof.
  intros P1 P2 P3 P4.
  split.
  apply (conjunction_is_associative_4_from_left_to_right P1 P2 P3 P4).
  apply (conjunction_is_associative_4_from_right_to_left P1 P2 P3 P4).
Qed.

(* ********** *)

(* disjunction in the goal: use left or right *)

Lemma whatever_1 :
  forall P Q : Prop,
    P -> Q -> P \/ Q.
Proof.
  intros P Q.
  intros H_P H_Q.
  left.
  apply H_P.
Qed.

Lemma whatever_1' :
  forall P Q : Prop,
    P -> Q -> P \/ Q.
Proof.
  intros P Q.
  intros H_P H_Q.
  right.
  apply H_Q.
Qed.

(* ********** *)

(* disjunction in an assumption: use destruct *)

Lemma disjunction_is_commutative :
  forall P Q : Prop,
    P \/ Q -> Q \/ P.
Proof.
  intros P Q.
  intro H_P_or_Q.
  destruct H_P_or_Q as [H_P | H_Q].
  right.
  apply H_P.
  left.
  apply H_Q.
Qed.

Lemma disjunction_is_commutative' :
  forall P Q : Prop,
    P \/ Q -> Q \/ P.
Proof.
  intros P Q.
  intros [H_P | H_Q].
  right.
  apply H_P.
  left.
  apply H_Q.
Qed.

Lemma disjunction_is_commutative'' :
  forall P Q : Prop,
    P \/ Q -> Q \/ P.
Proof.
  intros P Q [H_P | H_Q].
  right.
  apply H_P.
  left.
  apply H_Q.
Qed.

Lemma disjunction_is_commutative_either_way :
  forall P Q : Prop,
    P \/ Q <-> Q \/ P.
Proof.
  intros P Q.
  split.
  intros [H_P | H_Q].
  right.
  apply H_P.
  left.
  apply H_Q.
  intros [H_Q | H_P].
  right.
  apply H_Q.
  left.
  apply H_P.
Qed.

Lemma disjunction_is_associative_from_left_to_right :
  forall P1 P2 P3 : Prop,
    (P1 \/ P2) \/ P3 -> P1 \/ (P2 \/ P3).
Proof.
  intros P1 P2 P3 [[H_P1 | H_P2] | H_P3].
  left. apply H_P1.
  right. left. apply H_P2.
  right. right. apply H_P3.
Qed.

Lemma disjunction_is_associative_from_right_to_left :
  forall P1 P2 P3 : Prop,
    P1 \/ (P2 \/ P3) -> (P1 \/ P2) \/ P3.
Proof.
  intros P1 P2 P3 [ H_P1 | [ H_P2 | H_P3]].
  left. left. apply H_P1.
  left. right. apply H_P2.
  right. apply H_P3.
Qed.

Lemma disjunction_is_associative_either_way :
  forall P1 P2 P3 : Prop,
    P1 \/ (P2 \/ P3) <-> (P1 \/ P2) \/ P3.
Proof.
  intros P1 P2 P3.
  split.
  apply (disjunction_is_associative_from_right_to_left P1 P2 P3).
  apply (disjunction_is_associative_from_left_to_right P1 P2 P3).
Qed.


Lemma disjunction_is_associative_4_from_left_to_right :
  forall P1 P2 P3 P4 : Prop,
    P1 \/ (P2 \/ (P3 \/ P4)) -> ((P1 \/ P2) \/ P3) \/ P4.
Proof.
  intros P1 P2 P3 P4.
  intros [H_P1 | [ H_P2 | [H_P3 | H_P4]]].
  left. left. left. apply H_P1.
  left. left. right. apply H_P2.
  left. right. apply H_P3.
  right. apply H_P4.
Qed.

Lemma disjunction_is_associative_4_from_right_to_left :
  forall P1 P2 P3 P4 : Prop,
    ((P1 \/ P2) \/ P3) \/ P4 -> P1 \/ (P2 \/ (P3 \/ P4)).
Proof.
  intros P1 P2 P3 P4.
  intros [[[H_P1 | H_P2] | H_P3] | H_P4].
  left. apply H_P1.
  right. left. apply H_P2.
  right. right. left. apply H_P3.
  right. right. right. apply H_P4.
Qed.

Lemma disjunction_is_associative_4_either_way :
  forall P1 P2 P3 P4 : Prop,
    P1 \/ (P2 \/ (P3 \/ P4)) <-> ((P1 \/ P2) \/ P3) \/ P4.
Proof.
  intros P1 P2 P3 P4.
  split.
  apply (disjunction_is_associative_4_from_left_to_right P1 P2 P3 P4).
  apply (disjunction_is_associative_4_from_right_to_left P1 P2 P3 P4).
Qed.


(* ********** *)

Lemma transitivity_of_implication :
  forall A B C : Prop,
    (A -> B) -> (B -> C) -> (A -> C).
Proof.
  intros A B C.
  intro H_A_implies_B.
  intro H_B_implies_C.
  intro H_A.
  apply H_B_implies_C.
  apply H_A_implies_B.
  apply H_A.
Qed.

Lemma transitivity_of_implication' :
  forall A B C : Prop,
    (B -> C) -> (A -> B) -> (A -> C).
Proof.
  intros A B C.
  intro H_B_IMPLIES_C.
  intro H_A_IMPLIES_B.
  intro H_A.
  apply H_B_IMPLIES_C.
  apply H_A_IMPLIES_B.
  apply H_A.
Qed.


Lemma Le :
  forall A B C: Prop,
    (A \/ B -> C) -> (A -> C) \/ (B -> C).
Proof.
  intros A B C.
  intro H_A_or_B_implies_C.
  left.
  intro H_A.
  apply H_A_or_B_implies_C.
  left.
  apply H_A.

  Restart.

  intros A B C.
  intro H_A_or_B_implies_C.
  right.
  intro H_B.
  apply H_A_or_B_implies_C.
  right.
  apply H_B.
Qed.

(* CANT MAKE THIS ONE WORK *)
Lemma Le' :
  forall A B C: Prop,
    (A -> C) \/ (B -> C) -> (A \/ B -> C).
Proof.
Admitted.


Lemma Lf :
  forall A B C: Prop,
    (A \/ B -> C) -> (A -> C) /\ (B -> C).
Proof.
  intros A B C.
  intro H_A_OR_B_IMPLIES_C.
  split.
  intro H_A.
  apply H_A_OR_B_IMPLIES_C.
  left.
  apply H_A.
  intro H_B.
  apply H_A_OR_B_IMPLIES_C.
  right.
  apply H_B.
Qed.


Lemma Lf' :
  forall A B C: Prop,
    (A -> C) /\ (B -> C) -> (A \/ B -> C).
Proof.
  intros A B C.
  intro H_A_OR_B_IMPLIES_C.
  destruct H_A_OR_B_IMPLIES_C as [H_P1 H_P2].
  intro H_A_OR_B.
  destruct H_A_OR_B.
  apply H_P1.
  apply H.
  apply H_P2.
  apply H.
Qed.

Lemma Lg :
  forall A B C: Prop,
    (A /\ B -> C) -> (A -> C) \/ (B -> C).
Proof.
Admitted.






(* TODO: Better naming *)
Lemma Lg' :
  forall A B C: Prop,
    (A -> C) \/ (B -> C) -> (A /\ B -> C).
Proof.
  intros A B C.
  intro H_A_OR_B_IMPLIES_C.
  destruct H_A_OR_B_IMPLIES_C.
  intro H_A_AND_B.
  destruct H_A_AND_B.
  apply H.
  apply H0.
  intro H_A_AND_B.
  destruct H_A_AND_B.
  apply H.
  apply H1.
Qed.



Lemma Lh :
  forall A B C: Prop,
    (A /\ B -> C) -> (A -> C) /\ (B -> C).
Proof.
Admitted.


Lemma Lh' :
  forall A B C: Prop,
    (A -> C) /\ (B -> C) -> (A /\ B -> C).
Proof.
  intros A B C.
  intro H_A_AND_B_IMPLIES_C.
  destruct H_A_AND_B_IMPLIES_C.
  intro H_A_AND_B.
  destruct H_A_AND_B.
  apply H.
  apply H1.
Qed.


(* ********** *)

Lemma distributivity_of_disjunction_over_conjunction:
  forall A B C : Prop,
    A \/ (B /\ C) <-> (A \/ B) /\ (A \/ C).
Proof.
  intros A B C.
  split.
  intro H_A_OR_B_AND_C.
  destruct H_A_OR_B_AND_C.
  split.
  left.
  apply H.
  left.
  apply H.
  split.
  destruct H.
  right.
  apply H.
  destruct H.
  right.
  apply H0.
  
  intro H_A_OR_B_AND_A_OR_C.
  destruct H_A_OR_B_AND_A_OR_C.
  destruct H.
  destruct H0.
  left.
  apply H.
  left.
  apply H.
  Admitted.


Lemma distributivity_of_conjunction_over_disjunction:
  forall A B C : Prop,
    A /\ (B \/ C) <-> (A /\ B) \/ (A /\ C).
Proof.
  intros A B C.
  split.
  intro H_A_AND_B_OR_C.
  destruct H_A_AND_B_OR_C.
  destruct H0.
  left.
  split.
  apply H.
  apply H0.
  right.
  split.
  apply H.
  apply H0.
  
  intro H_A_AND_B_OR_A_AND_C.
  destruct H_A_AND_B_OR_A_AND_C.
  destruct H.
  split.
  apply H.
  left.
  apply H0.
  destruct H.
  split.
  apply H.
  right.
  apply H0.
 Qed.


(* ********** *)

Lemma Curry :
  forall P Q R : Prop,
    (P /\ Q -> R) -> (P -> Q -> R).
Proof.
  intros P Q R.
  intro H_P_AND_Q_IMPLIES_R.
  intro H_P.
  intro H_Q.
  apply H_P_AND_Q_IMPLIES_R.
  split.
  apply H_P.
  apply H_Q.
Qed.


Lemma unCurry :
  forall P Q R : Prop,
    (P -> Q -> R) -> (P /\ Q -> R).
Proof.
  intros P Q R.
  intro H_P_Q_R.
  intro H_P_AND_Q.
  apply H_P_Q_R.
  destruct H_P_AND_Q.
  apply H.
  destruct H_P_AND_Q.
  apply H0.
Qed.


Lemma Curry_and_unCurry :
  forall P Q R : Prop,
    (P /\ Q -> R) <-> P -> Q -> R.
Proof.
  intros P Q R.
  split.
  apply (Curry P Q R).
  apply (unCurry P Q R).
Qed.

(* ********** *)

(* Here is how to import a Coq library about arithmetic expressions: *)

Require Import Arith.

Check plus_comm.

(*
plus_comm
     : forall n m : nat, n + m = m + n
*)

Lemma comm_a :
  forall a b c : nat,
    (a + b) + c = c + (b + a).
Proof.
  intros a b c.
  rewrite -> (plus_comm a b).
  rewrite -> (plus_comm (b + a) c).
  reflexivity.
 Qed.

Lemma comm_b :
  forall x y z : nat,
    (x + y) + z = z + (y + x).
Proof.
  intros x y z.
  apply (comm_a x y z).
Qed.

(* symmetry *)

Lemma comm_c :
  forall a b c : nat,
    c + (b + a) = (a + b) + c.
Proof.
  intros a b c.
  rewrite <- (plus_comm a b).
  rewrite <- (plus_comm (a + b) c).
  reflexivity.
Qed.

(* ********** *)

Check plus_assoc.

(*
plus_assoc
     : forall n m p : nat, n + (m + p) = n + m + p
*)

Lemma assoc_a :
  forall a b c d : nat,
    ((a + b) + c) + d = a + (b + (c + d)).
Proof.
  intros a b c d.

  rewrite -> (plus_assoc a b (c + d)).
  rewrite -> (plus_assoc (a + b) c d).
  reflexivity.
Qed.



(* ********** *)

Lemma mixed_a :
forall a b c d : nat,
    (c + (a + b)) + d = (b + (d + c)) + a.
Proof.
  intros a b c d.
  rewrite -> (plus_assoc c a b).
  rewrite -> (plus_comm (c + a + b) d).
  rewrite -> (plus_assoc d (c + a) b).
  rewrite -> (plus_assoc d c a).

  rewrite -> (plus_assoc b d c).
  rewrite -> (plus_comm (b + d + c) a).
  rewrite -> (plus_assoc a (b + d) c).
  rewrite -> (plus_assoc a b d).

  Admitted.



(* ********** *)

(* end of week_35.v *)
