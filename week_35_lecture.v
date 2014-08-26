Lemma Identity :
  forall A : Prop,
    A -> A.
Proof.
  intro A.
  intro H_A.
  apply H_A.
Qed.

(* ASSUMPTIONS
   ==========
     GOAL
*)

Lemma Identity' : 
  forall B : Prop,
    B -> B.
Proof.
  intro B.
  intro H_B.
  apply H_B.
Qed.

Lemma Identity'' : 
  forall C : Prop,
    C -> C.
Proof.
  intro C.
  intro H_C.
  apply H_C.
Qed.


(* Freedom to choose names *)
Lemma Identity''' : 
  forall Z : Prop,
    Z -> Z.
Proof.
  intro Simon.
  intro Hypothesis_about_Simon.
  apply Hypothesis_about_Simon.
Qed.

Theorem foobar : 
  forall A B : Prop,
    A -> (B -> A).
Proof.
  intro A.
  intro B.
  intro H_A.
  intro H_B.
  apply H_A.
Qed.

Require Import Arith.

Lemma comm_a : 
  forall a b c : nat,
    (a + b) + c = c + (b + a).
Proof.
  intros a b c.
  rewrite -> (plus_comm a b). (* From the left *)
  rewrite -> (plus_comm (b + a) c).
  reflexivity.

  Restart.

  intros a b c.
  rewrite -> (plus_comm (a + b) c).
  rewrite -> (plus_comm a b).
  reflexivity.

  (* It can obviously be done in any way and from any direction *)

Qed.
