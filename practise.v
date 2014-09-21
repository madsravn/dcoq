Require Import Arith.
Require Import "unfold_tactic".

Lemma unfold_add_v1_bc :
  forall j : nat,
    plus 0 j = j.
(* left-hand side in the base case
   =
   the corresponding conditional branch *)
Proof.
  unfold_tactic plus.
Qed.

Lemma unfold_add_v1_ic :
  forall i' j : nat,
    plus (S i') j = S (plus i' j).
(* left-hand side in the inductive case
   =
   the corresponding conditional branch *)
Proof.
  unfold_tactic plus.
Qed.


(*
Lemma unfold_add_v2_ic :
  forall i' j : nat,
    plus (S i') j = plus i' (S j).
(* left-hand side in the inductive case
   =
   the corresponding conditional branch *)
Proof.
  intros i' j.
  rewrite -> (unfold_add_v1_ic i' j).
  rewrite -> (plus_comm i' (S j)).
  rewrite -> (unfold_add_v1_ic j i').
  rewrite -> (plus_comm j i').
  reflexivity.
Qed.
*)


(* A useful lemma: *)
(*
Proposition add_v2_ic_right :
  forall i j : nat,
    plus i (S j) = S (plus i j).
Proof.

  intro i.
  induction i as [ | i' IHi'].

  intro j.
  rewrite -> unfold_add_v1_bc.
  rewrite -> unfold_add_v1_bc.
  reflexivity.

  intro j.
  rewrite -> unfold_add_v2_ic.
  rewrite -> unfold_add_v2_ic.
  rewrite -> (IHi' (S j)).
  reflexivity.
Qed.
*)

Proposition plus_1_S :
  forall n : nat,
    S n = plus 1 n.
Proof.
  intro n.
  induction n as [ | n' IHn'].
  rewrite -> (plus_0_r 1).
  reflexivity.
  rewrite -> (unfold_add_v1_ic).
  rewrite -> (plus_0_l (S n')).
  reflexivity.
Qed.



Fixpoint fac (x : nat) :=
  match x with
    | 0 => 1
    | S x' => mult (S x') (fac x')
  end.
             

Definition specification_of_the_mystery_function_12 (f : nat -> nat * nat) :=
  (f 0 = (0, 1))
  /\
  (forall n' : nat,
    f (S n') = let (x, y) := f n'
               in (S x, y * S x)).

Definition fac_co_help (x : nat) : nat * nat :=
  (x, fac x).

Compute(fac_co_help 3).