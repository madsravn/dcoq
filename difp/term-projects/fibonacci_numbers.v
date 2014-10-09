(* fibonacci_numbers.v *)
(* dIFP 2014-2015, Q1 *)
(* Teacher: Olivier Danvy <danvy@cs.au.dk> *)

(* Student name: ... *)
(* Student number: ... *)

(* ********** *)

(* The goal of this project is to study
   the Fibonacci function and
   properties of Fibonacci numbers. *)

(* ********** *)

Require Import Arith.
Require Import unfold_tactic.

Lemma unfold_plus_bc :
  forall j : nat,
    plus 0 j = j.
Proof.
  unfold_tactic plus.
Qed.

Lemma unfold_plus_ic :
  forall i' j : nat,
    plus (S i') j = S (plus i' j).
Proof.
  unfold_tactic plus.
Qed.

Proposition plus_1_S :
  forall n : nat,
    S n = plus 1 n.
Proof.
  intro n.
  induction n as [ | n' IHn'].
    rewrite -> (plus_0_r 1).
    reflexivity.
    
    rewrite -> (unfold_plus_ic).
    rewrite -> (plus_0_l (S n')).
    reflexivity.
Qed.



Lemma nat_ind2 :
  forall P : nat -> Prop,
    P 0 ->
    P 1 ->
    (forall i : nat,
      P i -> P (S i) -> P (S (S i))) ->
    forall n : nat,
      P n.
Proof.
  intros P H_P0 H_P1 H_PSS n.
  assert(consecutive :
           forall x : nat,
             P x /\ P (S x)).
    intro x.
    induction x as [ | x' [IHx' IHSx']].
      split.
        exact H_P0.
      exact H_P1.

      split.
        exact IHSx'.
      exact (H_PSS x' IHx' IHSx').

      destruct (consecutive n) as [ly _].

      exact ly.
Qed.



Definition square (x : nat) : nat :=
  x * x.

(* ********** *)

(* You are given the two following specifications
   of the Fibonacci function:
*)

Definition specification_of_fibonacci (fib : nat -> nat) :=
  fib 0 = 0
  /\
  fib 1 = 1
  /\
  forall n'' : nat,
    fib (S (S n'')) = fib (S n'') + fib n''.

Definition specification_of_fibonacci_alt (fib : nat -> nat) :=
  fib 0 = 0
  /\
  fib 1 = 1
  /\
  fib 2 = 1
  /\
  forall p q : nat,
    fib (S (p + q)) =
    fib (S p) * fib (S q) + fib p * fib q.

(* Prove that each of these specifications
   specifies a unique function.   
*)

Lemma specification_of_fibonacci_is_unique :
  forall (f g : nat -> nat),
    specification_of_fibonacci f ->
    specification_of_fibonacci g ->
    forall n : nat,
      f n = g n.
Proof.
  intros f g.
  unfold specification_of_fibonacci.
  intros [f0 [f1 fn]] [g0 [g1 gn]].
  intro n.
  
  induction n as [ | | n' IHn' IHSn'] using nat_ind2.

  rewrite -> f0.
  rewrite -> g0.
  reflexivity.

  rewrite -> f1.
  rewrite -> g1.
  reflexivity.

  rewrite -> fn.
  rewrite -> gn.
  rewrite -> IHn'.
  rewrite -> IHSn'.
  reflexivity.
Qed.

Lemma specification_of_fibonacci_alt_is_unique :
  forall (f g : nat -> nat),
    specification_of_fibonacci_alt f ->
    specification_of_fibonacci_alt g ->
    forall n : nat,
      f n = g n.
Proof.
  intros f g.
  unfold specification_of_fibonacci_alt.
  intros [f0 [f1 [f2 fn]]] [g0 [g1 [g2 gn]]].
  intro n.
  
  induction n as [ | | n' IHn' IHSn'] using nat_ind2.

  rewrite -> f0.
  rewrite -> g0.
  reflexivity.

  rewrite -> f1.
  rewrite -> g1.
  reflexivity.

  rewrite -> (plus_1_S).
  rewrite <- (plus_n_Sm).
  rewrite -> fn.
  rewrite -> gn.
  rewrite -> IHn'.
  rewrite -> IHSn'.
  rewrite -> f2.
  rewrite -> f1.
  rewrite -> g2.
  rewrite -> g1.
  reflexivity.
Qed.



(* If we removed the clause "fib 2 = 1" in
   specification_of_fibonacci_alt,
   would the specification still specify a unique function?
*)

Definition specification_of_fibonacci_alt_alt (fib : nat -> nat) :=
  fib 0 = 0
  /\
  fib 1 = 1
  /\
  forall p q : nat,
    fib (S (p + q)) =
    fib (S p) * fib (S q) + fib p * fib q.


Lemma specification_of_fibonacci_alt_alt_is_unique :
  forall (f g : nat -> nat),
    specification_of_fibonacci_alt_alt f ->
    specification_of_fibonacci_alt_alt g ->
    forall n : nat,
      f n = g n.
Proof.
  intros f g.
  unfold specification_of_fibonacci_alt_alt.
  intros [f0 [f1 fn]] [g0 [g1 gn]].
  intro n.
  
  induction n as [ | | n' IHn' IHSn'] using nat_ind2.

  rewrite -> f0.
  rewrite -> g0.
  reflexivity.

  rewrite -> f1.
  rewrite -> g1.
  reflexivity.

  rewrite <- (plus_0_r (S n')).
  rewrite -> fn.
  rewrite -> gn.

  Abort.
(* Hvordan skriver vi det i bevis at det ikke findes? *)



(*
   Show that these specifications are equivalent,
   i.e., prove the following proposition:
*)

Proposition equivalence_of_the_specifications_of_fibonacci:
  forall fib: nat -> nat,
    specification_of_fibonacci fib
    <->
    specification_of_fibonacci_alt fib.

(* Suppose that you have only proved
   that one of the two specifications is unique.
   Deduce that the other specification is also unique (i.e.,
   do not prove it from scratch: prove that it is a consequence
   of the uniqueness of the first specification).
*)

(* ********** *)

(* Given either of the specifications
   of the Fibonacci function above,
   prove the following propositions:
*)

Proposition about_fibonacci_numbers_whose_index_is_even :
  forall fib : nat -> nat,
    specification_of_fibonacci fib ->
    forall n : nat,
      fib (2 * (S n)) + square (fib n) =
      square (fib (S (S n))).
Proof.
  intro fib.
  unfold specification_of_fibonacci.
  intros [f0 [f1 fn]].
  intro n.
  
  induction n as [ | | n' IHn' IHSn'] using nat_ind2.
  rewrite -> (mult_1_r).
  rewrite -> f0.
  rewrite -> fn.
  rewrite -> f0.
  rewrite ->2 (plus_0_r).
  unfold square.
  rewrite -> f1.
  rewrite -> (mult_1_r).
  reflexivity.

  rewrite -> f1.
  rewrite -> (fn 1).
  rewrite -> (mult_succ_r 2).
  rewrite -> (mult_1_r).
  rewrite -> (plus_1_S 1) at 2.
  rewrite -> (plus_assoc 2 1 1).
  rewrite <- (plus_n_Sm 2 0).
  rewrite -> (plus_0_r).
  rewrite <- (plus_n_Sm 3 0).
  rewrite -> (plus_0_r).
  rewrite -> (fn 2).
  rewrite -> (fn 1).
  rewrite -> f1.
  rewrite  -> (fn 0).
  rewrite -> f1.
  rewrite -> f0.
Abort.

Proposition d_Occagne_s_identity :
  forall fib : nat -> nat,
    specification_of_fibonacci fib ->
    forall n : nat,
      fib (2 * (S n)) = fib (S n) * (fib (S (S n)) + fib n).
Proof.
  intro fib.
  unfold specification_of_fibonacci.
  intros [f0 [f1 fn]].
  intro n.
  
  induction n as [ | | n' IHn' IHSn'] using nat_ind2.
  rewrite -> (mult_1_r).
  rewrite -> f1.
  rewrite -> f0.
  rewrite -> (plus_0_r).
  rewrite -> (mult_1_l).
  reflexivity.

  



Abort.

Proposition Cassini_s_identity_for_even_numbers :
  forall fib : nat -> nat,
    specification_of_fibonacci fib ->
    forall n : nat,
      square (fib (S (2 * n))) =
      S ((fib (2 * (S n))) * (fib (2 * n))).
Proof.
Abort.

Proposition Cassini_s_identity_for_odd_numbers :
  forall fib : nat -> nat,
    specification_of_fibonacci fib ->
    forall n : nat,
      S (square (fib (2 * (S n)))) =
      (fib (S (2 * (S n)))) * (fib (S (2 * n))).
Proof.
Abort.

(* ********** *)

(* Here is the sum function from Week 37: *)

Fixpoint sum_ds (f : nat -> nat) (n : nat) : nat :=
  match n with
  | 0 => f 0
  | S n' => sum_ds f n' + f n
  end.

Definition sum  (f : nat -> nat) (n : nat) : nat :=
  sum_ds f n.

(* ********** *)

(* Given either of the specifications
   of the Fibonacci function above,
   prove the following propositions:
*)

Proposition sum_of_the_first_fibonacci_numbers :
  forall fib : nat -> nat,
    specification_of_fibonacci fib ->
    forall n : nat,
      S (sum fib n) = fib (S (S n)).
Proof.
Abort.

Proposition sum_of_the_first_fibonacci_numbers_whose_index_is_even :
  forall fib : nat -> nat,
    specification_of_fibonacci fib ->
    forall n : nat,
      S (sum (fun i => fib (2 * i)) n) = fib (S (2 * n)).
Proof.
Abort.

Proposition sum_of_the_first_fibonacci_numbers_whose_index_is_odd :
  forall fib : nat -> nat,
    specification_of_fibonacci fib ->
    forall n : nat,
      sum (fun i => fib (S (2 * i))) n = fib (2 * (S n)).
Proof.
Abort.

Proposition sum_of_the_squares_of_the_first_fibonacci_numbers :
  forall fib : nat -> nat,
    specification_of_fibonacci fib ->
    forall n : nat,
      sum (fun i => square (fib i)) n = fib n * fib (S n).
Proof.
Abort.

(* ********** *)

(* end of fibonacci_numbers.v *)
