(* two_by_two_matrices.v *)
(* dIFP 2014-2015, Q1 *)
(* Teacher: Olivier Danvy <danvy@cs.au.dk> *)

(* Student name: ... *)
(* Student number: ... *)

(* ********** *)

(* The goal of this project is to study 2x2 matrices,
   along the lines of Section 5 of
     http://users-cs.au.dk/danvy/dProgSprog12/Supplementary-material/more-about-induction-proofs.pdf
*)

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



Inductive m22 : Type :=
| M22 : nat -> nat -> nat -> nat -> m22.

Definition matr1 := (M22 1 2 3 4).
Definition matr2 := (M22 2 3 4 5).

Definition nine (m1 m2 : m22) : m22 :=
  match m1 with
    | (M22 x1 x2 x3 x4) => match m2 with
        | (M22 y1 y2 y3 y4) => (M22 (x1*y1 + x2*y3) (x1*y2 + x2*y4) (x3*y1 + x4*y3) (x3*y2 + x4*y4))
     end
  end.

Definition ninetwo (m1 m2 : m22) : m22 :=
  match m1,m2 with
      | (M22 x1 x2 x3 x4), (M22 y1 y2 y3 y4) => M22 (x1*y1 + x2*y3) (x1*y2 + x2*y4) (x3*y1 + x4*y3) (x3*y2 + x4*y4)
  end.

Lemma matrix_helper : 
  forall (x1 x2 x3 x4 y1 y2 y3 y4 : nat),
    nine (M22 x1 x2 x3 x4) (M22 y1 y2 y3 y4) = M22 (x1*y1 + x2*y3) (x1*y2 + x2*y4) (x3*y1 + x4*y3) (x3*y2 + x4*y4).
Proof.
  intros x1 x2 x3 x4 y1 y2 y3 y4.
  unfold nine.
  reflexivity.
Qed.

Compute ninetwo matr1 matr2.

Compute nine matr1 matr2.



Definition identity : m22 := (M22 1 0 0 1).

Compute ninetwo identity identity.

Fixpoint exp (m : m22) (n : nat) : m22 :=
  match n with
    | 0 => identity
    | S n' => nine (exp m n') m
end.

Lemma unfold_exp_base_case : 
  forall m : m22,
    exp m 0 = identity.
Proof.
  unfold_tactic exp.
Qed.

Lemma unfold_exp_induction_case : 
  forall (m : m22) (n : nat),
    exp m (S n) = nine (exp m n) m.
Proof.
  unfold_tactic exp.
Qed.

Compute exp identity 4.


Lemma matrix_comm_help :
  forall n1 n2 n3 n4 n5 n6 n7 n8 : nat,
    n1 * (n2 * n3 + n4 * n5) + n6 * (n7 * n3 + n8 * n5) = (n1 * n2 + n6 * n7) * n3 + (n1 * n4 + n6 * n8) * n5.
Proof.
  intros n1 n2 n3 n4 n5 n6 n7 n8.
  ring.
Qed.

Lemma matrices_are_communative : 
  forall (m1 m2 m3 : m22),
    nine m1 (nine m2 m3) = nine (nine m1 m2) m3.
Proof.
  intros m1 m2 m3.
  induction m1,m2,m3 as [ ].
  rewrite ->4 matrix_helper.
  rewrite -> (matrix_comm_help n n3 n7 n4 n9 n0 n5 n6).
  rewrite -> (matrix_comm_help n n3 n8 n4 n10 n0 n5 n6).
  rewrite -> (matrix_comm_help n1 n3 n7 n4 n9 n2 n5 n6).
  rewrite -> (matrix_comm_help n1 n3 n8 n4 n10 n2 n5 n6).
  reflexivity.
Qed.


Lemma identity_matrix_is_netrual_l :
  forall m : m22,
    nine identity m = m.
Proof.
  intros [x1 x2 x3 x4].
  unfold identity.
  unfold nine.
  rewrite ->4 (mult_1_l).
  rewrite ->4 (mult_0_l).
  rewrite ->2 (plus_0_r).
  rewrite ->2 (plus_0_l).
  reflexivity.
Qed.

Lemma identity_matrix_is_netrual_r :
  forall m : m22,
    nine m identity = m.
Proof.
  intro m.
  induction m as [ ].
  unfold identity.
  unfold nine.
  rewrite ->4 (mult_1_r).
  rewrite ->4 (mult_0_r).
  rewrite ->2 (plus_0_l).
  rewrite ->2 (plus_0_r).
  reflexivity.
Qed.

Lemma proposition_14 : 
  forall (n : nat),
    exp (M22 1 1 0 1) n = (M22 1 n 0 1).
Proof.
  intro n.
  induction n as [ | n' IHn'].
  rewrite -> (unfold_exp_base_case).
  unfold identity.
  reflexivity.

  rewrite -> (unfold_exp_induction_case).
  rewrite -> (IHn').
  rewrite -> (matrix_helper).
  rewrite ->3 (mult_1_r).
  rewrite ->2 (mult_0_r).
  rewrite ->2 (plus_0_l).
  rewrite -> (plus_0_r).
  rewrite -> (plus_1_S n').
  reflexivity.
Qed.

Fixpoint exp_alt (m : m22) (n : nat) : m22 :=
  match n with
    | 0 => identity
    | S n' => nine m (exp_alt m n')
end.

Lemma unfold_exp_alt_base_case : 
  forall m : m22,
    exp_alt m 0 = identity.
Proof.
  unfold_tactic exp_alt.
Qed.

Lemma unfold_exp_alt_induction_case : 
  forall (m : m22) (n : nat),
    exp_alt m (S n) = nine m (exp_alt m n).
Proof.
  unfold_tactic exp_alt.
Qed.

Lemma proposition_14_alt : 
  forall (n : nat),
    exp_alt (M22 1 1 0 1) n = (M22 1 n 0 1).
Proof.
  intro n.
  induction n as [ | n' IHn'].
  rewrite -> (unfold_exp_alt_base_case).
  unfold identity.
  reflexivity.

  rewrite -> (unfold_exp_alt_induction_case).
  rewrite -> (IHn').
  rewrite -> (matrix_helper).
  rewrite ->3 (mult_1_l).
  rewrite ->2 (mult_0_l).
  rewrite ->2 (plus_0_l).
  rewrite -> (plus_0_r).
  rewrite -> (plus_1_S n').
  rewrite -> (plus_comm n' 1).
  reflexivity.
Qed.

Lemma proposition_29 :
  forall (m : m22) (n : nat),
    nine m (exp m n) = nine (exp m n) m.
Proof.
  intros m n.
  induction n as [ | n' IHn'].
  
  rewrite -> (unfold_exp_base_case).
  rewrite -> (identity_matrix_is_netrual_r).
  rewrite -> (identity_matrix_is_netrual_l).
  reflexivity.

  (* We want both sides *)
  rewrite -> (unfold_exp_induction_case).
  rewrite -> (matrices_are_communative).
  rewrite -> (IHn').
  reflexivity.
Qed.

Lemma proposition_31 : 
  forall (m : m22) (n : nat),
    nine m (exp_alt m n) = nine (exp_alt m n) m.
Proof.
  intros m n.
  induction n as [ | n' IHn'].
  rewrite -> (unfold_exp_alt_base_case).
  rewrite -> (identity_matrix_is_netrual_l).
  rewrite -> (identity_matrix_is_netrual_r).
  reflexivity.

  (* Again, both sides *)
  rewrite -> (unfold_exp_alt_induction_case).

  (* Sjov egenskab - her er det baglæns *)
  rewrite <- (matrices_are_communative).
  rewrite <- (IHn').
  reflexivity.
Qed.
  
Lemma coro32 : 
  forall (m : m22) (n : nat),
    exp m n = exp_alt m n.
Proof.
  intros m n.
  
  induction n as [ | n' IHn'].
  rewrite -> (unfold_exp_alt_base_case).
  rewrite -> (unfold_exp_base_case).
  reflexivity.

  rewrite -> (unfold_exp_alt_induction_case).
  rewrite -> (unfold_exp_induction_case).
  rewrite -> (IHn').
  symmetry.
  apply proposition_31.
Qed.

Lemma proposition_33_34 :
  forall n : nat,
    exp (M22 1 0 1 1) n = (M22 1 0 n 1).
Proof.
  intro n.

  induction n as [ | n' IHn'].
  rewrite -> (unfold_exp_base_case).
  unfold identity.
  reflexivity.

  rewrite -> (unfold_exp_induction_case).
  rewrite -> (IHn').
  rewrite -> (matrix_helper).
  rewrite -> (mult_0_l).
  rewrite ->2 (mult_0_r).
  rewrite ->2 (mult_1_r).
  rewrite ->2 (plus_0_r).
  rewrite -> (plus_0_l).
  rewrite -> (plus_comm n' 1).
  rewrite -> (plus_1_S n').
  reflexivity.
Qed.

Definition transpose(m : m22) : m22 :=
  match m with
    | (M22 x1 x2 x3 x4) => (M22 x1 x3 x2 x4)
  end.

Lemma transpose_is_involutive : 
  forall m : m22,
    transpose(transpose(m)) = m.
Proof.
  intro m.
  induction m as [ ].
  unfold transpose.
  reflexivity.
Qed.

Lemma transpose_is_something :
  forall (m n : m22),
    transpose(nine m n) = nine (transpose n) (transpose m).
Proof.

  intros m n.
  induction m,n as [ ].
  unfold nine.
  unfold transpose.
  rewrite -> (mult_comm n1 n5).
  rewrite -> (mult_comm).
  rewrite -> (mult_comm n2 n).
  rewrite -> (mult_comm n3 n5).
  rewrite -> (mult_comm n0 n4).
  rewrite -> (mult_comm n1 n6).
  rewrite -> (mult_comm n2 n4).
  rewrite -> (mult_comm n3 n6).
  reflexivity.
Qed.

Lemma proposition_38_transpose_and_exp_commute :
  forall (m : m22) (n : nat),
    transpose(exp m n) = exp (transpose m) n.
Proof.
  intros m n.
  induction m as [].
  induction n as [ | n' IHn'].
  rewrite -> (unfold_exp_base_case).
  rewrite -> (unfold_exp_base_case).
  unfold identity.
  unfold transpose.
  reflexivity.

  rewrite ->2 (unfold_exp_induction_case).
  rewrite <- (IHn').
  rewrite <- (transpose_is_something).
  rewrite -> (proposition_29).
  reflexivity.
Qed.


Lemma proposition_40 : 
  forall (n : nat),
    exp (transpose (M22 1 1 0 1)) n = transpose (M22 1 n 0 1).
Proof.
  intro n.
  rewrite <- (proposition_38_transpose_and_exp_commute).
  rewrite -> (proposition_14).
  reflexivity.
Qed.


(* You are asked to:

   * implement Definitions 9, 11, and 13, x

   * prove Properties 10 and 12, x

   * prove Proposition 14, x

   * implement Definition 27, x

   * solve Exercise 28, x

   * prove Proposition 29, x

   * solve Exercise 31, x

   * implement Corollary 32,

   * solve Exercise 34, x

   * implement Definition 35, x

   * prove Property 36, x

   * prove Lemma 37, x

   * prove Proposition 38, and to x

   * solve Exercise 40. x
*)

(*********** *)

Definition matf := (M22 1 1 1 0).

Compute exp matf 0. (* 1 0 0 1 *)
Compute exp matf 1. (* 1 1 1 0 *)
Compute exp matf 2. (* 2 1 1 1 *)
Compute exp matf 3. (* 3 2 2 1 *)
Compute exp matf 4. (* 5 3 3 2 *)
Compute exp matf 5. (* 8 5 5 3 *)
Compute exp matf 6. (* 13 8 8 5 *)
Compute exp matf 7. (* 21 13 13 8 *)
Compute exp matf 8. (* 34 21 21 13 *)

(* For the over-achievers:

   * solve Exercise 25.
*)

(* ********** *)

(* end of two_by_two_matrices.v *)
