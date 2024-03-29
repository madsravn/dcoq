(* week_38c_mystery_functions.v *)
(* dIFP 2014-2015, Q1, Week 38 *)
(* Olivier Danvy <danvy@cs.au.dk> *)

(* ********** *)

(* Are the following specifications unique?
   What are then the corresponding functions?

   Spend the rest of your dIFP weekly time
   to answer these questions
   for the specifications below.
   (* At least 7 specifications would be nice. *)
*)

(* ********** *)
Require Import Arith List.
Require Import unfold_tactic.

(* Helper stuff *)

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

(* Helper for later *)
Proposition plus_1_S :
  forall n : nat,
    S n = plus 1 n.
Proof.
  intro n.
  induction n as [ | n' IHn'].
  
  (* Base case: *)
    rewrite -> (plus_0_r 1).
    reflexivity.
  
  (* Inductive case: *)
    rewrite -> (unfold_plus_ic 0 (S n')).
    rewrite -> (plus_0_l (S n')).
    reflexivity.
Qed.

Proposition plus_S_1 :
  forall n : nat,
    S n = plus n 1.
Proof.
  intro.
  induction n as [ | n' IHn'].

  (* Base case: *)
    rewrite -> (plus_0_l 1).
    reflexivity.

  (* Inductive case: *)
    rewrite -> (unfold_plus_ic n' 1).
    rewrite -> (IHn').
    reflexivity.
Qed.

Lemma unfold_mult_bc :
  forall y : nat,
    0 * y = 0.
(* left-hand side in the base case
   =
   the corresponding conditional branch *)
Proof.
  unfold_tactic mult.
Qed.

Lemma unfold_mult_ic :
  forall x' y : nat,
    (S x') * y = y + (x' * y).
(* left-hand side in the inductive case
   =
   the corresponding conditional branch *)
Proof.
  unfold_tactic mult.
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


Definition specification_of_the_mystery_function_0 (f : nat -> nat) :=
  (f 0 = 1)
  /\
  (forall i j : nat,
    f (S (i + j)) = f i + f j).

Proposition there_is_only_one_mystery_function_0 :
  forall f g : nat -> nat,
    specification_of_the_mystery_function_0 f ->
    specification_of_the_mystery_function_0 g ->
    forall n : nat,
      f n = g n.
Proof.
  intros f g.
  unfold specification_of_the_mystery_function_0.  
  intros [H_mys_bc1 H_mys_ic1].
  intros [H_mys_bc2 H_mys_ic2].
  intro n.
  induction n as [ | n' IHn'].
  (* Base case: *)
    rewrite -> (H_mys_bc1).
    rewrite -> (H_mys_bc2).
    reflexivity.

  (* Inductive case: *)
    rewrite <- (plus_0_r n').
    rewrite -> (H_mys_ic1 n' 0).
    rewrite -> (H_mys_ic2 n' 0).
    rewrite -> (H_mys_bc1).
    rewrite -> (H_mys_bc2).
    rewrite -> (IHn').
    reflexivity.
Qed.

Theorem and_the_mystery_function_0_is_dot_dot_dot :
  specification_of_the_mystery_function_0 S.
Proof.

  unfold specification_of_the_mystery_function_0.
  split.
    reflexivity.

    intros i j.
    rewrite -> (plus_1_S).
    rewrite -> (plus_S_1).
    rewrite -> (plus_1_S).
    rewrite -> (plus_assoc 1 i j).
    Check(plus_1_S).
    rewrite <- (plus_1_S i).
    rewrite <- (plus_assoc (S i) j 1).
    rewrite <- (plus_S_1 j).
    reflexivity.
Qed.

(* ********** *)

Definition specification_of_the_mystery_function_1 (f : nat -> nat) :=
  (f 0 = 0)
  /\
  (forall i j : nat,
    f (i + S j) = f i + S (f j)).

Proposition there_is_only_one_mystery_function_1 :
  forall f g : nat -> nat,
    specification_of_the_mystery_function_1 f ->
    specification_of_the_mystery_function_1 g ->
    forall n : nat,
      f n = g n.
Proof.
  intros f g.
  unfold specification_of_the_mystery_function_1.
  intros [H_f_bc H_f_ic].
  intros [H_g_bc H_g_ic].
  intro n.
  induction n as [ | n' IHn'].
  
  (* Base case: *)
    rewrite -> (H_f_bc).
    rewrite -> (H_g_bc).
    reflexivity.

  (* Inductive case: *)
    rewrite <- (plus_0_l (S n')).
    rewrite -> (H_f_ic).
    rewrite -> (H_g_ic).
    rewrite -> (H_f_bc).
    rewrite -> (H_g_bc).
    rewrite (IHn').
    reflexivity.
Qed.


Theorem and_the_mystery_function_1_is_id :
  specification_of_the_mystery_function_1 id.
Proof.
  unfold specification_of_the_mystery_function_1.
  split.
  
    reflexivity.


    intros i j.
    unfold id.
    reflexivity.
Qed.

(* ********** *)

Definition specification_of_the_mystery_function_2 (f : nat -> nat) :=
  (f 0 = 0)
  /\
  (forall i j : nat,
    f (S (i + j)) = S (f i) + S (f j)).

Proposition there_is_only_one_mystery_function_2 :
  forall f g : nat -> nat,
    specification_of_the_mystery_function_2 f ->
    specification_of_the_mystery_function_2 g ->
    forall n : nat,
      f n = g n.
Proof.
  intros f g.
  unfold specification_of_the_mystery_function_2.
  intros [H_f_bc H_f_ic].
  intros [H_g_bc H_g_ic].
  intro n.
  induction n as [ | n' IHn'].
  
  (* Base case: *)

    rewrite -> (H_f_bc).
    rewrite -> (H_g_bc).
    reflexivity.

  (* Inductive case: *)
    Check(plus_n_Sm).
    rewrite <- (plus_0_l (S n')).
    rewrite <- (plus_n_Sm 0 n').
    rewrite -> (H_f_ic).
    rewrite -> (H_g_ic).
    rewrite -> (H_f_bc).
    rewrite -> (H_g_bc).
    rewrite -> (IHn').
    reflexivity.
Qed.



Theorem and_the_mystery_function_2_is_mult_2 :
  specification_of_the_mystery_function_2 (mult 2).
Proof.
  unfold specification_of_the_mystery_function_2.
  split.
  
    rewrite -> (mult_0_r 2).
    reflexivity.

    intros i j.
    rewrite -> (plus_n_Sm i j).
    rewrite <- (plus_0_r j).
    rewrite -> (plus_n_Sm j 0).
    rewrite -> (plus_assoc i j 1).
    rewrite -> (plus_0_r j).
    rewrite <- (plus_0_r (2*i)).
    rewrite -> (plus_n_Sm (2*i) 0).
    rewrite <- (plus_0_r (2*j)).
    rewrite -> (plus_n_Sm (2*j) 0).
    rewrite <- (plus_assoc i j 1).
    rewrite -> (plus_comm j 1).
    rewrite -> (plus_assoc i 1 j).
    rewrite -> (mult_plus_distr_l 2 (i+1) j).
    rewrite -> (mult_plus_distr_l 2 i 1).
    rewrite -> (plus_comm (2*j) 1).
    rewrite -> (plus_assoc (2*i+1) 1 (2*j)).
    rewrite -> (mult_1_r 2).
    Check(plus_assoc).
    rewrite <- (plus_assoc (2*i) 1 1).
    rewrite <- (plus_1_S 1).
    reflexivity.
Qed.



(* ********** *)

Definition specification_of_the_mystery_function_3 (f : nat -> nat) :=
  (f 0 = 1)
  /\
  (forall i j : nat,
    f (S (i + j)) = S (f i) + S (f j)).


Proposition there_is_only_one_mystery_function_3 :
  forall f g : nat -> nat,
    specification_of_the_mystery_function_3 f ->
    specification_of_the_mystery_function_3 g ->
    forall n : nat,
      f n = g n.
Proof.
  intros f g.
  unfold specification_of_the_mystery_function_3.
  intros [H_f_bc H_f_ic].
  intros [H_g_bc H_g_ic].
  intro n.
  induction n as [ | n' IHn'].
  
  (* Base case: *)
    
    rewrite -> (H_f_bc).
    rewrite -> (H_g_bc).
    reflexivity.
    
  
  (* Inductive case: *)

    rewrite <- (plus_0_l (S n')).
    rewrite <- (plus_n_Sm 0 n').
    rewrite -> (H_f_ic).
    rewrite -> (H_g_ic).
    rewrite -> (H_f_bc).
    rewrite -> (H_g_bc).
    rewrite -> (IHn').
    reflexivity.
Qed.


Theorem and_the_mystery_function_3_is_mult_3_plus_1 :
  specification_of_the_mystery_function_3 (fun x => (3*x +1)).
Proof.
  unfold specification_of_the_mystery_function_3.
  split.
  
    rewrite -> (mult_0_r).
    rewrite -> (plus_0_l).
    reflexivity.

    intros i j.
    rewrite -> (plus_S_1 (i + j)).
    rewrite -> (mult_plus_distr_l).
    rewrite -> (mult_plus_distr_l).
    rewrite -> (plus_S_1 (3*i + 1)).
    rewrite -> (plus_1_S (3*j + 1)).
    rewrite <- (plus_assoc (3*i) 1 1).
    rewrite <- (plus_1_S 1).
    rewrite -> (mult_1_r 3).
    rewrite <- (plus_assoc (3*i + 3*j) 3 1).
    rewrite <- (plus_S_1 3).
    rewrite -> (plus_comm (3*j) 1).
    rewrite -> (plus_assoc 1 1 (3*j)).
    rewrite <- (plus_S_1 1).
    rewrite -> (plus_assoc (3*i + 2) 2 (3 * j)).
    rewrite <- (plus_assoc (3*i) 2 2).
    rewrite <- (plus_n_Sm 2 1).
    rewrite <- (plus_n_Sm 2 0).
    rewrite -> (plus_0_r 2).
    rewrite <- (plus_assoc (3*i) 4 (3*j)).
    rewrite -> (plus_comm 4 (3*j)).
    rewrite -> (plus_assoc (3*i) (3*j) 4).
    reflexivity.
Qed.


(* ********** *)


Definition specification_of_the_mystery_function_4 (f : nat -> nat) :=
  (f 0 = 0)
  /\
  (forall i j : nat,
    f (i + j) = f i + f j).

Proposition there_is_only_one_mystery_function_4 :
  forall f g : nat -> nat,
    specification_of_the_mystery_function_4 f ->
    specification_of_the_mystery_function_4 g ->
    forall n : nat,
      f n = g n.
Proof.
  intros f g.
  unfold specification_of_the_mystery_function_4.
  intros [H_f_bc H_f_ic].
  intros [H_g_bc H_g_ic].
  intro n.
  induction n as [ | n' IHn'].
  
  (* Base case: *)
    
    rewrite -> (H_f_bc).
    rewrite -> (H_g_bc).
    reflexivity.
    
  
  (* Inductive case: *)

    rewrite -> (plus_1_S n').
    rewrite -> (H_f_ic).
    rewrite -> (H_g_ic).
    rewrite -> (plus_1_S 0).
Abort.


Theorem possible_mystery_function_4_is_plus_0 : 
  specification_of_the_mystery_function_4 (plus 0).
Proof.
  unfold specification_of_the_mystery_function_4.
  split.
    rewrite -> (plus_0_l).
    reflexivity.

    intros i j.
    rewrite ->3 (plus_0_l).
    reflexivity.
Qed.

Theorem another_possibility_for_mystery_function_4_is_mult_1 : 
  specification_of_the_mystery_function_4 (mult 1).
Proof.
  unfold specification_of_the_mystery_function_4.
  split.
    rewrite -> (mult_0_r).
    reflexivity.
    
    intros i j.
    rewrite ->3 (mult_1_l).
    reflexivity.
Qed.

Theorem and_the_mystery_function_4_is_mult_id :
  specification_of_the_mystery_function_4 id.
Proof.
  unfold specification_of_the_mystery_function_4.
  split.
  
    unfold id.
    reflexivity.

    intros i j.
    unfold id.
    reflexivity.
Qed.



(* ********** *)

Lemma binomial_2 :
  forall x y : nat,
    (x + y) * (x + y) = (x * x) + 2 * x * y + (y * y).
Proof.
  intros x y.

  rewrite -> mult_plus_distr_r.
  rewrite -> mult_plus_distr_l.
  rewrite -> mult_plus_distr_l.
  rewrite -> (mult_comm y x).
  symmetry.

  rewrite -> (unfold_mult_ic 1 x).
  rewrite -> (unfold_mult_ic 0 x).
  rewrite -> unfold_mult_bc.
  rewrite -> plus_0_r.
  rewrite -> mult_plus_distr_r.
  rewrite -> plus_assoc.
  rewrite -> plus_assoc.
  reflexivity.
Qed.

Definition specification_of_the_mystery_function_5 (f : nat -> nat) :=
  (f 0 = 0)
  /\
  (forall i : nat,
    f (S i) = S (2 * i + f i)).


Proposition there_is_only_one_mystery_function_5 :
  forall f g : nat -> nat,
    specification_of_the_mystery_function_5 f ->
    specification_of_the_mystery_function_5 g ->
    forall n : nat,
      f n = g n.
Proof.
  intros f g.
  unfold specification_of_the_mystery_function_5.
  intros [H_f_bc H_f_ic].
  intros [H_g_bc H_g_ic].
  intro n.
  induction n as [ | n' IHn'].

  (* Base case: *)
   
    rewrite -> (H_f_bc).
    rewrite -> (H_g_bc).
    reflexivity.

  (* Inductive case: *)

    rewrite -> (H_f_ic).
    rewrite -> (H_g_ic).
    rewrite (IHn').
    reflexivity.
Qed.

Theorem and_the_mystery_function_5_is_square :
  specification_of_the_mystery_function_5 (fun x => x * x).
Proof.
  unfold specification_of_the_mystery_function_5.
  split.
    rewrite -> (mult_0_r).
    reflexivity.

    intro i.
    rewrite -> (plus_1_S).
    rewrite -> (plus_1_S (2*i + i*i)).
    rewrite -> (plus_assoc 1 (2*i) (i*i)).
    rewrite <- (mult_1_r (2*i)).
    rewrite <- (mult_assoc 2 i 1).
    rewrite -> (mult_comm i 1).
    rewrite -> (mult_assoc 2 1 i).
    rewrite -> (binomial_2).
    rewrite <- (mult_1_l 1) at 5.
    reflexivity.
Qed.


(* ********** *)

Definition specification_of_the_mystery_function_6 (f : nat -> nat) :=
  (forall i j : nat,
    f (i + j) = f i + 2 * i * j + f j).


Proposition there_is_only_one_mystery_function_6 :
  forall f g : nat -> nat,
    specification_of_the_mystery_function_6 f ->
    specification_of_the_mystery_function_6 g ->
    forall n : nat,
      f n = g n.
Proof.
  intros f g.
  unfold specification_of_the_mystery_function_6.
  intros H_f H_g.
  intro n.
  induction n as [ | n' IHn'].

  (* Base case: *)
   
    rewrite <- (plus_0_l 0).
    rewrite -> (H_f).
    rewrite -> (H_g).
Abort.



Theorem and_the_mystery_function_6_is_power :
  specification_of_the_mystery_function_6 (fun x => x*x).
Proof.
  unfold specification_of_the_mystery_function_6.
  intros i j.
  apply (binomial_2).
Qed.

Lemma rewriting_in_short_form_v1 : 
  forall a b c d : nat,
    a + b + c + d = a + d + b + c.
Proof.                    
  intros a b c d.
  rewrite <- (plus_assoc a d b).
  rewrite -> (plus_comm d b).
  rewrite <- (plus_assoc a (b + d) c).
  rewrite -> (plus_comm b d).
  rewrite <- (plus_assoc d b c).
  rewrite -> (plus_comm d (b + c)).
  rewrite -> (plus_assoc a (b + c) d).
  rewrite -> (plus_assoc a b c).
  reflexivity.
Qed.


Theorem and_the_mystery_function_6_could_also_be : 
  specification_of_the_mystery_function_6 (fun x => x*x + 2*x).
Proof.
  unfold specification_of_the_mystery_function_6.
  intros i j.
  rewrite -> (binomial_2).
  rewrite -> (mult_plus_distr_l).
  rewrite -> (plus_comm (2*i) (2*j)).
  rewrite <- (plus_assoc (i*i) (2*i) (2*i*j)).
  rewrite -> (plus_comm (2*i) (2*i*j)).
  rewrite -> (plus_assoc (i*i) (2*i*j) (2*i)).
  rewrite ->2 (plus_assoc).
  rewrite -> (rewriting_in_short_form_v1 (i*i + 2*i*j) (j*j) (2*j) (2*i)).
  reflexivity.
Qed.  
  
(* ********** *)

Fixpoint exp (x n : nat)  :=
  match n with
      | 0 => 1
      | S n' => mult x (exp x n')
end.               

Lemma unfold_exp_bc :
  forall x : nat,
    exp x 0 = 1.
Proof.
  unfold_tactic exp.
Qed.

Lemma unfold_exp_ic :
  forall (x n : nat),
    exp x (S n) = mult x (exp x n).
Proof.
  unfold_tactic exp.
Qed.


Definition specification_of_the_mystery_function_7 (f : nat -> nat) :=
  (f 0 = 1)
  /\
  (forall i j : nat,
    f (S (i + j)) = 2 * f i * f j).

Proposition there_is_only_one_mystery_function_7 :
  forall f g : nat -> nat,
    specification_of_the_mystery_function_7 f ->
    specification_of_the_mystery_function_7 g ->
    forall n : nat,
      f n = g n.
Proof.
  intros f g.
  unfold specification_of_the_mystery_function_7.
  intros [H_f_bc H_f_ic].
  intros [H_g_bc H_g_ic].
  intro n.
  induction n as [ | n' IHn'].

  (* Base case: *)
   
    rewrite -> (H_f_bc).
    rewrite -> (H_g_bc).
    reflexivity.

  (* Inductive case: *)

    rewrite <- (plus_0_l (S n')).
    rewrite <- (plus_n_Sm 0 n').
    rewrite -> (H_f_ic).
    rewrite -> (H_g_ic).
    rewrite -> (IHn').
    rewrite -> (H_f_bc).
    rewrite -> (H_g_bc).
    reflexivity.
Qed.



Lemma exp_is_distributive :
  forall (x n m : nat),
    mult (exp x n) (exp x m) = exp x (n+m).
Proof.
  intros x n m.
  induction n as [ | n' IHn'].
  
  (*Base case: *)

    rewrite -> (unfold_exp_bc).
    rewrite -> (plus_0_l m).
    rewrite -> (mult_1_l).
    reflexivity.

  (* Inductive case: *)

    rewrite -> (unfold_exp_ic).
    rewrite -> (plus_1_S).
    rewrite <- (plus_assoc 1 n' m).
    rewrite <- (plus_1_S (n' +m)).
    rewrite -> (unfold_exp_ic).
    rewrite <- (IHn').
    rewrite -> (mult_assoc x (exp x n') (exp x m)).
    reflexivity.
Qed.


Theorem and_the_mystery_function_7_is_power_of_2 :
  specification_of_the_mystery_function_7 (exp 2).
Proof.
  unfold specification_of_the_mystery_function_7.
  split.
  
    rewrite -> (unfold_exp_bc).
    reflexivity.

    intros i j.
    rewrite -> (unfold_exp_ic).
    rewrite <- (mult_assoc 2 (exp 2 i) (exp 2 j)).
    rewrite -> (exp_is_distributive).
    reflexivity.
Qed.

(* ********** *)

Definition specification_of_the_mystery_function_power_8 (f : nat -> nat) :=
  (f 0 = 2)
  /\
  (forall i j : nat,
    f (S (i + j)) = f i * f j).


Proposition there_is_only_one_mystery_function_power_8 :
  forall f g : nat -> nat,
    specification_of_the_mystery_function_power_8 f ->
    specification_of_the_mystery_function_power_8 g ->
    forall n : nat,
      f n = g n.
Proof.
  intros f g.
  unfold specification_of_the_mystery_function_power_8.
  intros [H_f_bc H_f_ic].
  intros [H_g_bc H_g_ic].
  intro n.
  induction n as [ | n' IHn'].

  (* Base case: *)
   
    rewrite -> (H_f_bc).
    rewrite -> (H_g_bc).
    reflexivity.

  (* Inductive case: *)
    
    rewrite <- (plus_0_l (S n')).
    rewrite <- (plus_n_Sm 0 n').
    rewrite -> (H_f_ic).
    rewrite -> (H_g_ic).
    rewrite -> (H_f_bc).
    rewrite -> (H_g_bc).
    rewrite -> (IHn').
    reflexivity.
Qed.


Theorem and_the_mystery_function_8_is_mult_2_power_of_2 :
  specification_of_the_mystery_function_power_8 (fun x => mult 2 (exp 2 x)).
Proof.
  unfold specification_of_the_mystery_function_power_8.
  split.
  
    rewrite -> (unfold_exp_bc).
    rewrite -> (mult_1_r).
    reflexivity.


    intros i j.
    rewrite -> (unfold_exp_ic).
    rewrite -> (mult_assoc 2 2 (exp 2 (i + j))).
    rewrite <- (exp_is_distributive).
    rewrite -> (mult_assoc).
    rewrite -> (mult_assoc).
    rewrite -> (mult_comm (2 * 2) (exp 2 i)).
    rewrite -> (mult_comm 2 (exp 2 i)).
    rewrite -> (mult_assoc).
    reflexivity.
Qed.

(* ********** *)

Definition specification_of_the_mystery_function_9 (f : nat -> nat) :=
  (f 0 = 0)
  /\
  (f 1 = 1)
  /\
  (f 2 = 1)
  /\
  (forall p q : nat,
    f (S (p + q)) = f (S p) * f (S q) + f p * f q).

Proposition there_is_only_one_mystery_function_9 :
  forall f g : nat -> nat,
    specification_of_the_mystery_function_9 f ->
    specification_of_the_mystery_function_9 g ->
    forall n : nat,
      f n = g n.
Proof.
  intros f g.
  unfold specification_of_the_mystery_function_9.
  intros [H_f_bc0 [H_f_bc1 [H_f_bc2 H_f_ic]]]
         [H_g_bc0 [H_g_bc1 [H_g_bc2 H_g_ic]]].
  intro n.
  induction n as [ | | n' IH_n' IH_Sn'] using nat_ind2.
  
  (* Base case 1: *)
    rewrite -> H_f_bc0.
    rewrite -> H_g_bc0.
    reflexivity.

  (* Base case 2: *)
    rewrite -> H_f_bc1.
    rewrite -> H_g_bc1.
    reflexivity.
  
  (* Inductive case: *)
    rewrite -> (plus_1_S n').
    rewrite -> (H_f_ic 1 n').
    rewrite -> (H_g_ic 1 n').
    rewrite -> IH_n'.
    rewrite -> (H_f_bc2).
    rewrite -> (H_g_bc2).
    rewrite -> IH_Sn'.
    rewrite -> (H_f_bc1).
    rewrite -> (H_g_bc1).
    reflexivity.
Qed.


Fixpoint fib_ds (n : nat) : nat :=
  match n with
    | 0 => 0
    | S n' => match n' with
                | 0 => 1
                | S n'' => fib_ds n' + fib_ds n''
              end
  end.

Lemma unfold_fib_ds_base_case_0 :
  fib_ds 0 = 0.
Proof.
  unfold_tactic fib_ds.
Qed.

Lemma unfold_fib_ds_base_case_1 :
  fib_ds 1 = 1.
Proof.
  unfold_tactic fib_ds.
Qed.

Lemma shorthand_rewrite_with_fib : 
  forall a b c d : nat,
    (a + b) * c + a* d = a*(c + d) + b*c.
Proof.
  intros a b c d .
  rewrite -> (mult_plus_distr_r).
  rewrite <- (plus_assoc (a*c) (b*c) (a*d)).
  rewrite -> (plus_comm (b*c) (a*d)).
  rewrite -> (plus_assoc (a*c) (a*d) (b*c)).
  Check(mult_plus_distr_l).
  rewrite <- (mult_plus_distr_l a c d).
  reflexivity.
Qed.


Lemma unfold_fib_ds_induction_case :
  forall n'' : nat,
    fib_ds (S (S n'')) = fib_ds (S n'') + fib_ds n''.
Proof.
  unfold_tactic fib_ds.
Qed.

Theorem and_the_mystery_function_9_is_fib :
  specification_of_the_mystery_function_9 (fib_ds).
Proof.
  unfold specification_of_the_mystery_function_9.
  split.
  
    rewrite -> (unfold_fib_ds_base_case_0).
    reflexivity.

    split.

      rewrite -> (unfold_fib_ds_base_case_1).
      reflexivity.

      split.

        rewrite -> (unfold_fib_ds_induction_case).
        rewrite -> (unfold_fib_ds_base_case_1).
        rewrite -> (unfold_fib_ds_base_case_0).
        rewrite -> (plus_0_r).
        reflexivity.

        intros p q.
        revert p. (* To strengthen my hypothesis *)
        induction q as [ | q' IHq'].
        
        (* Base case *)
          intro p.
          rewrite -> (plus_0_r).
          rewrite -> (unfold_fib_ds_base_case_0).
          rewrite -> (unfold_fib_ds_base_case_1).
          rewrite -> (mult_0_r).
          rewrite -> (mult_1_r).
          rewrite -> (plus_0_r).
          reflexivity.

        (* Inductive case: *)
        
          intro p.
          rewrite -> (plus_1_S q') at 1.
          rewrite -> (plus_assoc p 1 q').
          rewrite <- (plus_S_1 p).
          rewrite -> (IHq' (S p)).
          rewrite ->2 (unfold_fib_ds_induction_case).
          rewrite -> (shorthand_rewrite_with_fib (fib_ds (S p)) (fib_ds p) (fib_ds (S q')) (fib_ds q')).
          reflexivity.
Qed.

(* ********** *)


Require Import Bool.

Definition specification_of_the_mystery_function_power_10 (f : nat -> bool) :=
  (f 0 = true)
  /\
  (f 1 = false)
  /\
  (forall i j : nat,
     f (i + j) = eqb (f i) (f j)).

Proposition there_is_only_one_mystery_function_power_10 :
  forall f g : nat -> bool,
    specification_of_the_mystery_function_power_10 f ->
    specification_of_the_mystery_function_power_10 g ->
    forall n : nat,
      f n = g n.
Proof.
  intros f g.
  unfold specification_of_the_mystery_function_power_10.
  intros [H_f_bc0 [H_f_bc1 H_f_ic]].
  intros [H_g_bc0 [H_g_bc1 H_g_ic]].
  intro n.
  induction n as [ | n' IHn'].
  
  (* Base case. *)
    rewrite -> (H_f_bc0).
    rewrite -> (H_g_bc0).
    reflexivity.

  (* Inductive case: *)
    rewrite -> (plus_1_S n').
    rewrite -> (H_f_ic).
    rewrite -> (H_f_bc1).
    rewrite -> (IHn').
    rewrite -> (H_g_ic).
    rewrite -> (H_g_bc1).
    reflexivity.
Qed.


Fixpoint evenp (n : nat) : bool :=
  match n with
    | 0 => true
    | S 0 => false
    | S (S n'') => evenp n''
  end.


Lemma unfold_evenp_bc0 :
  evenp 0 = true.
Proof.
  unfold_tactic evenp.
Qed.

Lemma unfold_evenp_bc1 :
  evenp 1 = false.
Proof.
  unfold_tactic evenp.
Qed.

Lemma unfold_evenp_ic :
  forall n'' : nat,
    evenp (S (S n'')) = evenp n''.
Proof.
  unfold_tactic evenp.
Qed.


Lemma about_mystery_evenp_v2 :
    forall x : nat,
      evenp (S x) = negb (evenp x).
Proof.
  intro x.
  induction x as [ | x' IHx'].

  rewrite -> (unfold_evenp_bc0).
  rewrite -> (unfold_evenp_bc1).
  unfold negb.
  reflexivity.
  
  rewrite -> (unfold_evenp_ic).
  rewrite -> (IHx').
  rewrite -> (negb_involutive).
  reflexivity.
Qed.


Lemma eqb_if_both_even_or_odd : 
  forall x y : nat, 
    eqb (evenp x) (evenp y) = eqb (evenp (S x)) (evenp (S y)).
Proof.
  intro x.
  induction x as [ | x' IHx'].

  (* Base case: *)
  
    intros [ | y'].
      rewrite -> (unfold_evenp_bc0).
      rewrite -> (unfold_evenp_bc1).
      unfold eqb.
      reflexivity.

    rewrite -> (unfold_evenp_bc1).
    rewrite -> (unfold_evenp_bc0).
    rewrite -> (unfold_evenp_ic).
    rewrite -> (about_mystery_evenp_v2 y').
    destruct (evenp y') eqn:H_y.
      unfold negb.
      unfold eqb.
      reflexivity.

    unfold negb.
    unfold eqb.
    reflexivity.

  (* Inductive case: *)

    rewrite -> (unfold_evenp_ic).
    rewrite -> (about_mystery_evenp_v2).
    intros [ | y'].

      rewrite -> (unfold_evenp_bc0).
      rewrite -> (IHx' 1).
      rewrite -> (unfold_evenp_ic).
      rewrite -> (unfold_evenp_bc0).
      rewrite -> (about_mystery_evenp_v2).
      reflexivity.
    
    rewrite <- (about_mystery_evenp_v2).
    rewrite <- (IHx' y').
    rewrite -> (unfold_evenp_ic).
    reflexivity.
Qed.




Theorem fun_theorem_about_evenp : 
  forall x y : nat,
    evenp (x + y) = eqb (evenp x) (evenp y).
Proof.
  intro x.
  induction x as [ | x' IHx'].
  
  (* Base case: *)
  
  intro y.
  rewrite -> (plus_0_l).
  rewrite -> (unfold_evenp_bc0).
  unfold eqb.
  destruct (evenp y) eqn:H_y.
    reflexivity.
  reflexivity.
  
  intros [ | y'].
  rewrite -> (unfold_evenp_bc0).
  rewrite -> (plus_0_r).
  unfold eqb.
  destruct (evenp (S x')) eqn:H_Sx'.
    reflexivity.
  reflexivity.
  rewrite -> (plus_S_1 x').
  rewrite <- (plus_assoc x' 1 (S y')).
  rewrite <- (plus_1_S (S y')).
  rewrite (IHx' (S (S y'))).
  rewrite <- (plus_S_1 x').
  rewrite -> (unfold_evenp_ic).
  rewrite -> (eqb_if_both_even_or_odd).
  reflexivity.
Qed.



Theorem and_the_mystery_function_10_is_is_evenp : 
  specification_of_the_mystery_function_power_10 evenp.
Proof.
  unfold specification_of_the_mystery_function_power_10.
  split.
  rewrite -> (unfold_evenp_bc0).
  reflexivity.
  split.
  rewrite -> (unfold_evenp_bc1).
  reflexivity.
  
  apply (fun_theorem_about_evenp).
Qed.




Definition specification_of_the_mystery_function_11 (f : nat -> nat * nat) :=
  (f 0 = (1, 0))
  /\
  (forall n' : nat,
    f (S n') = let (x, y) := f n'
               in (x + y, x)).

Fixpoint fib_co_acc (n : nat) : nat * nat :=
  match n with
    | O => (1, 0)
    | S n' => let (x, y) := fib_co_acc n'
              in (x + y, x)
  end.

Lemma unfold_fib_co_acc_base_case :
  fib_co_acc 0 = (1, 0).
Proof.
  unfold_tactic fib_co_acc.
Qed.

Lemma unfold_fib_co_acc_induction_case :
  forall n' : nat,
    fib_co_acc (S n') = let (x, y) := fib_co_acc n'
                        in (x + y, x).
Proof.
  unfold_tactic fib_co_acc.
Qed.


Proposition there_is_only_one_mystery_function_11 :
  forall f g : nat -> nat * nat,
    specification_of_the_mystery_function_11 f ->
    specification_of_the_mystery_function_11 g ->
    forall n : nat,
      f n = g n.
Proof.
  intros f g.
  unfold specification_of_the_mystery_function_11.
  intros [H_f_bc H_f_ic].
  intros [H_g_bc H_g_ic].
  intro n.
  induction n as [ | n' IHn'].
  
  (* Base case: *)
    rewrite -> (H_f_bc).
    rewrite -> (H_g_bc).
    reflexivity.
    
  (* Inductive case: *)
    rewrite -> (H_f_ic).
    rewrite -> (H_g_ic).
    rewrite -> (IHn').
    reflexivity.
Qed.    

Theorem and_the_mystery_function_11_is_power_fibonacci_accumulator :
  specification_of_the_mystery_function_11 fib_co_acc.
Proof.
  unfold specification_of_the_mystery_function_11.
  split.
    rewrite -> (unfold_fib_co_acc_base_case).
    reflexivity.

    intro n'.
    rewrite -> (unfold_fib_co_acc_induction_case).
    reflexivity.
Qed.

(* ********** *)

Fixpoint fac_co_acc (n : nat) : nat * nat :=
  match n with
    | 0 => (0, 1)
    | S n' => let (x,y) := fac_co_acc n'
              in (S x, y * S x)
end.

Compute fac_co_acc 3.

 Fixpoint split (A : Type) (ls : list A) : list A * list A :=
    match ls with
      | nil => (nil, nil)
      | h :: nil => (h :: nil, nil)
      | h1 :: h2 :: ls' =>
        let (ls1, ls2) := split A ls' in
          (h1 :: ls1, h2 :: ls2)
    end.

Check split.
Compute split nat (1 :: 2 :: 3 :: 4 :: nil).

Fixpoint fac (x : nat) :=
  match x with
    | 0 => 1
    | S x' => mult (S x') (fac x')
  end.
         

Definition fac_co_help (x : nat) : nat * nat :=
  (x, fac x).



Definition specification_of_the_mystery_function_12 (f : nat -> nat * nat) :=
  (f 0 = (0, 1))
  /\
  (forall n' : nat,
    f (S n') = let (x, y) := f n'
               in (S x, y * S x)).

Proposition there_is_only_one_mystery_function_12 :
  forall f g : nat -> nat * nat,
    specification_of_the_mystery_function_12 f ->
    specification_of_the_mystery_function_12 g ->
    forall n : nat,
      f n = g n.
Proof.
  intros f g.
  unfold specification_of_the_mystery_function_12.
  intros [H_f_bc H_f_ic].
  intros [H_g_bc H_g_ic].
  intro n.
  
  induction n as [ | n' IHn'].
  
  (* Base case: *)
    rewrite -> (H_f_bc).
    rewrite -> (H_g_bc).
    reflexivity.
  
  (* Inductive case: *)
    rewrite -> (H_f_ic).
    rewrite -> (H_g_ic).
    rewrite -> (IHn').
    reflexivity.
Qed.


Lemma unfold_fac_co_acc_base_case :
  fac_co_acc 0 = (0, 1).
Proof.
  unfold_tactic fac_co_acc.
Qed.

Lemma unfold_fac_co_acc_induction_case :
  forall n' : nat,
    fac_co_acc (S n') = let (x, y) := fac_co_acc n'
                        in (S x, y * S x).
Proof.
  unfold_tactic fac_co_acc.
Qed.

Lemma unfold_fac_co_help_base_case :
  fac_co_help 0 = (0,1).
Proof.
  unfold_tactic fac_co_help.
Qed.

Lemma unfold_fac_co_help_induction_case : 
  forall n' : nat,
    fac_co_help (S n') = (S n', (S n') * fac n').
Proof.
  unfold_tactic fac_co_help.
Qed.


Theorem and_the_mystery_function_12_is_tuple_index_and_factorial :
  specification_of_the_mystery_function_12 fac_co_acc.
Proof.
  unfold specification_of_the_mystery_function_12.
  split.
    rewrite -> (unfold_fac_co_acc_base_case).
    reflexivity.

    intro n'.
    rewrite -> (unfold_fac_co_acc_induction_case).
    reflexivity.
Qed.

Theorem we_could_also_call_it_fac_co_help : 
  specification_of_the_mystery_function_12 fac_co_help.
Proof.
  unfold specification_of_the_mystery_function_12.
  split.
    rewrite -> (unfold_fac_co_help_base_case).
    reflexivity.

    intro n'.
    rewrite -> (unfold_fac_co_help_induction_case).
    unfold fac_co_help.
    rewrite -> (mult_comm).
    reflexivity.
Qed.

(* end of week_38c_mystery_functions.v *)
