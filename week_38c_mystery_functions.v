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
Require Import Arith.
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
    rewrite <- (BinInt.ZL0).
    reflexivity.
Qed.



(* ********** *)

Definition specification_of_the_mystery_function_3 (f : nat -> nat) :=
  (f 0 = 1)
  /\
  (forall i j : nat,
    f (S (i + j)) = S (f i) + S (f j)).

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

Definition square (x : nat) : nat :=
  x * x.

Lemma unfold_square :
  forall x : nat,
    square x = x * x.
Proof.
  unfold_tactic square.
Qed.

Lemma binomial_2 :
  forall x y : nat,
    square (x + y) = square x + 2 * x * y + square y.
Proof.
  intros x y.
  rewrite -> unfold_square.
  rewrite -> mult_plus_distr_r.
  rewrite -> mult_plus_distr_l.
  rewrite -> mult_plus_distr_l.
  rewrite -> (mult_comm y x).
  symmetry.
  rewrite -> unfold_square.
  rewrite -> unfold_square.
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

Theorem and_the_mystery_function_5_is_power :
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
    apply(binomial_2).
Qed.


(* ********** *)

Definition specification_of_the_mystery_function_6 (f : nat -> nat) :=
  (forall i j : nat,
    f (i + j) = f i + 2 * i * j + f j).

Theorem and_the_mystery_function_6_is_power :
  specification_of_the_mystery_function_6 (fun x => x*x).
Proof.
  unfold specification_of_the_mystery_function_6.
  intros i j.
  apply (binomial_2).
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

(* ESSENTIALLY WORTHLESS *)
Lemma about_exp :
  forall (x m : nat),
    exp x (m + 1) = x * (exp x m).
Proof.
  intros x m.
  induction m as [ | m' IHm'].
  
  (* Base case: *)
  
    rewrite -> (plus_0_l).
    rewrite -> (unfold_exp_ic).
    rewrite -> (unfold_exp_bc).
    reflexivity.

  (* Inductive case: *)
    rewrite <- (unfold_exp_ic).
    rewrite -> (plus_1_S).
    rewrite <- (plus_S_1 (1 + m')).
    reflexivity.
Qed.

Lemma exp_is_distributive :
  forall (x n m : nat),
    mult (exp x n) (exp x m) = exp x (n+m).
Proof.
  intros x n m.
  induction n as [ | n' IHn'].
  
  (* Base case: *)
  
    rewrite -> (unfold_exp_bc).
    rewrite -> (plus_0_l m).
    rewrite -> (mult_1_l).
    reflexivity.

  (* Base case: *)

    rewrite -> (unfold_exp_ic).
    rewrite -> (plus_comm (S n') m).
    rewrite -> (plus_S_1 n').
    rewrite -> (plus_assoc m n' 1).
    rewrite -> (about_exp x (m + n')).
    rewrite <- (mult_assoc x (exp x n') (exp x m)).
    rewrite -> (IHn').
    rewrite -> (plus_comm n' m).
    reflexivity.

  Restart.
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

Lemma x_is_exp_x_1 :
  forall x : nat,
    x = exp x 1.
Proof.
  intro x.
  induction x as [ | x' IHx'].
  
  (* Base case: *)

    rewrite -> (unfold_exp_ic).
    rewrite -> (mult_0_l (exp 0 0)).
    reflexivity.

  (* Inductive case: *)

    rewrite -> (unfold_exp_ic).
    rewrite -> (unfold_exp_bc).
    rewrite -> (mult_1_r).
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
        induction q as [ | q' IHq'].
        rewrite -> (plus_0_r).
        rewrite -> (unfold_fib_ds_base_case_0).
        rewrite -> (unfold_fib_ds_base_case_1).
        rewrite -> (mult_0_r).
        rewrite -> (mult_1_r).
        rewrite -> (plus_0_r).
        reflexivity.
        
        rewrite -> (unfold_fib_ds_induction_case).
        rewrite -> (plus_1_S).
        Check(plus_1_S).
        rewrite -> (plus_1_S q').
        rewrite -> (plus_comm 1 q').
        rewrite -> (plus_assoc p q' 1).
        rewrite <- (plus_S_1 (p + q')).
        rewrite <- (plus_1_S (S (p +q'))).
        rewrite -> (unfold_fib_ds_induction_case).
        
        rewrite <- (plus_S_1 q').
        Check(unfold_fib_ds_induction_case).
        rewrite <- (unfold_fib_ds_induction_case q').
(*        induction q as [ | q' IHq'].
        
        rewrite -> (plus_0_r).
        rewrite -> (unfold_fib_ds_induction_case).
        rewrite -> (unfold_fib_ds_base_case_0).
        rewrite -> (unfold_fib_ds_base_case_1).
        rewrite -> (mult_0_r).
        rewrite -> (plus_0_r).
        rewrite -> (mult_1_r).
        reflexivity.
        rewrite -> (unfold_fib_ds_induction_case p').
        rewrite -> (unfold_fib_ds_induction_case q').
        rewrite -> (plus_1_S p').
        rewrite -> (plus_1_S q').
        rewrite -> (plus_1_S (1 + p' + (1 + q'))).
        rewrite -> (plus_comm 1 q').
        rewrite -> (plus_assoc (1 +p') q' 1).
        Check(plus_assoc).
        rewrite <- (plus_assoc 1 p' q').
        rewrite <- (plus_1_S (p'+ q')).
        rewrite <- (plus_S_1 (S (p' + q'))).
        rewrite <- (plus_1_S (S (S (p' + q')))).
        rewrite -> (unfold_fib_ds_induction_case).
*)
Admitted.

(* ********** *)


Require Import Bool.

Definition specification_of_the_mystery_function_power_10 (f : nat -> bool) :=
  (f 0 = true)
  /\
  (f 1 = false)
  /\
  (forall i j : nat,
     f (i + j) = eqb (f i) (f j)).

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

Definition specification_of_evenp (evenp : nat -> bool) :=
  (evenp 0 = true) 
    /\
    (evenp 1 = false)
      /\
      (forall n'' : nat,
         evenp (S (S n'')) = evenp n'').


Lemma about_evenp :
  forall evenp : nat -> bool,
    specification_of_evenp evenp ->
    forall x : nat,
      evenp (S x) = negb (evenp x).
Proof.
  intros evenp.
  unfold specification_of_evenp.
  intros [H_0 [H_1 H_SS]].
  intro x.
  induction x as [ | x' IHx'].

  rewrite -> H_1.
  rewrite -> H_0.
  unfold negb.
  reflexivity.

  rewrite -> H_SS.
  rewrite -> IHx'.
  destruct (evenp x') eqn:H_evenp_x'.

    unfold negb.
    reflexivity.

  unfold negb.
  reflexivity.
Qed.

Lemma about_evenp_of_a_sum :
  forall evenp : nat -> bool,
    specification_of_evenp evenp ->
    forall x y : nat,
      evenp (x + y) = eqb (evenp x) (evenp y).
Proof.
  intros evenp.
  intro S_evenp.
  assert(evenp_s := S_evenp).
  unfold specification_of_evenp in S_evenp.
  destruct S_evenp as [H_0 [H_1 H_SS]].
  intro x.
  induction x as [ | x' IHx'].

  intro y.
  rewrite -> plus_0_l.
  rewrite -> H_0.
  unfold eqb.
  destruct (evenp y) eqn:H_y.
    reflexivity.
  reflexivity.

  (* Det samme som 
  intro y.
  destruct y as [ | y' ].
  *)

  intros [ | y' ].

  rewrite -> plus_0_r.
  rewrite -> H_0.
  destruct (evenp (S x')) eqn:H_evenp_Sx'.
  unfold eqb.
  reflexivity.

  unfold eqb.
  reflexivity.

  rewrite -> unfold_plus_ic.
  rewrite -> plus_comm.
  rewrite -> unfold_plus_ic.
  rewrite -> plus_comm.
  rewrite -> H_SS.
  rewrite -> IHx'.
  rewrite -> about_evenp.
  rewrite -> about_evenp.
  destruct (evenp x') eqn:H_evenp_x'.
    destruct (evenp y') eqn:H_evenp_y'.
      unfold negb.
      unfold eqb.
      reflexivity.
    unfold negb.
    unfold eqb.
    reflexivity.
  destruct (evenp y') eqn:H_evenp_y'.
    unfold negb.
    unfold eqb.
    reflexivity.
  unfold negb.
  unfold eqb.
  reflexivity.
  apply (evenp_s).
  apply (evenp_s).
Qed.

  

Theorem and_the_mystery_function_10_is_is_even :
  specification_of_the_mystery_function_power_10 evenp.
Proof.
  unfold specification_of_the_mystery_function_power_10.
  split.
  rewrite -> (unfold_evenp_bc0).
  reflexivity.
  
    split.

    rewrite -> (unfold_evenp_bc1).
    reflexivity.


    intros i j.
    apply (about_evenp_of_a_sum).
    unfold specification_of_evenp.
    split.
    apply(unfold_evenp_bc0).
    split.
    apply(unfold_evenp_bc1).
    
    apply(unfold_evenp_ic).
Qed.

Definition specification_of_the_mystery_function_11 (f : nat -> nat * nat) :=
  (f 0 = (1, 0))
  /\
  (forall n' : nat,
    f (S n') = let (x, y) := f n'
               in (x + y, x)).

(*
Theorem and_the_mystery_function_11_is_power_fibonacci_accumulator :
*)
 

(* ********** *)

Definition specification_of_the_mystery_function_12 (f : nat -> nat * nat) :=
  (f 0 = (0, 1))
  /\
  (forall n' : nat,
    f (S n') = let (x, y) := f n'
               in (S x, y * S x)).

(*
Theorem and_the_mystery_function_12_is_tuple_index_and_factorial :
*)

(* ********** *)

(* end of week_38c_mystery_functions.v *)
