(* week_36c_mul.v *)
(* dIFP 2014-2015, Q1, Week 36 *)
(* Olivier Danvy <danvy@cs.au.dk> *)

(* ********** *)

Require Import Arith Bool.

Require Import unfold_tactic.

(* ********** *)

Notation "A === B" := (beq_nat A B) (at level 70, right associativity).

Definition unit_tests_for_multiplication (mul : nat -> nat -> nat) :=
  (mul 0 0 === 0)
  &&
  (mul 0 1 === 0)
  &&
  (mul 1 1 === 1)
  &&
  (mul 2 1 === 2)
  &&
  (mul 2 0 === 0)
  && 
  (mul 2 2 === 4)
  &&
  (mul 0 2 === 0)
  &&
  (mul 1 2 === 2).

(* Exercise 0: flesh out the unit tests above with more tests. *)

(* mult is the built-in multiplication in Coq (infix notation: * ): *)
Compute (unit_tests_for_multiplication mult).
(*
     = true
     : bool
*)

(* Exercise 1: why is there a space in the comment just above
   on the right of the infix notation for multiplication?

  Answer: It seems that when using the Notation ARG that the
  ARG is composed of tokens separated by spaces. Seeing that 
  Notation "a*b" := (mult a b) will yield a parse error. So
  I would say it's because that the definition of the infix
  operator is Notation "a * b" that we write it like that.
  Though we can still utilize the infix operator without
  the spaces it was defined with seeing that
  Compute(3*4) yields a correct response of 12.
*)

(* ********** *)

Definition specification_of_multiplication (mul : nat -> nat -> nat) :=
  (forall j : nat,
    mul O j = 0)
  /\
  (forall i' j : nat,
    mul (S i') j = j + (mul i' j)).

(* ********** *)

(* For the following exercise,
   the following lemmas from the Arith library might come handy:
   plus_0_l, plus_0_r, plus_comm, and plus_assoc.
*)

Check plus_0_l.
Check mult_0_l.

(* Helper for later *)
(* Would we rather use unfold plus or the unfold_tactic with plus? *)
Proposition plus_1_S : 
  forall n : nat,
    S n = plus 1 n.
Proof.
  intro n.
  (* unfold_tactic plus. *)
  unfold plus.
  reflexivity.
Qed.


(*
    show that 0 is left-absorbant for multiplication
    (aka mult_0_l in Arith)
*)

Proposition multiplication_bc_left :
  forall (mul : nat -> nat -> nat),
    specification_of_multiplication mul ->
    forall j : nat,
      mul 0 j = 0.
Proof.
  intro mult.
  intro S_mult.
  intro j.
  unfold specification_of_multiplication in S_mult.
  destruct S_mult as [H_mult_bc _].
  rewrite -> (H_mult_bc j).
  reflexivity.
Qed.


(*
    show that 0 is right-absorbant for multiplication
    (aka mult_0_r in Arith)
*)


Proposition multiplication_bc_right : 
  forall (mul : nat -> nat -> nat),
    specification_of_multiplication mul ->
    forall j : nat,
      mul j 0 = 0.
Proof.
  intro mult.
  intro S_mult.
  unfold specification_of_multiplication in S_mult.
  destruct S_mult as [H_mult_bc H_mult_ic].
  intro j.

  induction j as [ | n' IHn'].
  
  (* Base case: *)
  apply (H_mult_bc 0).

  (* Induction case: *)
  rewrite -> (H_mult_ic n' 0).
  rewrite -> (plus_0_l (mult n' 0)).
  apply IHn'.
Qed.

(*
   show that 1 is left-neutral for multiplication
   (aka mult_1_l in Arith) x
*)

Proposition multiplication_1_neutral_left :
  forall (mul : nat -> nat -> nat),
    specification_of_multiplication mul ->
    forall j : nat,
      mul 1 j = j.
Proof.
  intro mult.
  intro S_mult.
  unfold specification_of_multiplication in S_mult.
  destruct S_mult as [H_mult_bc H_mult_ic].
  intro j.
  rewrite -> (H_mult_ic 0 j).
  rewrite -> (H_mult_bc j).
  rewrite -> (plus_0_r j).
  reflexivity.
 Qed.

(* COULD HAVE BEEN DONE WITH INDUCTION! *)

(*
    show that 1 is right-neutral for multiplication
    (aka mult_1_r in Arith)
*)

Proposition multiplication_1_neutral_right :
  forall (mul : nat -> nat -> nat),
    specification_of_multiplication mul ->
    forall j : nat,
      mul j 1 = j.
Proof.
  intro mult.
  intro S_mult.
  unfold specification_of_multiplication in S_mult.
  destruct S_mult as [H_mult_bc H_mult_ic].
  intro j.
  induction j as [ | n' IHn'].

  (* Base case: *)
  apply (H_mult_bc 1).

  (* Induction case: *)
  rewrite -> (H_mult_ic n' 1).
  Check(IHn').
  rewrite -> (IHn').
  symmetry.
  rewrite -> (plus_1_S n').
  reflexivity.
Qed.

(*
   show that multiplication is commutative
   (aka mult_comm in Arith)
*)

Check(mult_comm).

Proposition multiplication_ic_left : 
  forall (mul : nat -> nat -> nat),
    specification_of_multiplication mul ->
    forall (x y : nat), 
      y + mul x y = mul (S x) y.
Proof.
  intro mult.
  intro S_mult.
  intros x y.
  unfold specification_of_multiplication in S_mult.
  destruct S_mult as [H_mult_bc H_mult_ic].
  rewrite -> (H_mult_ic x y).
  reflexivity.
Qed.

Proposition multiplication_ic_right :
  forall (mul : nat -> nat -> nat),
    specification_of_multiplication mul ->
    forall (x y : nat),
      x + mul x y = mul x (S y).
Proof.
  intro mult.
  intro S_mult.
  intros x y.
  assert (mul_s := S_mult).
  unfold specification_of_multiplication in S_mult.
  destruct S_mult as [H_mult_bc H_mult_ic].
  induction x as [ | n' IHn'].
  
  (* Base case: *)
  rewrite -> (H_mult_bc).
  rewrite -> (multiplication_bc_left mult mul_s (S y)).
  rewrite -> (plus_0_l 0).
  reflexivity.

  (* Induction case: *)
  rewrite -> (H_mult_ic n' y).
  rewrite -> (H_mult_ic n' (S y)).
  rewrite <- (IHn').

  rewrite -> (plus_assoc (S n') y (mult n' y)).
  rewrite -> (plus_assoc (S y) n' (mult n' y)).

  rewrite -> (plus_1_S n').
  rewrite -> (plus_1_S y).

  (* There must be an easier way to align the rest *)
  rewrite -> (plus_comm (1 + n' + y) (mult n' y)).
  rewrite -> (plus_comm (1 + y + n') (mult n' y)).
  rewrite -> (plus_comm (1 + n') y).
  rewrite -> (plus_comm 1 n').
  rewrite -> (plus_assoc y n' 1).
  rewrite -> (plus_assoc (mult n' y) (y + n') 1).

  rewrite -> (plus_comm (1 + y) n').
  rewrite -> (plus_comm 1 y).
  rewrite -> (plus_assoc n' y 1).

  rewrite -> (plus_assoc (mult n' y) (n' + y) 1).
  rewrite -> (plus_comm n' y).
  reflexivity.
Qed.



Proposition multiplication_is_commutative :
  forall (mul : nat -> nat -> nat),
    specification_of_multiplication mul ->
    forall (x y : nat),
      mul x y = mul y x.
Proof.
  intro mult.
  intro S_mult.
  assert(mul_s := S_mult).
  unfold specification_of_multiplication in S_mult.
  destruct S_mult as [H_mult_bc H_mult_ic].
  intros x y.
  induction x as [ | n' IHn'].

  (* Base case: *)

  rewrite -> (multiplication_bc_left mult mul_s y).
  rewrite -> (multiplication_bc_right mult mul_s y).
  reflexivity.


  (* Induction case: *)
  rewrite -> (H_mult_ic n' y).
  rewrite -> (IHn').
  rewrite -> (multiplication_ic_right mult mul_s y n').
  reflexivity.
Qed.

Check(mult_0_l).

(* 
 * show that the specification of multiplication is unique
 *)

Proposition there_is_only_one_multiplication : 
  forall mult1 mult2 : nat -> nat -> nat,
    specification_of_multiplication mult1 ->
    specification_of_multiplication mult2 ->
    forall x y : nat,
      mult1 x y = mult2 x y.
Proof.
  intros mult1 mult2 S_mult1 S_mult2 x y.
  induction x as [ | n' IHn'].
  rewrite -> (multiplication_bc_left mult1 S_mult1 y).
  rewrite -> (multiplication_bc_left mult2 S_mult2 y).
  reflexivity.

  rewrite <- (multiplication_ic_left mult1 S_mult1 n' y).
  rewrite <- (multiplication_ic_left mult2 S_mult2 n' y).
  rewrite -> (IHn').
  reflexivity.
Qed.


(*
   * implement multiplication,
     verify that your implementation passes the unit tests, and
     prove that your implementation satisfies the specification
*)

Fixpoint mult_v1 (x y : nat) : nat :=
  match x with
    | 0 => 0
    | S x' => y + (mult_v1 x' y)
  end.


Compute(unit_tests_for_multiplication mult_v1).

Lemma unfold_mult_v1_bc :
  forall (y: nat),
    mult_v1 0 y = 0.
Proof.
  unfold_tactic mult_v1.
Qed.

(* Is this how we would do it otherwise? *)
Lemma unfold_mult_v1_bc2 :
  forall (y: nat),
    mult_v1 0 y = 0.
Proof.
  intro y.
  unfold mult_v1.
  reflexivity.
Qed.

Lemma unfold_mult_v1_ic : 
  forall (i' j : nat),
    mult_v1 (S i') j = j + mult_v1 i' j. 
Proof.
  unfold_tactic mult_v1.
Qed.



Theorem mult_v1_satisfies_the_specification_of_multiplication : 
  specification_of_multiplication mult_v1.
Proof.
  unfold specification_of_multiplication.
  split.

  apply unfold_mult_v1_bc.

  apply unfold_mult_v1_ic.

Qed.



(* Exercise:

   * show that 0 is left-absorbant for multiplication
     (aka mult_0_l in Arith) x

   * show that 0 is right-absorbant for multiplication
     (aka mult_0_r in Arith) x

   * show that 1 is left-neutral for multiplication
     (aka mult_1_l in Arith) x

   * show that 1 is right-neutral for multiplication
     (aka mult_1_r in Arith) x

   * show that multiplication is commutative
     (aka mult_comm in Arith)

   * show that the specification of multiplication is unique

   * implement multiplication,
     verify that your implementation passes the unit tests, and
     prove that your implementation satisfies the specification
*)

(*
    show that multiplication distributes over addition on the left
    (aka mult_plus_distr_l in Arith), and
*)

Check(mult_plus_distr_l).

Proposition multiplication_plus_distribution_left :
  forall(mul : nat -> nat -> nat),
    specification_of_multiplication mul ->
    forall(x y z : nat),
      mul x (y + z) = mul x y + mul x z.
Proof.
  intro mult.
  intro S_mult.
  intros x y z.
  assert(mul_s := S_mult).
  unfold specification_of_multiplication in S_mult.
  destruct S_mult as [H_mult_bc H_mult_ic].
  induction x as [ | n' IHn'].
  rewrite -> (multiplication_bc_left mult mul_s (y + z)).
  rewrite -> (multiplication_bc_left mult mul_s y).
  rewrite -> (multiplication_bc_left mult mul_s z).
  rewrite -> (plus_0_l 0).
  reflexivity.

  rewrite -> (H_mult_ic n' (y + z)).
  rewrite -> (H_mult_ic n' y).
  rewrite -> (H_mult_ic n' z).
  rewrite -> (IHn').
  rewrite -> (plus_assoc (y + mult n' y) z (mult n' z)).
  rewrite -> (plus_assoc (y + z) (mult n' y) (mult n' z)).
  rewrite -> (plus_comm y (mult n' y)).
  Check(plus_assoc).
  rewrite <- (plus_assoc (mult n' y) y z).
  rewrite -> (plus_comm (mult n' y) (y + z)).
  reflexivity.
Qed.

(*
   show that multiplication is associative
   (aka mult_assoc in Arith),
*)

Proposition multiplication_is_associative : 
  forall(mul : nat -> nat -> nat),
    specification_of_multiplication mul ->
    forall (x y z : nat),
      mul x (mul y z) = mul (mul x y) z.
Proof.
  intro mult.
  intro S_mult.
  assert(mul_s := S_mult).
  unfold specification_of_multiplication in S_mult.
  destruct S_mult as [H_mult_bc H_mult_ic].
  intros x y z.
  induction x as [ | n' IHn'].

  (* Base case: *)
  rewrite -> (multiplication_bc_left mult mul_s (mult y z)).
  rewrite -> (multiplication_bc_left mult mul_s y).
  rewrite -> (multiplication_bc_left mult mul_s z).
  reflexivity.

  (* Induction case: *)

  rewrite -> (H_mult_ic n' (mult y z)).
  rewrite -> (H_mult_ic n' y).
  rewrite -> (IHn').
  rewrite -> (multiplication_is_commutative mult mul_s (y + mult n' y) z).
  rewrite -> (multiplication_plus_distribution_left mult mul_s z y (mult n' y)).
  rewrite -> (multiplication_is_commutative mult mul_s (mult n' y) z).
  rewrite -> (multiplication_is_commutative mult mul_s y z).
  reflexivity.
Qed.


(*
    show that multiplication distributes over addition on the right
    (aka mult_plus_distr_r in Arith).
*)

Check(mult_plus_distr_r).

Proposition multiplication_plus_distribution_right :
  forall(mul : nat -> nat -> nat),
    specification_of_multiplication mul ->
    forall (x y z : nat),
      mul (x + y) z = mul x z + mul y z.
Proof.
  intro mult.
  intro S_mult.
  assert(mul_s := S_mult).
  intros x y z.
  rewrite -> (multiplication_is_commutative mult mul_s (x + y) z).
  rewrite -> (multiplication_is_commutative mult mul_s x z).
  rewrite -> (multiplication_is_commutative mult mul_s y z).
  apply (multiplication_plus_distribution_left mult mul_s z x y).
Qed.


(* ********** *)

(* Exercise for the over-achievers:

   In no particular order,

   * show that multiplication is associative
     (aka mult_assoc in Arith),

   * show that multiplication distributes over addition on the left
     (aka mult_plus_distr_l in Arith), and

   * show that multiplication distributes over addition on the right
     (aka mult_plus_distr_r in Arith).
*)

(* ********** *)

(* Exercise for the over-achievers with time on their hands:
   repeat the exercises above with our own implementation
   of the addition function.
   (You will first need to compile week_36b_add.v with coqc.) 
*)

(*
Require Import week_36b_add.

Definition specification_of_multiplication' (mul : nat -> nat -> nat) :=
  (forall j : nat,
    mul O j = 0)
  /\
  (forall add : nat -> nat -> nat,
     specification_of_addition add ->
     forall i' j : nat,
       mul (S i') j = add j (mul i' j)).
*)

(* ********** *)

(* end of week_36c_mul.v *)
