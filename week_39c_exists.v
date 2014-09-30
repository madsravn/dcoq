(* week_39c_exists.v *)
(* dIFP 2014-2015, Q1, Week 38 *)
(* Olivier Danvy <danvy@cs.au.dk> *)

(* Revised and completed version of 30 Sep 2014:

   * an unfold lemma is added for "beq_nat."

   * Theorem there_are_at_least_two_foo_s is stated properly.
*)

(* ********** *)

Require Import Arith Bool unfold_tactic.

Notation "A =n= B" := (beq_nat A B) (at level 70, right associativity).

(* ********** *)

(* The existential quantifier is written
     exists x : type,
       expression
   in Coq (just like the universal quantifier
   is written
     forall x : type,
       expression
   in Coq).

   If it appears in a goal,
   we process it with
     exists blah.
   where "blah" is a witness of existence.
   For example, if the goal is
     exists n : nat,
       S n = 1.
   then we write
     exists 0.

   If it appears as an assumption (a hypothesis) named A,
   we process it with
     destruct A as [x H].
   which will replace A with 2 assumptions:
     x : type
     H : ...
*)

(* ********** *)

(* Three useful lemmas: *)

Lemma twice_the_successor :
  forall i : nat,
    2 * S i = S (S (2 * i)).
Proof.
  intro i.
  ring. (* No time to lose (Tarney Spencer Band dixit) *)

  (* And yet again, in case it comes at the oral exam: *)

  Restart.

  intro i.
(* Search (S _ * _ = _).
   mult_succ_l: forall n m : nat, S n * m = n * m + m
   mult_1_l:    forall n : nat, 1 * n = n
*)
  (* left-hand side: *)
  rewrite -> mult_succ_l.
  rewrite -> mult_1_l.
  (* right-hand side: *)
  rewrite -> mult_succ_l.
  rewrite -> mult_1_l.
(* Search (S (_ + _) = _).  
   plus_n_Sm: forall n m : nat, S (n + m) = n + S m
*)
  rewrite -> plus_n_Sm.
(* Search (S _ + _ = _).
   plus_Snm_nSm: forall n m : nat, S n + m = n + S m
   plus_Sn_m: forall n m : nat, S n + m = S (n + m)
*)
  apply plus_Sn_m.
Qed.

Lemma unfold_beq_nat_1_0 :
  beq_nat 1 0 = false.
Proof.
  unfold_tactic beq_nat.
Qed.

(* A useful lemma,
   using an existential quantifier:
*)
Proposition a_natural_number_is_even_or_it_is_odd :
  forall n : nat,
    exists m : nat,
      n = 2 * m \/ n = S (2 * m).
Proof.
  intro n.
  induction n as [ | n' [m [IHn'_even | IHn'_odd]]].

  exists 0.
  left.
  rewrite -> mult_0_r.
  reflexivity.

  rewrite -> IHn'_even.
  exists m.
  right.
  reflexivity.

  rewrite -> IHn'_odd.
  exists (S m).
  left.
  ring.
Qed.  

(* ********** *)

(* Example: having an existential in the goal. *)

(* The following specification
   does not uniquely specify a function,
   because it doesn't say what happens
   to odd numbers:
*)
Definition specification_of_foo (foo : nat -> nat) :=
  forall n : nat,
    foo (2 * n) = n.

Definition unit_test_for_foo (candidate : nat -> nat) :=
  (candidate 0 =n= 0)
  &&
  (candidate 2 =n= 1)
  &&
  (candidate 8 =n= 4)
  .

(* ***** *)

(* First version of a function that satisfies the specification:
   even numbers are mapped to their half;
   odd numbers are mapped to their half.
*)
Fixpoint fool (n : nat) : nat :=
  match n with
    | 0 => 0
    | S 0 => 0
    | S (S n') => S (fool n')
  end.

Definition foo_v0 (n : nat) :=
  fool n.

Compute unit_test_for_foo foo_v0.
(*   = true
     : bool
*)

Compute (foo_v0 6, foo_v0 7, foo_v0 8, foo_v0 9).
(*   = (3, 3, 4, 4)
     : nat * nat * nat * nat
*)

Lemma unfold_fool_bc0 :
  fool 0 = 0.
Proof.
  unfold_tactic fool.
Qed.

Lemma unfold_fool_bc1 :
  fool 1 = 0.
Proof.
  unfold_tactic fool.
Qed.

Lemma unfold_fool_ic :
  forall n' : nat,
    fool (S (S n')) = S (fool n').
Proof.
  unfold_tactic fool.
Qed.

Theorem foo_v0_satisfies_the_specification_of_foo :
  specification_of_foo foo_v0.
Proof.
  unfold specification_of_foo.
  unfold foo_v0.
  intro n.
  induction n as [ | n' IHn'].

  rewrite -> mult_0_r.
  rewrite -> unfold_fool_bc0.
  reflexivity.

  rewrite -> twice_the_successor.
  rewrite -> unfold_fool_ic.
  rewrite -> IHn'.
  reflexivity.
Qed.

(* ***** *)

(* Second version of a function that satisfies the specification:
   even numbers are mapped to their half;
   odd numbers are mapped to their half, plus 1.
*)
Fixpoint fou (n : nat) : nat :=
  match n with
    | 0 => 0
    | S 0 => 1
    | S (S n') => S (fou n')
  end.

Definition foo_v1 (n : nat) :=
  fou n.

Compute unit_test_for_foo foo_v1.
(*   = true
     : bool
*)

Compute (foo_v1 6, foo_v1 7, foo_v1 8, foo_v1 9).
(*   = (3, 4, 4, 5)
     : nat * nat * nat * nat
*)

Lemma unfold_fou_bc0 :
  fou 0 = 0.
Proof.
  unfold_tactic fou.
Qed.

Lemma unfold_fou_bc1 :
  fou 1 = 1.
Proof.
  unfold_tactic fou.
Qed.

Lemma unfold_fou_ic :
  forall n' : nat,
    fou (S (S n')) = S (fou n').
Proof.
  unfold_tactic fou.
Qed.

Theorem foo_v1_satisfies_the_specification_of_foo :
  specification_of_foo foo_v1.
Proof.
  unfold specification_of_foo.
  unfold foo_v1.
  intro n.
  induction n as [ | n' IHn'].

  rewrite -> mult_0_r.
  rewrite -> unfold_fou_bc0.
  reflexivity.

  rewrite -> twice_the_successor.
  rewrite -> unfold_fou_ic.
  rewrite -> IHn'.
  reflexivity.
Qed.

(* ***** *)

(* Proof that specification_of_foo
   does not uniquely specify a function,
   with foo_v0 and foo_v1 as witness
   and any odd number as input:
*)
Theorem there_are_at_least_two_foo_s :
  exists f g : nat -> nat,
    specification_of_foo f
    /\
    specification_of_foo g
    /\
    exists n : nat,
      f n <> g n.
Proof.
  exists foo_v0.  (* Eureka. *)
  exists foo_v1.  (* Eureka. *)
  split.

  exact foo_v0_satisfies_the_specification_of_foo.
  
  split.

  exact foo_v1_satisfies_the_specification_of_foo.
  
  exists 1.  (* Eureka. *)
  (* left-hand side: *)
  unfold foo_v0.
  rewrite -> unfold_fool_bc1.
  (* right-hand side: *)
  unfold foo_v1.
  rewrite -> unfold_fou_bc1.
(* beq_nat_false :
   forall x y : nat, beq_nat x y = false -> x <> y *)
  apply beq_nat_false.
  exact unfold_beq_nat_1_0.
Qed.

(* ********** *)

(* The following specification
   uniquely specifies a function,
   because it says what happens
   both to even numbers and to odd numbers:
*)
Definition specification_of_bar (bar : nat -> nat) :=
  (forall n : nat,
     bar (2 * n) = n)
  /\
  (forall n : nat,
     bar (S (2 * n)) = n).

Theorem there_is_only_one_bar :
  forall f g : nat -> nat,
    specification_of_bar f ->
    specification_of_bar g ->
    forall n : nat,
      f n = g n.
Proof.
  intros f g.
  unfold specification_of_bar.
  intros [Hf_even Hf_odd] [Hg_even Hg_odd].
  intro n.
  destruct (a_natural_number_is_even_or_it_is_odd n)
        as [m [Hn_even | Hn_odd]].

  rewrite -> Hn_even.
  rewrite -> Hf_even.
  rewrite -> Hg_even.
  reflexivity.

  rewrite -> Hn_odd.
  rewrite -> Hf_odd.
  rewrite -> Hg_odd.
  reflexivity.
Qed.

Theorem foo_v0_satisfies_the_specification_of_bar :
  specification_of_bar foo_v0.
Proof.
  unfold specification_of_bar.
  unfold foo_v0.
  split.

    intro n.
    induction n as [ | n' IHn'].
  
    rewrite -> mult_0_r.
    rewrite -> unfold_fool_bc0.
    reflexivity.
  
    rewrite -> twice_the_successor.
    rewrite -> unfold_fool_ic.
    rewrite -> IHn'.
    reflexivity.

  intro n.
  induction n as [ | n' IHn'].

  rewrite -> mult_0_r.
  rewrite -> unfold_fool_bc1.
  reflexivity.

  rewrite -> twice_the_successor.
  rewrite -> unfold_fool_ic.
  rewrite -> IHn'.
  reflexivity.
Qed.

(* ********** *)

(* The following specification
   uniquely specifies a function,
   because it says what happens
   both to even numbers and to odd numbers:
*)
Definition specification_of_baz (bar : nat -> nat) :=
  (forall n : nat,
     bar (2 * n) = n)
  /\
  (forall n : nat,
     bar (S (2 * n)) = S n).

Theorem there_is_only_one_baz :
  forall f g : nat -> nat,
    specification_of_baz f ->
    specification_of_baz g ->
    forall n : nat,
      f n = g n.
Proof.
  intros f g.
  unfold specification_of_baz.
  intros [Hf_even Hf_odd] [Hg_even Hg_odd].
  intro n.
  destruct (a_natural_number_is_even_or_it_is_odd n)
        as [m [Hn_even | Hn_odd]].

  rewrite -> Hn_even.
  rewrite -> Hf_even.
  rewrite -> Hg_even.
  reflexivity.

  rewrite -> Hn_odd.
  rewrite -> Hf_odd.
  rewrite -> Hg_odd.
  reflexivity.
Qed.

Theorem foo_v1_satisfies_the_specification_of_baz :
  specification_of_baz foo_v1.
Proof.
  unfold specification_of_baz.
  unfold foo_v1.
  split.

    intro n.
    induction n as [ | n' IHn'].
  
    rewrite -> mult_0_r.
    rewrite -> unfold_fou_bc0.
    reflexivity.
  
    rewrite -> twice_the_successor.
    rewrite -> unfold_fou_ic.
    rewrite -> IHn'.
    reflexivity.

  intro n.
  induction n as [ | n' IHn'].

  rewrite -> mult_0_r.
  rewrite -> unfold_fou_bc1.
  reflexivity.

  rewrite -> twice_the_successor.
  rewrite -> unfold_fou_ic.
  rewrite -> IHn'.
  reflexivity.
Qed.

(* ********** *)

(* end of week_39c_exists.v *)
