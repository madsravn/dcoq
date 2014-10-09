(* filtering_lists.v *)
(* dIFP 2014-2015, Q1 *)
(* Teacher: Olivier Danvy <danvy@cs.au.dk> *)

(* Student name: ... *)
(* Student number: ... *)

(* ********** *)

(* The goal of this project is to study
   how to filter elements in or out of lists.
*)

Require Import List Bool unfold_tactic.

(* The Bool library defines
     true,
     false,
     andb (noted && in infix notation),
     orb (noted || in infix notation),
     and negb.
   It also provides the following equations:

    andb_true_l : forall b : bool, true && b = b
    andb_true_r : forall b : bool, b && true = b
   andb_false_l : forall b : bool, false && b = false
   andb_false_r : forall b : bool, b && false = false
    orb_false_l : forall b : bool, false || b = b
    orb_false_r : forall b : bool, b || false = b
     orb_true_r : forall b : bool, b || true = true
     orb_true_l : forall b : bool, true || b = true

   andb_true_iff
        : forall b1 b2 : bool, b1 && b2 = true <-> b1 = true /\ b2 = true
   andb_false_iff:
     forall b1 b2 : bool, b1 && b2 = false <-> b1 = false \/ b2 = false
   orb_false_iff
        : forall b1 b2 : bool, b1 || b2 = false <-> b1 = false /\ b2 = false
   orb_true_iff
        : forall b1 b2 : bool, b1 || b2 = true <-> b1 = true \/ b2 = true

You will also have the use of the two following unfold lemmas:
*)

Lemma unfold_negb_base_case_true :
  negb true = false.
Proof.
  unfold_tactic negb.
Qed.

Lemma unfold_negb_base_case_false :
  negb false = true.
Proof.
  unfold_tactic negb.
Qed.

(* Also, when, among the assumptions, you have
     H_foo : true = false
   remember that the command
     discriminate H_foo.
   solves the current subgoal.
*)

(* And finally, remember that
      destruct blah as [...] eqn:H_blah.
    has the niceness of adding an assumption H_blah
    that reflects the destruction.  For example,
    if foo has type bool,
      destruct foo as [ | ] eqn:H_foo.
    will successively provide
      H_foo : foo = true
    and then
      H_foo : foo = false
*)

(* ********** *)

(* All of that said, here is a specification: *)

Definition specification_of_filter_in (filter_in : (nat -> bool) -> list nat -> list nat) :=
  (forall p : nat -> bool,
     filter_in p nil = nil)
  /\
  (forall (p : nat -> bool)
          (x : nat)
          (xs' : list nat),
     p x = true ->
     filter_in p (x :: xs') = x :: (filter_in p xs'))
  /\
  (forall (p : nat -> bool)
          (x : nat)
          (xs' : list nat),
     p x = false ->
     filter_in p (x :: xs') = filter_in p xs').

(* You are asked to:

   * write unit tests for filter_in;

   * prove whether this definition specifies a unique function;

   * implement a definition of filter_in that satisfies the
     specification;

   * prove the following theorems:
*)

Theorem about_filtering_in_all_of_the_elements :
  forall filter_in : (nat -> bool) -> list nat -> list nat,
    specification_of_filter_in filter_in ->
    forall ns : list nat,
      filter_in (fun _ => true) ns = ns.
Proof.
Abort.

Theorem about_filtering_in_none_of_the_elements :
  forall filter_in : (nat -> bool) -> list nat -> list nat,
    specification_of_filter_in filter_in ->
    forall ns : list nat,
      filter_in (fun _ => false) ns = nil.
Proof.
Abort.

Theorem about_filtering_in_incrementally :
  forall filter_in : (nat -> bool) -> list nat -> list nat,
    specification_of_filter_in filter_in ->
    forall (p1 p2 : nat -> bool)
           (ns : list nat),
      filter_in p2 (filter_in p1 ns) =
      filter_in (fun x => andb (p1 x) (p2 x)) ns.
Proof.
Abort.

(* ********** *)

(* Here is another specification: *)

Definition specification_of_filter_out (filter_out : (nat -> bool) -> list nat -> list nat) :=
  (forall p : nat -> bool,
     filter_out p nil = nil)
  /\
  (forall (p : nat -> bool)
          (x : nat)
          (xs' : list nat),
     p x = true ->
     filter_out p (x :: xs') = filter_out p xs')
  /\
  (forall (p : nat -> bool)
          (x : nat)
          (xs' : list nat),
     p x = false ->
     filter_out p (x :: xs') = x :: (filter_out p xs')).

(* You are asked to:

   * write unit tests for filter_out;

   * prove whether this definition specifies a unique function;

   * implement a definition of filter_out that satisfies the
     specification;

   * prove properties that are analogue to filter_in; and to

   * prove the two following propositions:
*)

Proposition filter_out_from_filter_in :
  forall filter_in : (nat -> bool) -> list nat -> list nat,
    specification_of_filter_in filter_in ->
    specification_of_filter_out (fun p ns => filter_in (fun x => negb (p x)) ns).
Proof.
Abort.

Proposition filter_in_from_filter_out :
  forall filter_out : (nat -> bool) -> list nat -> list nat,
    specification_of_filter_out filter_out ->
    specification_of_filter_in (fun p ns => filter_out (fun x => negb (p x)) ns).
Proof.
Abort.

(* Which consequences of these propositions can you think of? *)

(* ********** *)

(* What is the result

   * of applying filter_in to the concatenation of two lists?

   * of applying filter_out to the concatenation of two lists?

   * of applying filter_in to a reversed list?

   * of applying filter_out to a reversed list?
*)

(* ********** *)

(* end of filtering_lists.v *)
