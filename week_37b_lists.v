(* week_37b_lists.v *)
(* dIFP 2014-2015, Q1, Week 37 *)
(* Olivier Danvy <danvy@cs.au.dk> *)

(* ********** *)

(* New tactics:
   - assert (to declare a new hypothesis)
   - clear (to garbage collect the hypotheses).
*)

Require Import unfold_tactic.

Require Import Arith Bool List.

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

Compute 3 :: 2 :: 1 :: nil.
(*
     = 3 :: 2 :: 1 :: nil
     : list nat
*)

(* ********** *)

Lemma f_equal_S :
  forall x y : nat,
    x = y -> S x = S y.
Proof.
  intros x y.
  intro H_xy.
  rewrite -> H_xy.
  reflexivity.
Qed.

(* ********** *)

(* The length of a list: *)

Notation "A === B" := (beq_nat A B) (at level 70, right associativity).

Definition unit_tests_for_length_nat (length : list nat -> nat) :=
  (length nil === 0)
  &&
  (length (1 :: nil) === 1)
  &&
  (length (2 :: 1 :: nil) === 2)
  &&
  (length (3 :: 2 :: 1 :: nil) === 3)
  .

Definition unit_tests_for_length_bool (length : list bool -> nat) :=
  (length nil === 0)
  &&
  (length (true :: nil) === 1)
  &&
  (length (true :: true :: nil) === 2)
  &&
  (length (true :: true :: true :: nil) === 3)
  .

Definition specification_of_length (T : Type) (length : list T -> nat) :=
  (length nil = 0)
  /\
  (forall (x : T) (xs' : list T),
     length (x :: xs') = S (length xs')).

Theorem there_is_only_one_length :
  forall (T : Type) (length_1 length_2 : list T -> nat),
    specification_of_length T length_1 ->
    specification_of_length T length_2 ->
    forall xs : list T,
      length_1 xs = length_2 xs.
Proof.
  intros T length_1 length_2.

  unfold specification_of_length.
  intros l1 l2.
  destruct l1 as [Hbc1 Hic1].
  destruct l2 as [Hbc2 Hic2].
  (* intros [Hbc1 Hic1] [Hbc2 Hic2]. *)

  intro xs.
  induction xs as [ | x xs' IHxs'].

  (* Base case: *)
    rewrite -> Hbc1.
    rewrite -> Hbc2.
    reflexivity.

  (* Inductive case: *)
    rewrite (Hic1 x xs').
    rewrite (Hic2 x xs').
    rewrite -> IHxs'.
    reflexivity.
Qed.

(* ***** *)

(* A first implementation of length: *)

Fixpoint length_ds (T : Type) (xs : list T) : nat :=
  match xs with
    | nil => 0
    | x :: xs' => S (length_ds T xs')
  end.

Definition length_v1 (T : Type) (xs : list T) : nat :=
  length_ds T xs.

Compute unit_tests_for_length_nat (length_v1 nat).
(*
     = true
     : bool
*)

Compute unit_tests_for_length_bool (length_v1 bool).
(*
     = true
     : bool
*)

(* The canonical unfold lemmas: *)

Lemma unfold_length_ds_base_case :
  forall T : Type,
    length_ds T nil = 0.
(* left-hand side in the base case
   =
   the corresponding conditional branch *)
Proof.
  unfold_tactic length_ds.
Qed.

Lemma unfold_length_ds_induction_case :
  forall (T : Type) (x : T) (xs' : list T),
    length_ds T (x :: xs') = S (length_ds T xs').
(* left-hand side in the inductive case
   =
   the corresponding conditional branch *)
Proof.
  unfold_tactic length_v1.
Qed.

Lemma unfold_length_v1_base_case :
  forall T : Type,
    length_v1 T nil = 0.
Proof.
  unfold length_v1.
  apply (unfold_length_ds_base_case).
Qed.

Lemma unfold_length_v1_induction_case :
  forall (T : Type) (x : T) (xs' : list T),
    length_v1 T (x :: xs') = S(length_v1 T xs').
Proof.
  unfold length_v1.
  apply (unfold_length_ds_induction_case).
Qed.



Proposition length_v1_fits_the_specification_of_length :
  forall T : Type,
    specification_of_length T (length_v1 T).
Proof.
  intro T.
  unfold specification_of_length.
  split.

    rewrite -> (unfold_length_v1_base_case T).
    reflexivity.

    intros x xs'.
    rewrite -> (unfold_length_v1_induction_case T x xs').
    reflexivity.
Qed.

(* ***** *)

(* A second implementation of length: *)

Fixpoint length_acc (T : Type) (xs : list T) (a : nat) : nat :=
  match xs with
    | nil => a
    | x :: xs' => length_acc T xs' (S a)
  end.

Definition length_v2 (T : Type) (xs : list T) : nat :=
  length_acc T xs 0.

Compute unit_tests_for_length_nat (length_v2 nat).
(*
     = true
     : bool
*)

Compute unit_tests_for_length_bool (length_v2 bool).
(*
     = true
     : bool
*)

(* The canonical unfold lemmas: *)

Lemma unfold_length_acc_base_case :
  forall (T : Type) (a : nat),
    length_acc T nil a = a.
(* left-hand side in the base case
   =
   the corresponding conditional branch *)
Proof.
  unfold_tactic length_acc.
Qed.

Lemma unfold_length_acc_induction_case :
  forall (T : Type) (x : T) (xs' : list T) (a : nat),
    length_acc T (x :: xs') a = length_acc T xs' (S a).
(* left-hand side in the inductive case
   =
   the corresponding conditional branch *)
Proof.
  unfold_tactic length_acc.
Qed.

(* A useful lemma (Eureka): *)

Lemma about_length_acc :
  forall (T : Type) (xs : list T) (a : nat),
    length_acc T xs a = (length_acc T xs 0) + a.
Proof.
  intro T.
  intros xs.
  induction xs as [ | x xs' IHx'].

  (* Base case: *)
    intro a.
    rewrite -> (unfold_length_acc_base_case T a).
    rewrite -> (unfold_length_acc_base_case T 0).
    rewrite -> (plus_0_l a).
    reflexivity.

  (* Induction case: *)
    intro a.
    rewrite -> (unfold_length_acc_induction_case T x xs' a).
    rewrite -> (unfold_length_acc_induction_case T x xs' 0).
    rewrite -> (IHx' (S a)).

    rewrite -> (IHx' 1).
    rewrite -> (plus_comm (length_acc T xs' 0 + 1) a).
    rewrite -> (plus_assoc a (length_acc T xs' 0) 1).
    rewrite -> (plus_comm a (length_acc T xs' 0)).
    rewrite -> (plus_1_S a).
    rewrite -> (plus_comm 1 a).
    rewrite -> (plus_assoc (length_acc T xs' 0) a 1).
    reflexivity.
Qed.


Proposition length_v2_fits_the_specification_of_length :
  forall T : Type,
    specification_of_length T (length_v2 T).
Proof.
  intro T.
  unfold specification_of_length.
  
  split.
    unfold length_v2.
    rewrite -> (unfold_length_acc_base_case T 0).
    reflexivity.
  
    unfold length_v2.
    intros x xs'.
    rewrite -> (unfold_length_acc_induction_case T x xs' 0).
    rewrite -> (plus_1_S (length_acc T xs' 0)).
    rewrite -> (plus_comm 1 (length_acc T xs' 0)).
    rewrite <- (about_length_acc T xs' 1).
    reflexivity.
Qed.    

(* ********** *)

Fixpoint equal_list_nat (xs ys : list nat) :=
  match xs with
    | nil =>
      match ys with
        | nil => true
        | y :: ys' => false
      end
    | x :: xs' =>
      match ys with
        | nil => false
        | y :: ys' => (beq_nat x y) && (equal_list_nat xs' ys')
      end
  end.

(* ********** *)

(* Concatenating two lists: *)

Definition unit_tests_for_append_nat (append : list nat -> list nat -> list nat) :=
  (equal_list_nat (append nil
                          nil)
                  nil)
  &&
  (equal_list_nat (append (1 :: nil)
                          nil)
                  (1 :: nil))
  &&
  (equal_list_nat (append nil
                          (1 :: nil))
                  (1 :: nil))
  &&
  (equal_list_nat (append (1 :: 2 :: nil)
                          (3 :: 4 :: 5 :: nil))
                  (1 :: 2 :: 3 :: 4 :: 5 :: nil))
  .

Definition specification_of_append (T : Type) (append : list T -> list T -> list T) :=
  (forall ys : list T,
     append nil ys = ys)
  /\
  (forall (x : T) (xs' ys : list T),
     append (x :: xs') ys = x :: (append xs' ys)).

Theorem there_is_only_one_append :
  forall (T : Type) (append_1 append_2 : list T -> list T -> list T),
    specification_of_append T append_1 ->
    specification_of_append T append_2 ->
    forall xs ys : list T,
      append_1 xs ys = append_2 xs ys.
Proof.
  intro T.
  intros append1 append2.
  intro S_append1.
  intro S_append2.
  unfold specification_of_append in S_append1.
  unfold specification_of_append in S_append2.
  destruct S_append1 as [H_append_bc1 H_append_ic1].
  destruct S_append2 as [H_append_bc2 H_append_ic2].
  intros xs ys.
  induction xs as [ | x xs' IHx'].
  
  (* Base case: *)
    rewrite -> (H_append_bc1 ys).
    rewrite -> (H_append_bc2 ys).
    reflexivity.

  (* Inductive case: *)
    rewrite -> (H_append_ic1 x xs' ys).
    rewrite -> (H_append_ic2 x xs' ys).
    rewrite (IHx').
    reflexivity.
Qed.

Fixpoint append_ds (T : Type) (xs ys : list T) : list T :=
  match xs with
    | nil => ys
    | x :: xs' => x :: append_ds T xs' ys
  end.

Definition append_v1 (T : Type) (xs ys : list T) : list T :=
  append_ds T xs ys.

Compute unit_tests_for_append_nat (append_v1 nat).

(*
  = true
  : bool
*)

Lemma unfold_append_v1_base_case :
  forall (T : Type) (ys : list T),
    append_ds T nil ys = ys.
(* left-hand side in the base case
   =
   the corresponding conditional branch *)
Proof.
  unfold_tactic append_ds.
Qed.

Lemma unfold_append_v1_induction_case :
  forall (T : Type) (x : T) (xs' ys : list T),
    append_ds T (x :: xs') ys = x :: append_ds T xs' ys.
(* left-hand side in the inductive case
   =
   the corresponding conditional branch *)
Proof.
  unfold_tactic append_ds.
Qed.

Proposition append_v1_fits_the_specification_of_append :
  forall T : Type,
    specification_of_append T (append_v1 T).
Proof.
  intro T.
  unfold specification_of_append.
  split.
    intro ys.
    unfold append_v1.
    rewrite -> (unfold_append_v1_base_case T ys).
    reflexivity.

    intros x xs ys.
    unfold append_v1.
    rewrite -> (unfold_append_v1_induction_case T x xs ys).
    reflexivity.
Qed.


(* ********** *)

(* Properties:
     for all ys, append nil ys = ys
     for all xs, append xs nil = xs
     for all xs ys zs,
       append (append xs ys) zs = append xs (append ys zs)
     for all xs ys,
       length (append xs ys) = (length xs) + (length ys)
*)

(* Exercise: write a unit test that validates these properties. *)

Definition unit_tests_for_append_nat_v1 (append : list nat -> list nat -> list nat) :=
  (equal_list_nat (append nil
                          (1 :: 2 :: nil))
                  (1 :: 2 :: nil))
  &&
  (equal_list_nat (append (1 :: nil)
                          nil)
                  (1 :: nil))
  &&
  (equal_list_nat (append (append (nil) (1 :: nil)) (2 :: nil))
                  (append (nil) (append (1 :: nil) (2 :: nil))))
  &&
  ((length (append (1 :: 2 :: nil) (3 :: 4 :: 5 :: nil))) ===
                  ((length (1 :: 2 :: nil)) + (length (3 :: 4 :: 5 :: nil))))
  &&
  (equal_list_nat (append (append (1 :: 2 :: 3 :: nil) (4 :: 5 :: 6 :: nil)) (7 :: 8 :: 9 :: nil))
                  (append (1 :: 2 :: 3 :: nil) (append (4 :: 5 :: 6 :: nil) (7 :: 8 :: 9 ::nil))))
  &&
  ((length (append (1 :: 2 :: 3 :: 4 :: nil) (5 :: 6 :: 7 :: nil)) ===
           ((length (1 :: 2 :: 3 :: 4 :: nil)) + (length (5 :: 6 :: 7 :: nil)))))
  .

(* Verifying the unit tests *)
Compute unit_tests_for_append_nat_v1 (append_v1 nat).
(*
  = true
  : bool
*)

Lemma nil_is_neutral_for_append_on_the_left :
  forall (T : Type)
         (append : list T -> list T -> list T),
    specification_of_append T append ->
    forall ys : list T,
      append nil ys = ys.
Proof.
  intros T append.
  unfold specification_of_append.
  intros [Hbc Hic].
  intro ys.
  apply (Hbc ys).
Qed.

Lemma nil_is_neutral_for_append_on_the_right :
  forall (T : Type)
         (append : list T -> list T -> list T),
    specification_of_append T append ->
    forall xs : list T,
      append xs nil = xs.
Proof.
  intros T append.

  unfold specification_of_append.
  intros [Hbc Hic].

  intro xs.
  induction xs as [ | x xs' IHxs'].

  apply (Hbc nil).

  rewrite -> (Hic x xs' nil).
  rewrite -> IHxs'.
  reflexivity.
Qed.

Lemma append_is_associative :
  forall (T : Type)
         (append : list T -> list T -> list T),
    specification_of_append T append ->
    forall xs ys zs: list T,
      append (append xs ys) zs = append xs (append ys zs).
Proof.
  intros T append.

  unfold specification_of_append.
  intros [Hbc Hic].

  intros xs.
  induction xs as [ | x xs' IHxs'].

  intros ys zs.
  rewrite -> (Hbc ys).
  rewrite -> (Hbc (append ys zs)).
  reflexivity.

  intros ys zs.
  rewrite -> (Hic x xs' ys).
  rewrite -> (Hic x (append xs' ys)).
  rewrite -> (Hic x xs' (append ys zs)).
  rewrite -> (IHxs' ys zs).
  reflexivity.
Qed.

(* ********** *)

Proposition append_preserves_length :
  forall (T : Type)
         (length : list T -> nat)
         (append : list T -> list T -> list T),
    specification_of_length T length ->
    specification_of_append T append ->
    forall xs ys : list T,
      length (append xs ys) = (length xs) + (length ys).
Proof.
  intros T length append.

  unfold specification_of_length.
  intros [H_length_bc H_length_ic].

  unfold specification_of_append.
  intros [H_append_bc H_append_ic].

  intro xs.
  induction xs as [ | x xs' IHxs'].

  (* Base case: *)
    intro ys.
    rewrite -> (H_append_bc ys).
    rewrite -> H_length_bc.
    rewrite -> plus_0_l.
    reflexivity.

  (* Inductive case: *)
    intro ys.
    rewrite -> (H_append_ic x xs' ys).
    rewrite -> (H_length_ic x (append xs' ys)).
    rewrite -> (IHxs' ys).
    rewrite -> (H_length_ic x xs').
    symmetry.
    rewrite -> (plus_Sn_m (length xs') (length ys)).
    reflexivity.
Qed.

(* ********** *)

(* Reversing a list: *)

Definition unit_tests_for_reverse_nat (reverse : list nat -> list nat) :=
  (equal_list_nat (reverse nil)
                  nil)
  &&
  (equal_list_nat (reverse (1 :: nil))
                  (1 :: nil))
  &&
  (equal_list_nat (reverse (1 :: 2 :: nil))
                  (2 :: 1 :: nil))
  &&
  (equal_list_nat (reverse (1 :: 2 :: 3 :: nil))
                  (3 :: 2 :: 1 :: nil))
  .

Definition specification_of_reverse (T : Type) (reverse : list T -> list T) :=
  forall (append : list T -> list T -> list T),
    specification_of_append T append ->
    (reverse nil = nil)
    /\
    (forall (x : T) (xs' : list T),
       reverse (x :: xs') = append (reverse xs') (x :: nil)).

Theorem there_is_only_one_reverse :
  forall (T : Type)
         (append : list T -> list T -> list T),
    specification_of_append T append ->
    forall reverse_1 reverse_2 : list T -> list T,
      specification_of_reverse T reverse_1 ->
      specification_of_reverse T reverse_2 ->
      forall xs : list T,
        reverse_1 xs = reverse_2 xs.
Proof.
  intro T.
  intro append.
  intro S_append.
  intros rev1 rev2.
  intro S_rev1.
  intro S_rev2.
  intro xs.
  unfold specification_of_reverse in S_rev1.
  unfold specification_of_reverse in S_rev2.
  destruct (S_rev1 append S_append) as [H_rev_bc1 H_rev_ic1].
  destruct (S_rev2 append S_append) as [H_rev_bc2 H_rev_ic2].
  clear S_rev1.
  clear S_rev2.
  induction xs as [ | x' xs' IHxs'].

  (* Base case: *)
    rewrite -> (H_rev_bc1).
    rewrite -> (H_rev_bc2).
    reflexivity.

  (* Inductive case: *)
    unfold specification_of_append in S_append.
    destruct S_append as [H_app_bc H_app_ic].
    rewrite -> (H_rev_ic1 x' xs').
    rewrite -> (H_rev_ic2 x' xs').
    rewrite -> (IHxs').
    reflexivity.
Qed.

(* ***** *)

(* An implementation of reverse: *)

Fixpoint reverse_ds (T : Type) (xs : list T) : list T :=
  match xs with
    | nil => nil
    | x :: xs' => append_v1 T (reverse_ds T xs') (x :: nil)
  end.

Definition reverse_v1 (T : Type) (xs : list T) : list T :=
  reverse_ds T xs.

Compute unit_tests_for_reverse_nat (reverse_v1 nat).

Lemma unfold_reverse_ds_base_case :
  forall (T : Type),
    reverse_ds T nil = nil.
(* left-hand side in the base case
   =
   the corresponding conditional branch *)
Proof.
  unfold_tactic reverse_ds.
Qed.

Lemma unfold_reverse_v1_base_case :
  forall (T : Type),
    reverse_v1 T nil = nil.
Proof.
  unfold reverse_v1.
  apply (unfold_reverse_ds_base_case).
Qed.

Lemma unfold_reverse_ds_induction_case :
  forall (T : Type)
         (x : T)
         (xs' : list T),
    reverse_ds T (x :: xs') =
    append_v1 T (reverse_ds T xs') (x :: nil).
(* left-hand side in the inductive case
   =
   the corresponding conditional branch *)
Proof.
  unfold_tactic reverse_ds.
Qed.

Lemma unfold_reverse_v1_induction_case :
  forall (T : Type)
         (x : T)
         (xs' : list T),
    reverse_v1 T (x :: xs') = 
    append_v1 T (reverse_v1 T xs') (x :: nil).
Proof.
  unfold reverse_v1.
  apply (unfold_reverse_ds_induction_case).
Qed.


Proposition reverse_v1_fits_the_specification_of_reverse :
  forall T : Type,
    specification_of_reverse T (reverse_v1 T).
Proof.
  intro T.
  unfold specification_of_reverse.
  intro append.
  intro S_append.
  split.

    rewrite -> (unfold_reverse_v1_base_case T).
    reflexivity.


    intros x xs.
    rewrite -> (there_is_only_one_append 
                  T append
                  (append_v1 T)
                  S_append
                  (append_v1_fits_the_specification_of_append T)
                  (reverse_v1 T xs) (x :: nil)).

    rewrite -> (unfold_reverse_v1_induction_case T x xs).
    reflexivity.
Qed.


(* ***** *)

(* A second implementation of reverse, with an accumulator : *)

Fixpoint reverse_acc (T : Type) (xs a : list T) : list T :=
  match xs with
    | nil => a
    | x :: xs' => reverse_acc T xs' (x :: a)
  end.

Definition reverse_v2 (T : Type) (xs : list T) :=
  reverse_acc T xs nil.

Compute unit_tests_for_reverse_nat (reverse_v2 nat).

(* A useful lemma (Eureka): *)

Lemma unfold_reverse_acc_base_case :
  forall (T : Type) (a : list T),
    reverse_acc T nil a = a.
(* left-hand side in the base case
   =
   the corresponding conditional branch *)
Proof.
  unfold_tactic reverse_acc.
Qed.

Lemma unfold_reverse_acc_induction_case :
  forall (T : Type)
         (x : T)
         (a xs' : list T),
    reverse_acc T (x :: xs') a =
    reverse_acc T xs' (x :: a).
(* left-hand side in the inductive case
   =
   the corresponding conditional branch *)
Proof.
  unfold_tactic reverse_acc.
Qed.


Lemma about_reverse_acc :
  forall (T : Type)
         (append : list T -> list T -> list T),
    specification_of_append T append ->
    forall xs a : list T,
      reverse_acc T xs a = append (reverse_acc T xs nil) a.
Proof.
  intro T.
  intro append.
  intro S_append.
  intro xs.
  assert(append_s := S_append).
  unfold specification_of_append in S_append.
  destruct S_append as [H_app_bc H_app_ic].

  induction xs as [ | x xs' IHxs'].

  (* Base case: *)

    intro a.
    rewrite -> (unfold_reverse_acc_base_case T nil).
    rewrite -> (unfold_reverse_acc_base_case T a).
    rewrite -> (H_app_bc a).
    reflexivity.

  (* Inductive case: *)
    intro a.
    rewrite -> (unfold_reverse_acc_induction_case T x nil xs').
    rewrite -> (unfold_reverse_acc_induction_case T x a xs').
    rewrite -> (IHxs' (x :: a)).
    rewrite -> (IHxs' (x :: nil)).
    rewrite -> (append_is_associative T append append_s (reverse_acc T xs' nil) (x :: nil) a). 
    rewrite -> (H_app_ic x nil a).
    rewrite -> (H_app_bc a).
    reflexivity.
Qed.



Proposition reverse_v2_fits_the_specification_of_reverse :
  forall T : Type,
    specification_of_reverse T (reverse_v2 T).
Proof.
  intro T.
  unfold specification_of_reverse.
  intro append.
  intro S_append.
  split.
  
    unfold reverse_v2.
    rewrite -> (unfold_reverse_acc_base_case T nil).
    reflexivity.

    intros x xs'.
    unfold reverse_v2.
    rewrite -> (unfold_reverse_acc_induction_case T x nil xs').
    apply (about_reverse_acc T append S_append xs' (x :: nil)).
Qed.

(* ********** *)

(* Properties:
     for all xs,
       length xs = length (reverse xs)
     forall xs ys,
       reverse (append xs ys) = append (reverse ys) (reverse xs)
     forall xs,
       reverse (reverse xs) = xs
*)

(* Exercise: write a unit test that validates these properties. *)

Definition unit_tests_for_app_rev_len_v1 (reverse : list nat -> list nat) (append : list nat -> list nat -> list nat) (length : list nat -> nat) :=
  (length (1 :: 2 :: 3 :: nil) === length (reverse (1 :: 2 :: 3 :: nil)))
  &&
  (length (1 :: 2 :: 3 :: 4 :: nil) === length (reverse (1 :: 2 :: 3 :: 4 :: nil)))
  &&
  (equal_list_nat (reverse (append (1 :: 2 :: nil) (3 :: 4 :: nil))) 
                  (append (reverse (3 :: 4 :: nil)) (reverse (1 :: 2 :: nil))))
  &&
  (equal_list_nat (reverse (append (1 :: 2 :: 3 :: nil) (4 :: 5 :: 6 :: nil)))
                  (append (reverse (4 :: 5 :: 6 :: nil)) (reverse (1 :: 2 :: 3 :: nil))))
  &&
  (equal_list_nat (reverse (append (3 :: 4 :: 7 :: nil) (1 :: 2 :: 5 :: 6 :: nil)))
                  (append (reverse (1 :: 2 :: 5 :: 6 :: nil)) (reverse (3 :: 4 :: 7 :: nil))))
  &&
  (equal_list_nat (reverse (append (nil) (1 :: nil)))
                  (append (reverse (nil)) (reverse (1 :: nil))))
  &&
  (equal_list_nat (reverse (reverse (1 :: 2 :: 3 :: 4 :: 5 :: nil))) (1 :: 2 :: 3 :: 4 :: 5 :: nil))
  &&
  (equal_list_nat (reverse (reverse (1 :: 2 :: 3 :: 4 :: nil))) (1 :: 2 :: 3 :: 4 :: nil))
  .


Compute unit_tests_for_app_rev_len_v1 (reverse_v1 nat) (append_v1 nat) (length_v1 nat).
(*
  = true
  : bool
*)

Proposition reverse_preserves_length :
  forall (T : Type)
         (length : list T -> nat)
         (append : list T -> list T -> list T)
         (reverse : list T -> list T),
    specification_of_length T length ->
    specification_of_append T append ->
    specification_of_reverse T reverse ->
    forall xs : list T,
      length xs = length (reverse xs).
Proof.
  intro T.
  intro length.
  intro append.
  intro reverse.
  intro S_length.
  intro S_append.
  intro S_reverse.
  intro xs.

  assert(length_s := S_length).
  assert(append_s := S_append).
  assert(reverse_s := S_reverse).
  unfold specification_of_reverse in S_reverse.
  destruct (S_reverse append S_append) as [H_rev_bc H_rev_ic].
  unfold specification_of_length in S_length.
  destruct S_length as [H_len_bc H_len_ic].
  unfold specification_of_append in S_append.
  destruct S_append as [H_app_bc H_app_ic].
  clear S_reverse.
  
  induction xs as [ | x xs' IHxs'].

  (* Base case. *)
    rewrite -> (H_rev_bc).
    reflexivity.

  (* Inductive case: *)
    rewrite -> (H_rev_ic x xs').
    rewrite -> (append_preserves_length T length append length_s append_s (reverse xs') (x :: nil)).
    rewrite <- (IHxs').
    rewrite -> (H_len_ic x nil).
    rewrite -> (H_len_bc).
    rewrite -> (H_len_ic x xs').
    rewrite -> (plus_S_1 (length xs')).
    reflexivity.
Qed.
  

Proposition reverse_preserves_append_sort_of :
  forall (T : Type)
         (append : list T -> list T -> list T)
         (reverse : list T -> list T),
    specification_of_append T append ->
    specification_of_reverse T reverse ->
    forall xs ys : list T,
      reverse (append xs ys) = append (reverse ys) (reverse xs).
Proof.
  intro T.
  intro append.
  intro reverse.
  intro S_append.
  intro S_reverse.
  intros xs ys.
  assert(append_s := S_append).
  unfold specification_of_reverse in S_reverse.
  destruct (S_reverse append S_append) as [H_rev_bc H_rev_ic].
  unfold specification_of_append in S_append.
  destruct S_append as [H_app_bc H_app_ic].
  clear S_reverse.
  induction xs as [ | x xs' IHxs'].

  
  (* Base case: *)
    rewrite -> (H_app_bc ys).
    rewrite -> (H_rev_bc).
    rewrite -> (nil_is_neutral_for_append_on_the_right T append append_s (reverse ys)).
    reflexivity.

  (* Inductive case: *)
    rewrite -> (H_rev_ic x xs').
    rewrite <- (append_is_associative T  append append_s (reverse ys) (reverse xs') (x :: nil)).
    rewrite <- (IHxs').
    rewrite -> (H_app_ic x xs' ys).
    rewrite -> (H_rev_ic x (append xs' ys)).
    reflexivity.
Qed.

Proposition reverse_is_involutive :
  forall (T : Type)
         (append : list T -> list T -> list T)
         (reverse : list T -> list T),
    specification_of_append T append ->
    specification_of_reverse T reverse ->
    forall xs : list T,
      reverse (reverse xs) = xs.
Proof.
  intro T.
  intro append.
  intro reverse.
  intro S_append.
  intro S_reverse.
  intro xs.
  assert(append_s := S_append).
  assert(reverse_s := S_reverse).
  unfold specification_of_reverse in S_reverse.
  destruct (S_reverse append S_append) as [H_rev_bc H_rev_ic].
  clear S_reverse.
  induction xs as [ | x xs' IHxs'].

  (* Base case: *)
    rewrite -> (H_rev_bc).
    rewrite -> (H_rev_bc).
    reflexivity.

  (* Inductive case: *)
    rewrite -> (H_rev_ic x xs').
    unfold specification_of_append in S_append.
    destruct S_append as [H_app_bc H_app_ic].
    rewrite -> (reverse_preserves_append_sort_of T append reverse append_s reverse_s (reverse xs') (x :: nil)).
    rewrite ->(IHxs').
    rewrite -> (H_rev_ic x nil).
    rewrite -> (H_rev_bc).
    rewrite -> (H_app_bc).
    rewrite -> (H_app_ic x nil xs').
    rewrite -> (H_app_bc xs').
    reflexivity.
Qed.

(* ********** *)

(* Mapping a function over the elements of a list: *)

Definition unit_tests_for_map_nat (map : (nat -> nat) -> list nat -> list nat) :=
  (equal_list_nat (map (fun n => n)
                       nil)
                  nil)
  &&
  (equal_list_nat (map (fun n => n)
                       (1 :: nil))
                  (1 :: nil))
  &&
  (equal_list_nat (map (fun n => n)
                       (1 :: 2 :: 3 :: nil))
                  (1 :: 2 :: 3 :: nil))
  &&
  (equal_list_nat (map (fun n => S n)
                       nil)
                  nil)
  &&
  (equal_list_nat (map (fun n => S n)
                       (1 :: nil))
                  (2 :: nil))
  &&
  (equal_list_nat (map (fun n => S n)
                       (1 :: 2 :: 3 :: nil))
                  (2 :: 3 :: 4 :: nil))
  &&
  (equal_list_nat (map (fun n => n*n)
                       (1 :: 2 :: 3 :: nil))
                  (1 :: 4 :: 9 :: nil))
  &&
  (equal_list_nat (map (fun n => n + n)
                       (1 :: 2 :: 3 :: 4 :: nil))
                  (map (fun n => 2*n)
                       (1 :: 2 :: 3 :: 4 :: nil)))
  &&
  (equal_list_nat (map (fun n => n + 3)
                       (1 :: 2 :: 3 :: 4 :: nil))
                  (4 :: 5 :: 6 :: 7 :: nil))
                  
  .

(* Exercise: add more tests. *)

Definition specification_of_map (T1 T2 : Type) (map : (T1 -> T2) -> list T1 -> list T2) :=
  (forall f : T1 -> T2,
     map f nil = nil)
  /\
  (forall (f : T1 -> T2) (x : T1) (xs' : list T1),
     map f (x :: xs') = (f x) :: (map f xs')).

Theorem there_is_only_one_map :
  forall (T1 T2 : Type)
         (map_1 map_2 : (T1 -> T2) -> list T1 -> list T2),
    specification_of_map T1 T2 map_1 ->
    specification_of_map T1 T2 map_2 ->
    forall (f : T1 -> T2)
           (xs : list T1),
      map_1 f xs = map_2 f xs.
Proof.
  intros T1 T2.
  intros map1 map2.
  intros S_map1 S_map2.
  intro f.
  intro xs.

  unfold specification_of_map in S_map1.
  destruct S_map1 as [H_map_bc1 H_map_ic1].
  unfold specification_of_map in S_map2.
  destruct S_map2 as [H_map_bc2 H_map_ic2].

  induction xs as [ | x xs' IHxs'].

  (* Base case: *)
    rewrite -> (H_map_bc1).
    rewrite -> (H_map_bc2).
    reflexivity.
    
  (* Inductive case: *)
    rewrite -> (H_map_ic1 f x xs').
    rewrite -> (H_map_ic2 f x xs').
    rewrite -> (IHxs').
    reflexivity.
Qed.

(* ***** *)

(* An implementation of map: *)

Fixpoint map_ds (T1 T2 : Type) (f : T1 -> T2) (xs : list T1) : list T2 :=
  match xs with
    | nil => nil
    | x :: xs' => (f x) :: (map_ds T1 T2 f xs')
  end.

Definition map_v1 (T1 T2 : Type) (f : T1 -> T2) (xs : list T1) : list T2 :=
  map_ds T1 T2 f xs.

Compute unit_tests_for_map_nat (map_v1 nat nat).
(*
  = true
  : bool
*)


Lemma unfold_map_ds_base_case : 
  forall (T1 T2 : Type) (f : T1 -> T2),
    map_ds T1 T2 f nil = nil.
Proof.  
  unfold_tactic map_ds.
Qed.

Lemma unfold_map_v1_base_case : 
  forall (T1 T2 : Type) (f : T1 -> T2),
    map_v1 T1 T2 f nil = nil.
Proof.
  unfold map_v1.
  apply (unfold_map_ds_base_case).
Qed.

Lemma unfold_map_ds_induction_case : 
  forall (T1 T2 : Type) (f : T1 -> T2) (x : T1) (xs' : list T1),
    map_ds T1 T2 f (x :: xs') = (f x) :: (map_ds T1 T2 f xs').
Proof.
  unfold_tactic map_ds.
Qed.

Lemma unfold_map_v1_induction_case : 
  forall (T1 T2 : Type) (f : T1 -> T2) (x : T1) (xs' : list T1),
    map_v1 T1 T2 f (x :: xs') = (f x) :: (map_v1 T1 T2 f xs').
Proof.
  unfold map_v1.
  apply (unfold_map_ds_induction_case).
Qed.


Proposition map_v1_fits_the_specification_of_map :
  forall T1 T2 : Type,
    specification_of_map T1 T2 (map_v1 T1 T2).
Proof.
  intros T1 T2.
  unfold specification_of_map.
  split.
  
    intro f.
    rewrite -> (unfold_map_v1_base_case T1 T2 f).
    reflexivity.

    intro f.
    intros x xs'.
    rewrite -> (unfold_map_v1_induction_case T1 T2 f x xs').
    reflexivity.
Qed.

(* Properties:
     for all f1 f2 xs,
       map f2 (map f1 xs) = map (fun x => f2 (f1 x)) xs
     for all f xs ys,
        map f (append xs ys) = append (map f xs) (map f ys)
     for all f xs,
       map f (reverse xs) = reverse (map f xs)
*)

(* Exercise: write a unit test that validates these properties. *)

Definition unit_tests_for_map_nat_v2 (map : (nat -> nat) -> list nat -> list nat) (append : list nat -> list nat -> list nat) (reverse : list nat -> list nat)  :=
  (equal_list_nat (map (fun n => n) (map (fun n => 2*n) (1 :: 2 :: 3 :: nil)))
                  (map (fun n => 2*n) (map (fun n => n) (1 :: 2 :: 3 :: nil))))
  &&
  (equal_list_nat (map (fun n => n*n) (map (fun n => n) (1 :: 2 :: 3 :: 4 :: nil)))
                  (map (fun n => n) (map (fun n => n*n) (1 :: 2 :: 3 :: 4 :: nil))))
  &&
  (equal_list_nat (map (fun n => 2*n) (map (fun n => 2*n) (1 :: 2 :: 3 :: 4 :: nil)))
                  (4 :: 8 :: 12 :: 16 :: nil))
  &&
  (equal_list_nat (map (fun n => n) (append (1 :: 2 :: 3 :: nil) (4 :: 5 :: 6 ::nil)))
                  (append (map (fun n => n) (1 :: 2 :: 3 :: nil)) (map (fun n => n) (4 :: 5 :: 6 :: nil))))
  &&
  (equal_list_nat (map (fun n => n) (append (1 :: 2 :: nil) (4 :: 5 :: nil)))
                  (append (map (fun n => n) (1 :: 2 :: nil)) (map (fun n => n) (4 :: 5 :: nil))))
  &&
  (equal_list_nat (map (fun n => n) (reverse (1 :: 2 :: 3 :: nil)))
                  (reverse (map (fun n => n) (1 :: 2 :: 3 :: nil))))
  &&
  (equal_list_nat (map (fun n => n*n) (reverse (1 :: 2 :: 3 :: 4 :: nil)))
                  (reverse (map (fun n => n*n) (1 :: 2 :: 3 :: 4 :: nil))))
  .

Compute unit_tests_for_map_nat_v2 (map_v1 nat nat) (append_v1 nat) (reverse_v1 nat).
(*
  = true
  : bool
*)

Proposition listlessness_of_map :
  forall (T1 T2 T3 : Type)
         (map12 : (T1 -> T2) -> list T1 -> list T2)
         (map23 : (T2 -> T3) -> list T2 -> list T3)
         (map13 : (T1 -> T3) -> list T1 -> list T3),
    specification_of_map T1 T2 map12 ->
    specification_of_map T2 T3 map23 ->
    specification_of_map T1 T3 map13 ->
    forall (f1 : T1 -> T2)
           (f2 : T2 -> T3)
           (xs : list T1),
      map23 f2 (map12 f1 xs) = map13 (fun x => f2 (f1 x)) xs.
Proof.
  intros T1 T2 T3.
  intros map12 map23 map13.
  intros S_map12 S_map23 S_map13.
  intros f12 f23.
  intros xs.
  unfold specification_of_map in S_map12.
  destruct S_map12 as [H_map_bc12 H_map_ic12].
  unfold specification_of_map in S_map23.
  destruct S_map23 as [H_map_bc23 H_map_ic23].
  unfold specification_of_map in S_map13.
  destruct S_map13 as [H_map_bc13 H_map_ic13].

  induction xs as [ | x' xs' IHxs'].
  
  (* Base case: *)
    rewrite -> (H_map_bc12 f12).
    rewrite -> (H_map_bc23 f23).
    rewrite -> (H_map_bc13 (fun x : T1 => f23 (f12 x))).
    reflexivity.

  (* Inductive case: *)
    rewrite -> (H_map_ic13 (fun x : T1 => f23 (f12 x)) x' xs').
    rewrite -> (H_map_ic12 f12 x' xs').
    rewrite -> (H_map_ic23 f23 (f12 x') (map12 f12 xs')).
    rewrite -> (IHxs').
    reflexivity.
Qed.


Proposition append_preserves_map :
  forall (T1 T2 : Type)
         (map : (T1 -> T2) -> list T1 -> list T2)
         (append_1 : list T1 -> list T1 -> list T1)
         (append_2 : list T2 -> list T2 -> list T2),
    specification_of_map T1 T2 map ->
    specification_of_append T1 append_1 ->
    specification_of_append T2 append_2 ->
    forall (f : T1 -> T2) (xs ys : list T1),
       map f (append_1 xs ys) = append_2 (map f xs) (map f ys).
Proof.
  intros T1 T2.
  intros map append_1 append_2.
  intros S_map S_append1 S_append2.
  intro f.
  intros xs ys.
  unfold specification_of_map in S_map.
  destruct S_map as [H_map_bc H_map_ic].
  unfold specification_of_append in S_append1.
  destruct S_append1 as [H_app_bc1 H_app_ic1].
  unfold specification_of_append in S_append2.
  destruct S_append2 as [H_app_bc2 H_app_ic2].
  
  induction xs as [ | x xs' IHxs'].
  
  (* Base case: *)
    rewrite -> (H_app_bc1 ys).
    rewrite -> (H_map_bc f).
    rewrite -> (H_app_bc2 (map f ys)).
    reflexivity.

  (* Inductive case: *)
    rewrite -> (H_app_ic1 x xs' ys).
    rewrite -> (H_map_ic f x (append_1 xs' ys)).
    rewrite -> (IHxs').
    rewrite -> (H_map_ic f x xs').
    rewrite -> (H_app_ic2 (f x) (map f xs') (map f ys)).
    reflexivity.
Qed.
  
Proposition reverse_preserves_map_sort_of :
  forall (T1 T2 : Type)
         (append_1 : list T1 -> list T1 -> list T1)
         (append_2 : list T2 -> list T2 -> list T2)
         (reverse_1 : list T1 -> list T1)
         (reverse_2 : list T2 -> list T2)
         (map : (T1 -> T2) -> list T1 -> list T2),
    specification_of_append T1 append_1 ->
    specification_of_append T2 append_2 ->
    specification_of_reverse T1 reverse_1 ->
    specification_of_reverse T2 reverse_2 ->
    specification_of_map T1 T2 map ->
    forall (f : T1 -> T2)
           (xs : list T1),
      map f (reverse_1 xs) = reverse_2 (map f xs).
Proof.
  intros T1 T2.
  intros append1 append2 reverse1 reverse2 map.
  intros S_append1 S_append2 S_reverse1 S_reverse2 S_map.
  intro f.
  intro xs.
  assert(map_s := S_map).
  assert(app_s1 := S_append1).
  assert(app_s2 := S_append2).
  unfold specification_of_reverse in S_reverse1.
  destruct (S_reverse1 append1 S_append1) as [H_rev_bc1 H_rev_ic1].
  unfold specification_of_reverse in S_reverse2.
  destruct (S_reverse2 append2 S_append2) as [H_rev_bc2 H_rev_ic2].
  clear S_reverse1.
  clear S_reverse2.
  unfold specification_of_append in S_append1.
  destruct S_append1 as [H_app_bc1 H_app_ic1].
  unfold specification_of_append in S_append2.
  destruct S_append2 as [H_app_bc2 H_app_ic2].
  unfold specification_of_map in S_map.
  destruct S_map as [H_map_bc H_map_ic].

  induction xs as [ | x xs' IHxs'].
  
  (* Base case: *)
    rewrite -> (H_rev_bc1).
    rewrite -> (H_map_bc f).
    rewrite -> (H_rev_bc2).
    reflexivity.

  (* Inductive case: *)
    rewrite -> (H_map_ic f x xs').
    rewrite -> (H_rev_ic2 (f x) (map f xs')).
    rewrite <- (IHxs').
    rewrite -> (H_rev_ic1 x xs').
    rewrite -> (append_preserves_map T1 T2 map append1 append2 map_s app_s1 app_s2 f (reverse1 xs') (x :: nil)).
    rewrite -> (H_map_ic f x nil).
    rewrite -> (H_map_bc f). 
    reflexivity.
Qed.

(* ********** *)

(* end of week_37b_lists.v *)
