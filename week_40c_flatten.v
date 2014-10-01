(* week_40c_flatten.v *)
(* dIFP 2014-2015, Q1, Week 40 *)
(* Olivier Danvy <danvy@cs.au.dk> *)

(* ********** *)

Require Import Arith Bool unfold_tactic List.

Fixpoint beq_list (T : Type) (beq : T -> T -> bool) (xs ys : list T) : bool :=
  match xs with
    | nil =>
      match ys with
        | nil => true
        | y :: ys' => false
      end
    | x :: xs' =>
      match ys with
        | nil => false
        | y :: ys' => (beq x y) && (beq_list T beq xs' ys')
      end
  end.

Definition beq_list_nat (xs ys : list nat) : bool :=
  beq_list nat beq_nat xs ys.

Definition beq_list_bool (xs ys : list bool) : bool :=
  beq_list bool eqb xs ys.

Notation "A =n= B" := (beq_nat A B) (at level 70, right associativity).
Notation "A =l= B" := (beq_list_nat A B) (at level 70, right associativity).

(* ********** *)

(* Data type of binary trees of natural numbers: *)

Inductive binary_tree_nat : Type :=
  | Leaf : nat -> binary_tree_nat
  | Node : binary_tree_nat -> binary_tree_nat -> binary_tree_nat.

Check(binary_tree_nat_ind).
Check nat_ind.


(* There is one base case: leaves.
   There is one induction case, with two subtrees.
*)

(* ********** *)

(* Sample of binary trees of natural numbers: *)

Definition bt_0 :=
  Leaf 42.

Definition bt_1 :=
  Node (Leaf 10)
       (Leaf 20).

Definition bt_2 :=
  Node (Node (Leaf 10)
             (Leaf 20))
       (Leaf 30).

(* ********** *)

Definition unit_test_for_flatten (candidate : binary_tree_nat -> list nat) :=
  (candidate bt_0 =l= 42 :: nil)
  &&
  (candidate bt_1 =l= 10 :: 20 :: nil)
  &&
  (candidate bt_2 =l= 10 :: 20 :: 30 :: nil)
  &&
  (candidate (Node bt_1 bt_2) =l= 10 :: 20 :: 10 :: 20 :: 30 :: nil)
  .
(* ********** *)

Definition specification_of_flatten (flatten : binary_tree_nat -> list nat) :=
  (forall n : nat,
     flatten (Leaf n) = n :: nil)
  /\
  (forall t1 t2 : binary_tree_nat,
     flatten (Node t1 t2) = (flatten t1) ++ (flatten t2)).

Theorem there_is_only_one_flatten :
  forall flatten1 flatten2 : binary_tree_nat -> list nat,
    specification_of_flatten flatten1 ->
    specification_of_flatten flatten2 ->
    forall t : binary_tree_nat,
      flatten1 t = flatten2 t.
Proof.
  intros flatten1 flatten2.
  unfold specification_of_flatten.
  intros [H1_leaf H1_node] [H2_leaf H2_node].
  intro t.
  induction t as [n | t1 IHt1 t2 IHt2].

  rewrite -> H2_leaf.
  apply H1_leaf.

  rewrite -> H1_node.
  rewrite -> H2_node.
  rewrite -> IHt1.
  rewrite -> IHt2.
  reflexivity.
Qed.

(* ********** *)

(* Version with append: *)

Fixpoint flatten_ds (t : binary_tree_nat) : list nat :=
  match t with
    | Leaf n => n :: nil
    | Node t1 t2 => (flatten_ds t1) ++ (flatten_ds t2)
  end.


Definition flatten_v0 (t : binary_tree_nat) : list nat :=
  flatten_ds t.

Compute unit_test_for_flatten flatten_v0.

Lemma unfold_flatten_ds_bc :
  forall n : nat,
    flatten_ds( Leaf n) = n :: nil.
Proof.    
  unfold_tactic flatten_ds.
Qed.

Lemma unfold_flatten_ds_ic :
  forall t1 t2 : binary_tree_nat,
    flatten_ds (Node t1 t2) = (flatten_ds t1) ++ (flatten_ds t2).
Proof.
  unfold_tactic flatten_ds.
Qed.


Lemma flatten_v0_fits_the_specification_of_flatten :
    specification_of_flatten flatten_v0.
Proof.
  unfold specification_of_flatten.
  unfold flatten_v0.
  split.
    apply unfold_flatten_ds_bc.
    apply unfold_flatten_ds_ic.
Qed.

(* ********** *)

(* Version with an accumulator: *)

Fixpoint flatten_acc (t : binary_tree_nat) (a : list nat) : list nat :=
  match t with
    | Leaf n => n :: a
    | Node t1 t2 => flatten_acc t1 (flatten_acc t2 a)
  end.

Definition flatten_v1 (t : binary_tree_nat) : list nat :=
  flatten_acc t nil.

Compute unit_test_for_flatten flatten_v1.

Lemma unfold_flatten_acc_bc :
  forall (n : nat) (a : list nat),
    flatten_acc (Leaf n) a = n :: a.
Proof.
  unfold_tactic flatten_acc.
Qed.

Lemma unfold_flatten_acc_ic :
  forall (t1 t2 : binary_tree_nat) (a : list nat),
    flatten_acc (Node t1 t2) a = flatten_acc t1 (flatten_acc t2 a).
Proof.
  unfold_tactic flatten_acc.
Qed.

Lemma help_me_with_list :
  forall (n : nat) (a : list nat),
  n :: a = (n :: nil) ++ a.
Proof.
  intro n.
  intro a.
  unfold app.
  reflexivity.
Qed.

Lemma eureka_on_flatten_acc :
  forall (t1 t2 : binary_tree_nat) (a : list nat),
    flatten_acc (Node t1 t2) a = flatten_acc t1 nil ++ flatten_acc t2 a.
Proof.
  intros t1.
  induction t1 as [ n | ].
  intro t2.
  intro a.
  rewrite -> unfold_flatten_acc_bc.
  rewrite -> unfold_flatten_acc_ic.
  rewrite -> unfold_flatten_acc_bc.
  rewrite help_me_with_list.
  reflexivity.

  intro a.
  intro a0.
  rewrite -> unfold_flatten_acc_ic.
  rewrite -> unfold_flatten_acc_ic.
  rewrite -> (IHt1_1).
  rewrite <- (app_assoc).
  rewrite <- (IHt1_2).
  rewrite <- (IHt1_1).
  
  

Lemma flatten_v1_fits_the_specification_of_flatten :
  specification_of_flatten flatten_v1.
Proof.
  unfold specification_of_flatten.
  unfold flatten_v1.
  split.
  intro n.
  apply unfold_flatten_acc_bc.
  intros t1 t2.

  Abort.

(* ********** *)

Fixpoint swap_ds (t : binary_tree_nat) : binary_tree_nat :=
  match t with
    | Leaf n => Leaf n
    | Node t1 t2 => Node (swap_ds t2) (swap_ds t1)
  end.

Definition swap_v0 (t : binary_tree_nat) : binary_tree_nat :=
  swap_ds t.

(* Prove that composing swap_v0 with itself yields the identity function. *)

(* ********** *)

(* What is the result of applying flatten_v0
   to the result of applying swap_v0 to a tree?
*)

(* ********** *)

(* end of week_40c_flatten.v *)
