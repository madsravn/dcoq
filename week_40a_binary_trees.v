(* week_40a_binary_trees.v *)
(* dIFP 2014-2015, Q1, Week 40 *)
(* Olivier Danvy <danvy@cs.au.dk> *)

(* ********** *)

Require Import Arith Bool unfold_tactic.

Lemma plus_1_l :
  forall n : nat,
    1 + n = S n.
Proof.
  intro n.
  rewrite -> plus_Sn_m.
  rewrite -> plus_0_l.
  reflexivity.
Qed.

Lemma plus_1_r :
  forall n : nat,
    n + 1 = S n.
Proof.
  intro n.
  rewrite -> (plus_comm).
  apply plus_1_l.
Qed.

Notation "A =n= B" := (beq_nat A B) (at level 70, right associativity).

(* ********** *)

(* Data type of binary trees of natural numbers: *)

Inductive binary_tree_nat : Type :=
  | Leaf : nat -> binary_tree_nat
  | Node : binary_tree_nat -> binary_tree_nat -> binary_tree_nat.

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

(*
Print bt_2.
bt_2 = Node (Node (Leaf 10) (Leaf 20)) (Leaf 30)
     : binary_tree_nat
*)

(* ********** *)

(* How many leaves are there in a given binary tree? *)

(* A unit test: *)

Definition unit_test_for_number_of_leaves (candidate : binary_tree_nat -> nat) :=
  (candidate bt_0 =n= 1)
  &&
  (candidate bt_1 =n= 2)
  &&
  (candidate bt_2 =n= 3)
  &&
  (candidate (Node bt_1 bt_2) =n= 5)
  .

(* ***** *)

(* A specification: *)

Definition specification_of_number_of_leaves (number_of_leaves : binary_tree_nat -> nat) :=
  (forall n : nat,
     number_of_leaves (Leaf n) = 1)
  /\
  (forall t1 t2 : binary_tree_nat,
     number_of_leaves (Node t1 t2) = number_of_leaves t1 + number_of_leaves t2).

(* ***** *)

(* Uniqueness of the specification: *)

Theorem there_is_only_one_number_of_leaves :
  forall f g : binary_tree_nat -> nat,
    specification_of_number_of_leaves f ->
    specification_of_number_of_leaves g ->
    forall t : binary_tree_nat,
      f t = g t.
Proof.
  intros f g.
  unfold specification_of_number_of_leaves.
  intros [Hf_leaf Hf_node] [Hg_leaf Hg_node].
  intro t.
  induction t as [n | t1 IHt1 t2 IHt2].

  rewrite -> Hf_leaf.
  rewrite -> Hg_leaf.
  reflexivity.

  rewrite -> Hf_node.
  rewrite -> Hg_node.
  rewrite -> IHt1.
  rewrite -> IHt2.
  reflexivity.
Qed.

(* ***** *)

(* A first implementation, in direct style: *)

(* The auxiliary (recursive) function: *)

Fixpoint number_of_leaves_ds (t : binary_tree_nat) : nat :=
  match t with
    | Leaf n =>
      1
    | Node t1 t2 =>
      (number_of_leaves_ds t1) + (number_of_leaves_ds t2)
  end.

(* The canonical unfold lemmas: *)

Lemma unfold_number_of_leaves_ds_Leaf :
  forall n : nat,
    number_of_leaves_ds (Leaf n) = 1.
Proof.
  unfold_tactic number_of_leaves_ds.
Qed.

Lemma unfold_number_of_leaves_ds_Node :
  forall t1 t2 : binary_tree_nat,
    number_of_leaves_ds (Node t1 t2) =
    (number_of_leaves_ds t1) + (number_of_leaves_ds t2).
Proof.
  unfold_tactic number_of_leaves_ds.
Qed.

(* The main (non-recursive) function: *)

Definition number_of_leaves_v0 (t : binary_tree_nat) : nat :=
  number_of_leaves_ds t.

(* ***** *)

(* The standard sanity check: *)

Compute unit_test_for_number_of_leaves number_of_leaves_v0.
(*
     = true
     : bool
*)

(* ***** *)

(* The first implementation satisfies the specification: *)

Theorem number_of_leaves_v0_satisfies_the_specification_of_number_of_leaves :
  specification_of_number_of_leaves number_of_leaves_v0.
Proof.
  unfold specification_of_number_of_leaves.
  unfold number_of_leaves_v0.
  split.

  exact unfold_number_of_leaves_ds_Leaf.

  exact unfold_number_of_leaves_ds_Node.
Qed.

(* ***** *)

(* A second implementation, with an accumulator: *)

(* The auxiliary (recursive) function: *)

Fixpoint number_of_leaves_acc (t : binary_tree_nat) (a : nat) : nat :=
  match t with
    | Leaf n =>
      1 + a  (* or even better: S a *)
    | Node t1 t2 =>
      number_of_leaves_acc t1 (number_of_leaves_acc t2 a)
  end.

(* The canonical unfold lemmas: *)

Lemma unfold_number_of_leaves_acc_Leaf :
  forall n a : nat,
    number_of_leaves_acc (Leaf n) a = 1 + a.
Proof.
  unfold_tactic number_of_leaves_acc.
Qed.

Lemma unfold_number_of_leaves_acc_Node :
  forall (t1 t2 : binary_tree_nat)
         (a : nat),
    number_of_leaves_acc (Node t1 t2) a =
    number_of_leaves_acc t1 (number_of_leaves_acc t2 a).
Proof.
  unfold_tactic number_of_leaves_acc.
Qed.

(* The main (non-recursive) function: *)

Definition number_of_leaves_v1 (t : binary_tree_nat) : nat :=
  number_of_leaves_acc t 0.

(* ***** *)

(* The standard sanity check: *)

Compute unit_test_for_number_of_leaves number_of_leaves_v1.
(*
     = true
     : bool
*)

(* The second implementation satisfies the specification: *)

Theorem number_of_leaves_v1_satisfies_the_specification_of_number_of_leaves_first_attempt :
  specification_of_number_of_leaves number_of_leaves_v1.
Proof.
  unfold specification_of_number_of_leaves.
  unfold number_of_leaves_v1.
  split.

  intro n.
  apply (unfold_number_of_leaves_acc_Leaf n 0).

  intros t1 t2.
  rewrite -> unfold_number_of_leaves_acc_Node.
  (* Hum, we are stuck.  Let's venture a helpful lemma: *)
Abort.

Lemma about_number_of_leaves_acc_tentative :
  forall (t : binary_tree_nat)
         (a : nat),
    number_of_leaves_acc t a = (number_of_leaves_acc t 0) + a.
Proof.
Admitted.

Theorem number_of_leaves_v1_satisfies_the_specification_of_number_of_leaves_second_attempt :
  specification_of_number_of_leaves number_of_leaves_v1.
Proof.
  unfold specification_of_number_of_leaves.
  unfold number_of_leaves_v1.
  split.

  intro n.
  apply (unfold_number_of_leaves_acc_Leaf n 0).

  intros t1 t2.
  rewrite -> unfold_number_of_leaves_acc_Node.
  rewrite -> about_number_of_leaves_acc_tentative.
  reflexivity.
  (* Yay, the proof goes through.
     So let's prove the helpful lemma. *)
Abort.

Lemma about_number_of_leaves_acc :
  forall (t : binary_tree_nat)
         (a : nat),
    number_of_leaves_acc t a = (number_of_leaves_acc t 0) + a.
Proof.
  intro t.
  induction t as [n | t1 IHt1 t2 IHt2].

  (* Base case: *)
  intro a.
  (* left-hand side: *)
  rewrite -> unfold_number_of_leaves_acc_Leaf.
  (* right-hand side: *)
  rewrite -> unfold_number_of_leaves_acc_Leaf.
  rewrite -> plus_0_r.
  reflexivity.

  (* Induction case: *)
  intro a.
  (* left-hand side: *)
  rewrite -> unfold_number_of_leaves_acc_Node.
  rewrite -> IHt1.
  rewrite -> IHt2.
  (* right-hand side: *)
  rewrite -> unfold_number_of_leaves_acc_Node.
  rewrite -> (IHt1 (number_of_leaves_acc t2 0)).
  (* postlude: *)
  apply plus_assoc.
Qed.

Theorem number_of_leaves_v1_satisfies_the_specification_of_number_of_leaves :
  specification_of_number_of_leaves number_of_leaves_v1.
Proof.
  unfold specification_of_number_of_leaves.
  unfold number_of_leaves_v1.
  split.

  intro n.
  apply (unfold_number_of_leaves_acc_Leaf n 0).

  intros t1 t2.
  rewrite -> unfold_number_of_leaves_acc_Node.
  rewrite -> about_number_of_leaves_acc.
  reflexivity.
Qed.

(* ***** *)

(* The two implementations implement the same function: *)

Theorem number_of_leaves_v0_and_v1_implement_the_same_function :
  forall t : binary_tree_nat,
    number_of_leaves_v0 t = number_of_leaves_v1 t.
Proof.
  (* Pedestrian attempt: *)
  intro t.
  unfold number_of_leaves_v0.
  unfold number_of_leaves_v1.
  induction t as [n | t1 IHt1 t2 IHt2].

  rewrite -> unfold_number_of_leaves_ds_Leaf.
  rewrite -> unfold_number_of_leaves_acc_Leaf.
  rewrite -> plus_0_r.
  reflexivity.

  rewrite -> unfold_number_of_leaves_ds_Node.
  rewrite -> unfold_number_of_leaves_acc_Node.
  rewrite -> about_number_of_leaves_acc.
  rewrite -> IHt1.
  rewrite -> IHt2.
  reflexivity.

  Restart.

  (* Reusing what we did before: *)

  exact (there_is_only_one_number_of_leaves
           number_of_leaves_v0
           number_of_leaves_v1
           number_of_leaves_v0_satisfies_the_specification_of_number_of_leaves
           number_of_leaves_v1_satisfies_the_specification_of_number_of_leaves).

  Restart.

  (* Reusing what we did before, less concisely: *)

  intro t.
  exact (there_is_only_one_number_of_leaves
           number_of_leaves_v0
           number_of_leaves_v1
           number_of_leaves_v0_satisfies_the_specification_of_number_of_leaves
           number_of_leaves_v1_satisfies_the_specification_of_number_of_leaves
           t).
Qed.

(* ***** *)

(* A third implementation, with higher-order functions: *)

Definition compose_nat (f g : nat -> nat) (n : nat) :=
  f (g n).

Notation "F << G" := (compose_nat F G) (at level 70, right associativity).

Compute (S << S) 40.

Compute ((fun x => 2 + x) << (fun y => 10 * y)) 4.

Lemma unfold_compose_nat :
  forall (f g : nat -> nat)
          (n : nat),
    compose_nat f g n = f (g n).
Proof.
  unfold_tactic compose_nat.
Qed.

(* The auxiliary (recursive) function: *)

Fixpoint number_of_leaves_higher_order (t : binary_tree_nat) : nat -> nat :=
  match t with
    | Leaf n =>
      S
    | Node t1 t2 =>
      (number_of_leaves_higher_order t1) << (number_of_leaves_higher_order t2)
  end.

(* The canonical unfold lemmas: *)

Lemma unfold_number_of_leaves_higher_order_Leaf :
  forall n : nat,
    number_of_leaves_higher_order (Leaf n) = S.
Proof.
  unfold_tactic number_of_leaves_higher_order.
Qed.

Lemma unfold_number_of_leaves_higher_order_Node :
  forall (t1 t2 : binary_tree_nat),
    number_of_leaves_higher_order (Node t1 t2) =
    ((number_of_leaves_higher_order t1) << (number_of_leaves_higher_order t2)).
Proof.
  unfold_tactic number_of_leaves_higher_order.
Qed.

(* The main (non-recursive) function: *)

Definition number_of_leaves_v2 (t : binary_tree_nat) : nat :=
  number_of_leaves_higher_order t 0.

(* ***** *)

(* The standard sanity check: *)

Compute unit_test_for_number_of_leaves number_of_leaves_v2.
(*
     = true
     : bool
*)

(* The second implementation satisfies the specification: *)

Theorem number_of_leaves_v2_satisfies_the_specification_of_number_of_leaves_first_attempt :
  specification_of_number_of_leaves number_of_leaves_v2.
Proof.
  unfold specification_of_number_of_leaves.
  unfold number_of_leaves_v2.
  split.

  intro n.
  rewrite -> unfold_number_of_leaves_higher_order_Leaf.
  reflexivity.

  intros t1 t2.
  rewrite -> unfold_number_of_leaves_higher_order_Node.
  rewrite -> unfold_compose_nat.
(* Aha: number_of_leaves_v2 is the same as number_of_leaves_v1! *)
Abort.

Lemma about_number_of_leaves_higher_order :
  forall (t : binary_tree_nat)
         (a : nat),
    number_of_leaves_higher_order t a =
    number_of_leaves_acc t a.
Proof.
  intro t.
  induction t as [n | t1 IHt1 t2 IHt2].

  intro a.
  rewrite -> unfold_number_of_leaves_higher_order_Leaf.
  rewrite -> unfold_number_of_leaves_acc_Leaf.
  rewrite -> (plus_1_l a).
  reflexivity.

  intro a.
  rewrite -> unfold_number_of_leaves_higher_order_Node.
  rewrite -> unfold_compose_nat.
  rewrite -> IHt1.
  rewrite -> IHt2.
  rewrite -> unfold_number_of_leaves_acc_Node.
  reflexivity.
Qed.

Theorem number_of_leaves_v2_satisfies_the_specification_of_number_of_leaves :
  specification_of_number_of_leaves number_of_leaves_v2.
Proof.
  unfold specification_of_number_of_leaves.
  unfold number_of_leaves_v2.
  split.

  intro n.
  rewrite -> about_number_of_leaves_higher_order.
  exact (unfold_number_of_leaves_acc_Leaf n 0).

  intros t1 t2.
  rewrite -> about_number_of_leaves_higher_order.
  rewrite -> unfold_number_of_leaves_acc_Node.
  rewrite -> about_number_of_leaves_acc.
  rewrite -> about_number_of_leaves_higher_order.
  rewrite -> about_number_of_leaves_higher_order.
  reflexivity.
Qed.

(* ***** *)

(* A fourth implementation, in CPS: *)

(* The auxiliary (recursive) function: *)

Fixpoint number_of_leaves_cps (ans : Type) (t : binary_tree_nat) (k : nat -> ans) : ans :=
  match t with
    | Leaf n =>
      k 1
    | Node t1 t2 =>
      number_of_leaves_cps
        ans
        t1
        (fun n1 => number_of_leaves_cps
                     ans
                     t2
                     (fun n2 => k (n1 + n2)))
  end.

(* The canonical unfold lemmas: *)

Lemma unfold_number_of_leaves_cps_Leaf :
  forall (ans : Type)
         (n : nat)
         (k : nat -> ans),
    number_of_leaves_cps ans (Leaf n) k = k 1.
Proof.
  unfold_tactic number_of_leaves_cps.
Qed.

Lemma unfold_number_of_leaves_cps_Node :
  forall (ans : Type)
         (t1 t2 : binary_tree_nat)
         (k : nat -> ans),
    number_of_leaves_cps ans (Node t1 t2) k =
    number_of_leaves_cps
      ans
      t1
      (fun n1 => number_of_leaves_cps
                   ans
                   t2
                   (fun n2 => k (n1 + n2))).
Proof.
  unfold_tactic number_of_leaves_cps.
Qed.

(* The main (non-recursive) function: *)

Definition number_of_leaves_v3 (t : binary_tree_nat) : nat :=
  number_of_leaves_cps nat t (fun n => n).

(* ***** *)

(* The standard sanity check: *)

Compute unit_test_for_number_of_leaves number_of_leaves_v3.
(*
     = true
     : bool
*)

(* The fourth implementation satisfies the specification: *)

Theorem number_of_leaves_v3_satisfies_the_specification_of_number_of_leaves_first_attempt :
  specification_of_number_of_leaves number_of_leaves_v3.
Proof.
  unfold specification_of_number_of_leaves.
  unfold number_of_leaves_v3.
  split.

  intro n.
  rewrite -> unfold_number_of_leaves_cps_Leaf.
  reflexivity.

  intros t1 t2.
  rewrite -> unfold_number_of_leaves_cps_Node.
  (* Hum, we are stuck.  Let's venture a helpful lemma: *)
Abort.

Lemma about_number_of_leaves_cps_tentative :
  forall (ans : Type)
         (t : binary_tree_nat)
         (k : nat -> ans),
    number_of_leaves_cps ans t k =
    k (number_of_leaves_cps nat t (fun n => n)).
Proof.
Admitted.

Theorem number_of_leaves_v3_satisfies_the_specification_of_number_of_leaves_second_attempt :
  specification_of_number_of_leaves number_of_leaves_v3.
Proof.
  unfold specification_of_number_of_leaves.
  unfold number_of_leaves_v3.
  split.

  intro n.
  rewrite -> unfold_number_of_leaves_cps_Leaf.
  reflexivity.

  intros t1 t2.
  rewrite -> unfold_number_of_leaves_cps_Node.
  rewrite -> about_number_of_leaves_cps_tentative.
  rewrite -> about_number_of_leaves_cps_tentative.
  reflexivity.
  (* Yay, the proof goes through.
     So let's prove the helpful lemma. *)
Abort.

Lemma about_number_of_leaves_cps :
  forall (ans : Type)
         (t : binary_tree_nat)
         (k : nat -> ans),
    number_of_leaves_cps ans t k =
    k (number_of_leaves_cps nat t (fun n => n)).
Proof.
  intros ans t.
  induction t as [n | t1 IHt1 t2 IHt2].

  (* Base case: *)
  intro k.
  (* left-hand side: *)
  rewrite -> unfold_number_of_leaves_cps_Leaf.
  (* right-hand side: *)
  rewrite -> unfold_number_of_leaves_cps_Leaf.
  reflexivity.

  (* Induction case: *)
  intro k.
  (* left-hand side: *)
  rewrite -> unfold_number_of_leaves_cps_Node.
  rewrite -> IHt1.
  rewrite -> IHt2.
  (* right-hand side: *)
  symmetry.
  (* OK, left-hand side then: *)
  rewrite -> unfold_number_of_leaves_cps_Node.
  (* And we are stuck.
     Let's strengthen the induction hypothesis. *)

  Restart.

  intros ans t.
  revert ans.
  induction t as [n | t1 IHt1 t2 IHt2].

  (* Base case: *)
  intros ans k.
  (* left-hand side: *)
  rewrite -> unfold_number_of_leaves_cps_Leaf.
  (* right-hand side: *)
  rewrite -> unfold_number_of_leaves_cps_Leaf.
  reflexivity.

  (* Induction case: *)
  intros ans k.
  (* left-hand side: *)
  rewrite -> unfold_number_of_leaves_cps_Node.
  rewrite -> IHt1.
  rewrite -> IHt2.
  (* right-hand side: *)
  symmetry.
  (* OK, left-hand side then: *)
  rewrite -> unfold_number_of_leaves_cps_Node.
  rewrite -> IHt1.
  rewrite -> IHt2.
  reflexivity.
Qed.

Theorem number_of_leaves_v3_satisfies_the_specification_of_number_of_leaves :
  specification_of_number_of_leaves number_of_leaves_v3.
Proof.
  unfold specification_of_number_of_leaves.
  unfold number_of_leaves_v3.
  split.

  intro n.
  rewrite -> unfold_number_of_leaves_cps_Leaf.
  reflexivity.

  intros t1 t2.
  rewrite -> unfold_number_of_leaves_cps_Node.
  rewrite -> about_number_of_leaves_cps.
  rewrite -> about_number_of_leaves_cps.
  reflexivity.
Qed.

(* ***** *)

(* The four implementations implement the same function: *)

Theorem number_of_leaves_v0_and_v3_implement_the_same_function :
  forall t : binary_tree_nat,
    number_of_leaves_v0 t = number_of_leaves_v3 t.
Proof.
  exact (there_is_only_one_number_of_leaves
           number_of_leaves_v0
           number_of_leaves_v3
           number_of_leaves_v0_satisfies_the_specification_of_number_of_leaves
           number_of_leaves_v3_satisfies_the_specification_of_number_of_leaves).
Qed.

Theorem number_of_leaves_v1_and_v3_implement_the_same_function :
  forall t : binary_tree_nat,
    number_of_leaves_v1 t = number_of_leaves_v3 t.
Proof.
  exact (there_is_only_one_number_of_leaves
           number_of_leaves_v1
           number_of_leaves_v3
           number_of_leaves_v1_satisfies_the_specification_of_number_of_leaves
           number_of_leaves_v3_satisfies_the_specification_of_number_of_leaves).
Qed.

Theorem number_of_leaves_v2_and_v3_implement_the_same_function :
  forall t : binary_tree_nat,
    number_of_leaves_v2 t = number_of_leaves_v3 t.
Proof.
  exact (there_is_only_one_number_of_leaves
           number_of_leaves_v2
           number_of_leaves_v3
           number_of_leaves_v2_satisfies_the_specification_of_number_of_leaves
           number_of_leaves_v3_satisfies_the_specification_of_number_of_leaves).
Qed.

(* ********** *)
(* ********** *)
(* EXERCISES BEGIN HERE! *)


(* Exercise:
   Revisit how to compute the number of nodes
   of a binary tree.
*)

Definition specification_of_number_of_nodes (number_of_nodes : binary_tree_nat -> nat) :=
  (forall n : nat,
     number_of_nodes (Leaf n) = 0)
  /\
  (forall t1 t2 : binary_tree_nat,
     number_of_nodes (Node t1 t2) = S (number_of_nodes t1 + number_of_nodes t2)).



 Fixpoint number_of_leaves_acc' (t : binary_tree_nat) (a : nat) : nat :=
   match t with
     | Leaf n =>
       1 + a
     | Node t1 t2 =>
       (number_of_leaves_acc' t2 (number_of_leaves_acc' t1 a))
   end.
    
 Definition number_of_leaves_v1' (t : binary_tree_nat) : nat :=
   number_of_leaves_acc' t 0.

Compute unit_test_for_number_of_leaves number_of_leaves_v1'.
(* 
  = true
  : bool
*)

Lemma unfold_number_of_leaves_acc'_bc :
  forall (n a : nat),
    number_of_leaves_acc' (Leaf n) a = 1 + a.
Proof.
  unfold_tactic number_of_leaves_acc'.
Qed.

Lemma unfold_number_of_leaves_acc'_ic :
  forall (t1 t2 : binary_tree_nat) (a : nat),
    number_of_leaves_acc' (Node t1 t2) a = number_of_leaves_acc' t2 ( number_of_leaves_acc' t1 a).
Proof.
  unfold_tactic number_of_leaves_acc'.
Qed.

Lemma eureka_now :
  forall (t : binary_tree_nat) (a : nat),
    number_of_leaves_acc' t a = a + number_of_leaves_acc' t 0.
Proof.
  intro t.
  induction t as [ t' | t1 IHt1 t2 IHt2].
  intro a.
  rewrite -> unfold_number_of_leaves_acc'_bc.
  rewrite -> unfold_number_of_leaves_acc'_bc.
  rewrite -> (plus_0_r).
  rewrite -> (plus_comm).
  reflexivity.

  intro a.
  rewrite -> (unfold_number_of_leaves_acc'_ic).
  rewrite -> (unfold_number_of_leaves_acc'_ic).
  rewrite -> IHt2.
  rewrite -> IHt1.
  rewrite -> (IHt2 (number_of_leaves_acc' t1 0)).
  rewrite <- (plus_assoc).
  reflexivity.
Qed.


Lemma number_of_leaves_acc'_fits_specification_of_number_of_leaves :
  specification_of_number_of_leaves number_of_leaves_v1'.
Proof.
  unfold number_of_leaves_v1'.
  unfold specification_of_number_of_leaves.
  split.
  intro n.
  rewrite -> (unfold_number_of_leaves_acc'_bc).
  rewrite -> plus_0_r.
  reflexivity.

  intros t1 t2.
  rewrite -> (unfold_number_of_leaves_acc'_ic).
  rewrite -> (eureka_now).
  reflexivity.
Qed.



Fixpoint number_of_leaves_cps' (ans : Type) (t : binary_tree_nat) (k : nat -> ans) : ans :=
   match t with
     | Leaf n =>
       k 1
     | Node t1 t2 =>
       number_of_leaves_cps'
         ans
         t2
         (fun n2 => number_of_leaves_cps'
                      ans
                      t1
                      (fun n1 => k (n1 + n2)))
   end.
 
 Definition number_of_leaves_v3' (t : binary_tree_nat) : nat :=
   number_of_leaves_cps' nat t (fun n => n).

Compute unit_test_for_number_of_leaves number_of_leaves_v3'.
(*
  = true
  : bool
*)
Lemma unfold_number_of_leaves_cps'_bc :
  forall (ans : Type)
         (n : nat)
         (k : nat -> ans),
    number_of_leaves_cps' ans (Leaf n) k = k 1.
Proof.
  unfold_tactic number_of_leaves_cps'.
Qed.

Lemma unfold_number_of_leaves_cps'_ic :
  forall (ans : Type)
         (t1 t2 : binary_tree_nat)
         (k : nat -> ans),
    number_of_leaves_cps' ans (Node t1 t2) k =
    number_of_leaves_cps'
      ans
      t2
      (fun n2 => number_of_leaves_cps'
                   ans
                   t1
                   (fun n1 => k (n1 + n2))).
Proof.
  unfold_tactic number_of_leaves_cps'.
Qed.

Lemma about_number_of_leaves_cps' :
  forall (ans : Type)
         (t : binary_tree_nat)
         (k : nat -> ans),
    number_of_leaves_cps' ans t k =
    k (number_of_leaves_cps' nat t (fun n => n)).
Proof.
  intros ans t.
  revert ans.
  induction t as [n | t1 IHt1 t2 IHt2].

  (* Base case: *)
  intros ans k.
  (* left-hand side: *)
  rewrite -> unfold_number_of_leaves_cps'_bc.
  (* right-hand side: *)
  rewrite -> unfold_number_of_leaves_cps'_bc.
  reflexivity.

  (* Induction case: *)
  intros ans k.
  (* left-hand side: *)
  rewrite -> unfold_number_of_leaves_cps'_ic.

  rewrite -> IHt2.
  rewrite -> IHt1.
  (* right-hand side: *)
  symmetry.
  (* OK, left-hand side then: *)
  rewrite -> unfold_number_of_leaves_cps'_ic.

  rewrite -> IHt2.
  rewrite -> IHt1.
  reflexivity.
Qed.

Lemma number_of_leaves_cps'_fits_the_specification_of_number_of_leaves :
  specification_of_number_of_leaves number_of_leaves_v3'.
Proof.
  unfold specification_of_number_of_leaves.
  split.
  intro n.
  unfold number_of_leaves_v3'.
  rewrite -> (unfold_number_of_leaves_cps'_bc).
  reflexivity.

  intros t1 t2.
  unfold number_of_leaves_v3'.
  rewrite -> (unfold_number_of_leaves_cps'_ic).
  rewrite -> (about_number_of_leaves_cps').
  rewrite -> (about_number_of_leaves_cps').
  reflexivity.
Qed.

Definition specification_of_product_of_leaves (product_of_leaves : binary_tree_nat -> nat) :=
  (forall n : nat,
     product_of_leaves (Leaf n) = n)
  /\
  (forall t1 t2 : binary_tree_nat,
     product_of_leaves (Node t1 t2) = product_of_leaves t1 * product_of_leaves t2).

Definition bt_3 :=
  Node (Leaf 20)
       (Node (Leaf 3) (Leaf 4)).

Definition unit_test_for_product_of_leaves (candidate : binary_tree_nat -> nat) :=
  (candidate bt_0 =n= 42)
  &&
  (candidate bt_1 =n= 200)
  &&
  (candidate bt_3 =n= 240)
  .

Theorem there_is_only_one_product_of_leaves :
  forall f g : binary_tree_nat -> nat,
    specification_of_product_of_leaves f ->
    specification_of_product_of_leaves g ->
    forall t : binary_tree_nat,
      f t = g t.
Proof.
  intros f g.
  unfold specification_of_product_of_leaves.
  intros [Hf_leaf Hf_node] [Hg_leaf Hg_node].
  intro t.
  induction t as [ t' | t1 IHt1 t2 IHt2].
  rewrite -> Hf_leaf.
  rewrite -> Hg_leaf.
  reflexivity.
  
  rewrite -> Hf_node.
  rewrite -> Hg_node.
  rewrite -> IHt1.
  rewrite -> IHt2.
  reflexivity.
Qed.

Fixpoint product_of_leaves_ds (t : binary_tree_nat) : nat :=
  match t with
    | Leaf n => n
    | Node t1 t2 => (product_of_leaves_ds t1) * (product_of_leaves_ds t2)
end.

Lemma unfold_product_of_leaves_ds_bc :
  forall n : nat,
    product_of_leaves_ds (Leaf n) = n.
Proof.
  unfold_tactic product_of_leaves_ds.
Qed.

Lemma unfold_product_of_leaves_ds_ic :
  forall t1 t2 : binary_tree_nat,
    product_of_leaves_ds (Node t1 t2) = (product_of_leaves_ds t1) * (product_of_leaves_ds t2).
Proof.
  unfold_tactic product_of_leaves_ds.
Qed.

Definition product_of_leaves_v0 (t : binary_tree_nat) : nat :=
  product_of_leaves_ds t.

Compute unit_test_for_product_of_leaves product_of_leaves_v0.
(*
  = true
  : bool
*)
Lemma product_of_leaves_v0_fits_the_specification_of_product_of_leaves :
  specification_of_product_of_leaves product_of_leaves_v0.
Proof.
  unfold specification_of_product_of_leaves.
  unfold product_of_leaves_v0.
  split.
  intro n.
  rewrite -> (unfold_product_of_leaves_ds_bc).
  reflexivity.

  intros t1 t2.
  rewrite -> (unfold_product_of_leaves_ds_ic).
  reflexivity.
Qed.

Fixpoint product_of_leaves_good  (t : binary_tree_nat) : nat :=
  match t with
    | Leaf n => n
    | Node t1 t2 =>
      match (product_of_leaves_good t1) with
        | 0 => 0
        | x => x * (product_of_leaves_good t2)
      end
  end.

Lemma unfold_product_of_leaves_good_bc :
  forall n : nat,
    product_of_leaves_good (Leaf n) = n.
Proof.    
  unfold_tactic product_of_leaves_good.
Qed.

Lemma unfold_product_of_leaves_good_ic :
  forall (t1 t2 : binary_tree_nat),
    product_of_leaves_good (Node t1 t2) =  match (product_of_leaves_good t1) with
        | 0 => 0
        | x => x * (product_of_leaves_good t2)
      end.
Proof.
  unfold_tactic product_of_leaves_good.
Qed.

Definition product_of_leaves_v1 (t : binary_tree_nat) : nat :=
  product_of_leaves_good t.

Compute unit_test_for_product_of_leaves product_of_leaves_v1.
(*
  = true
  : bool
*)


Lemma product_of_leaves_v1_fits_the_specification_of_product_of_leaves :
  specification_of_product_of_leaves product_of_leaves_v1.
  unfold specification_of_product_of_leaves.
  unfold product_of_leaves_v1.
  split.
  intro n.
  rewrite -> unfold_product_of_leaves_good_bc.
  reflexivity.

  intros t1 t2.
  rewrite -> unfold_product_of_leaves_good_ic.
  case (product_of_leaves_good t1) as [ | n'].
    rewrite -> (mult_0_l).
    reflexivity.
  reflexivity.
Qed.

Theorem product_of_leaves_v0_and_v1_implement_the_same_function :
  forall t : binary_tree_nat,
    product_of_leaves_v0 t = product_of_leaves_v1 t.
Proof.
  exact (there_is_only_one_product_of_leaves
           product_of_leaves_v0
           product_of_leaves_v1
           product_of_leaves_v0_fits_the_specification_of_product_of_leaves
           product_of_leaves_v1_fits_the_specification_of_product_of_leaves ).
Qed.



(* ********** *)

(* Food for thought (with thanks to John Anker):
   For any binary tree,
   how would you compare its number of leaves and its number of nodes?
   Is there a relation?  If so, could you formalize it in Coq?
*)

Definition unit_test_for_number_of_nodes (candidate : binary_tree_nat -> nat) :=
  (candidate bt_0 =n= 0)
  &&
  (candidate bt_1 =n= 1)
  &&
  (candidate bt_2 =n= 2)
  &&
  (candidate (Node bt_1 bt_2) =n= 4)
  .

Theorem there_is_only_one_number_of_nodes :
  forall f g : binary_tree_nat -> nat,
    specification_of_number_of_nodes f ->
    specification_of_number_of_nodes g ->
    forall t : binary_tree_nat,
      f t = g t.
Proof.
  intros f g.
  unfold specification_of_number_of_nodes.
  intros [Hf_leaf Hf_node] [Hg_leaf Hg_node].
  intro t.
  induction t as [n | t1 IHt1 t2 IHt2].

  rewrite -> Hf_leaf.
  rewrite -> Hg_leaf.
  reflexivity.

  rewrite -> Hf_node.
  rewrite -> Hg_node.
  rewrite -> IHt1.
  rewrite -> IHt2.
  reflexivity.
Qed.

Fixpoint number_of_nodes_ds (t : binary_tree_nat) : nat :=
  match t with
    | Leaf n =>
      0
    | Node t1 t2 =>
      (number_of_nodes_ds t1) + (number_of_nodes_ds t2) + 1
  end.

Lemma unfold_number_of_nodes_ds_leaf :
  forall n : nat,
    number_of_nodes_ds (Leaf n) = 0.
Proof.
  unfold_tactic number_of_nodes_ds.
Qed.

Lemma unfold_number_of_nodes_ds_node :
  forall t1 t2 : binary_tree_nat,
    number_of_nodes_ds (Node t1 t2) =
    (number_of_nodes_ds t1) + (number_of_nodes_ds t2) + 1.
Proof.
  unfold_tactic number_of_nodes_ds.
Qed.

Definition number_of_nodes_v0 (t : binary_tree_nat) : nat :=
  number_of_nodes_ds t.

Compute unit_test_for_number_of_nodes number_of_nodes_v0.
(*
  = true
  : bool
*)

Lemma number_of_nodes_v0_fits_the_specification_of_number_of_nodes :
  specification_of_number_of_nodes number_of_nodes_v0.
Proof.    
  unfold specification_of_number_of_nodes.
  unfold number_of_nodes_v0.
  split.
  intro n.
  rewrite -> (unfold_number_of_nodes_ds_leaf).
  reflexivity.

  intros t1 t2.
  rewrite -> (unfold_number_of_nodes_ds_node).
  rewrite -> (plus_1_r).
  reflexivity.
Qed.


Theorem number_of_leaves_relates_to_number_of_nodes :
  forall t : binary_tree_nat,
    number_of_leaves_v0 t = 1 + number_of_nodes_v0 t.
Proof.
  intro t.
  unfold number_of_nodes_v0.
  unfold number_of_leaves_v0.
  induction t as [ t' | t1 IHt1 t2 IHt2 ].
  rewrite -> (unfold_number_of_leaves_ds_Leaf).
  rewrite -> (unfold_number_of_nodes_ds_leaf).
  rewrite -> (plus_0_r).
  reflexivity.

  rewrite -> (unfold_number_of_nodes_ds_node).
  rewrite -> (unfold_number_of_leaves_ds_Node).
  rewrite <- (plus_assoc).
  rewrite -> (plus_comm (number_of_nodes_ds t2) 1). 
  rewrite <- (IHt2).
  rewrite -> (plus_assoc).
  rewrite <- (IHt1).
  reflexivity.
Qed.

(* ********** *)

(* end of week_40a_binary_trees.v *)