Require Import Arith.
Require Import "unfold_tactic".

Lemma unfold_add_v1_bc :
  forall j : nat,
    plus 0 j = j.
(* left-hand side in the base case
   =
   the corresponding conditional branch *)
Proof.
  unfold_tactic plus.
Qed.

Lemma unfold_add_v1_ic :
  forall i' j : nat,
    plus (S i') j = S (plus i' j).
(* left-hand side in the inductive case
   =
   the corresponding conditional branch *)
Proof.
  unfold_tactic plus.
Qed.


(*
Lemma unfold_add_v2_ic :
  forall i' j : nat,
    plus (S i') j = plus i' (S j).
(* left-hand side in the inductive case
   =
   the corresponding conditional branch *)
Proof.
  intros i' j.
  rewrite -> (unfold_add_v1_ic i' j).
  rewrite -> (plus_comm i' (S j)).
  rewrite -> (unfold_add_v1_ic j i').
  rewrite -> (plus_comm j i').
  reflexivity.
Qed.
*)


(* A useful lemma: *)
(*
Proposition add_v2_ic_right :
  forall i j : nat,
    plus i (S j) = S (plus i j).
Proof.

  intro i.
  induction i as [ | i' IHi'].

  intro j.
  rewrite -> unfold_add_v1_bc.
  rewrite -> unfold_add_v1_bc.
  reflexivity.

  intro j.
  rewrite -> unfold_add_v2_ic.
  rewrite -> unfold_add_v2_ic.
  rewrite -> (IHi' (S j)).
  reflexivity.
Qed.
*)

Proposition plus_1_S :
  forall n : nat,
    S n = plus 1 n.
Proof.
  intro n.
  induction n as [ | n' IHn'].
  rewrite -> (plus_0_r 1).
  reflexivity.
  rewrite -> (unfold_add_v1_ic).
  rewrite -> (plus_0_l (S n')).
  reflexivity.
Qed.



Proposition reverse_v1_fits_the_specification_of_reverse :
  forall T : Type,
    specification_of_reverse T (reverse_v1 T).
Proof.
  intro T.
  unfold specification_of_reverse.
  intro append.
  intro s_append.
  assert (S_append := s_append).
  unfold specification_of_append in s_append.
  split.

  apply(unfold_reverse_v1_bc T).

  destruct s_append as [base_a indu_a].
  intros x.
  induction xs' as [ | xs'' IHxs''].
    rewrite -> (unfold_reverse_v1_bc T).
    rewrite -> (base_a (x :: nil)).
    rewrite -> (unfold_reverse_ds_induction_case T x).
    rewrite -> (unfold_reverse_ds_base_case T).
    rewrite -> (nil_is_neutral_for_append_on_the_left T).
    reflexivity.

    unfold specification_of_append.
    split.
      apply (unfold_append_v1_base_case T).
  
      intros x0 xs' ys.
      apply (unfold_append_v1_induction_case T x0 xs' ys).
    
    unfold reverse_v1.
    rewrite -> (unfold_reverse_ds_induction_case T x ( xs'' :: IHxs'')).
    Check there_is_only_one_append.
    rewrite -> (there_is_only_one_append 
                  T append (append_v1 T)
                  S_append
                  (append_v1_fits_the_specification_of_append T)
                  (reverse_ds T (xs'' :: IHxs''))
                  (x :: nil)).                                         
    reflexivity.
Qed.