Proposition plus_1_s :
  forall n : nat,
    S n = plus 1 n.
Proof.
  intro n.
  unfold plus.
  reflexivity.
Qed.