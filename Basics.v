Module Playground1.
Definition pred (n :nat) : nat :=
  match n with
      | O => O
      | S n' => n'
  end.
End Playground1.

Definition minustwo (n : nat) : nat :=
  match n with
      | O => O
      | S O => O
      | S (S n') => n'
  end.

Module Playground2.

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
      | O => m
      | S n' => S (plus n' m)
  end.

Eval compute in (plus (S (S (S O))) (S (S O))).

Fixpoint mult (n m : nat) : nat :=
  match n with
    | O => O
    | S n' => plus m (mult n' m)
  end.

Example test_mult1: (mult 3 3) = 9.
Proof. reflexivity. Qed.

Fixpoint minus (n m : nat) : nat :=
  match n, m with
      | O, _ => O
      | S _ , O => n
      | S n', S m' => minus n' m'
  end.

End Playground2.

Fixpoint exp (base power : nat) : nat :=
  match power with
      | O => S O
      | S p => mult base (exp base p)
  end.

Check O.
Check S.

Fixpoint factorial (n:nat) : nat :=
  match n with
      | O => (S O)
      | S n' => mult n (factorial n')
end.

Example test_factorial1: (factorial 3) = 6.
Proof. reflexivity. Qed.

Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. reflexivity. Qed.

Notation "x + y" := (plus x y) (at level 50, left associativity) : nat_scope.

Theorem plus_0_n : forall n : nat, 0 + n = n.
Proof.
intros n. reflexivity. Qed.

Theorem plus_1_l : forall n : nat, 1 + n = S n.
Proof.
intros n. reflexivity. Qed.

Theorem plus_id_example: forall n m : nat, n = m -> n + n = m + m.
Proof.
  intros n m.
  intros H.
  rewrite -> H.
  reflexivity.
Qed.

Theorem plus_id_exercise : forall n m o : nat, n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros H.
  intros H0.
  rewrite -> H.
  rewrite -> H0.
  reflexivity.
Qed.

Theorem mult_0_plus : forall n m : nat, (0 + n) * m = n * m.
Proof.
  intros n m.
  rewrite -> plus_0_n.
  reflexivity. Qed.

Theorem mult_S_1 : forall n m : nat, m = S n -> m * (1 + n) = m*m.
Proof.
  intros n m.
  intros H.
  rewrite -> plus_1_l.
  rewrite -> H.
  reflexivity.
Qed.

Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => beq_nat n' m'
            end
  end.

Theorem plus_1_neq_0_firsttry : forall n : nat, beq_nat (n + 1) 0 = false.
Proof.
  intros n. destruct n as [| n'].
  reflexivity.
  reflexivity.
 Qed.

Theorem negb_involutive : forall b : bool, negb (negb b) = b.
Proof.
  intros b. destruct b.
  reflexivity.
  reflexivity.
Qed.

Theorem zero_nbeq_plus_1 : forall n : nat, beq_nat 0 (n + 1) = false.
Proof.
  intros n.
  destruct n as [| n'].
  reflexivity.
  reflexivity.
Qed.

Theorem identity_fn_applied_twice : forall (f : bool -> bool), (forall (x : bool), f x = x) -> forall (b : bool), f (f b) = b.
Proof.
  intro f.
  intro H.
  intro b.
  rewrite -> H.
  rewrite -> H.
  reflexivity.
Qed.