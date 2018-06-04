Inductive unit : Set :=
  | tt.

Theorem unit_singleton : forall x : unit, x = tt.
  induction x.
  reflexivity.
Qed.

Inductive bool : Set :=
  | true
  | false.

Inductive nat : Set :=
  | O : nat
  | S : nat -> nat.

Definition is_zero (n : nat) : bool :=
  match n with
    | O => true
    | S _ => false
  end.

Definition pred (n : nat) : nat :=
  match n with
    | O => O
    | S n' => n'
  end.

Fixpoint plus (n m : nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.

Theorem O_plus_n : forall n : nat, plus O n = n.
  intro.
  simpl.
  reflexivity.
Qed.

Theorem S_inj : forall n m : nat, S n = S m -> n = m.
  injection 1.
  trivial.
Qed.
