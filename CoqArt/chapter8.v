Example ex_8_11 : forall n p : nat, n < p -> n <= p.
Proof.
  intros n p;
  apply le_ind;
  repeat constructor;
  assumption.
Qed.

Example ex_8_13 : forall n p q : nat, n <= p -> p <= q -> n <= q.
Proof.
  intros n p q.
  intros Hnp.
  apply le_ind.

  assumption.

  intros m Hpm Hnm.
  apply le_S. assumption.
Qed.

Inductive le_diff (n m : nat) : Prop :=
  le_d : forall x : nat, x + n = m -> le_diff n m.

Example ex_8_14 : forall n m : nat, n <= m <-> le_diff n m.
Proof.
  intros n m.
  split.

  intro n_le_m.
  split with (x := 0).
