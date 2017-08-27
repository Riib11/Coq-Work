(* '_l' means "on the left" *)
Theorem plus_1_l : (forall n : nat, 1 + n = S n).
Proof.
  intros n.
  simpl.
  reflexivity.
Qed.

Theorem mult_O_l : (forall n : nat, 0 * n = 0).
Proof.
  intros n.
  simpl.
  reflexivity.
Qed.

Theorem plus_n_O : (forall n : nat, n + 0 = n).
Proof.
  intros n.
  simpl.
  Abort. (* need to use rewriting *)
