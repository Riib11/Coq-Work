Theorem plus_id : (forall m n : nat, m=n -> n+n = m+m).
Proof.
  intros m n.
  intros m_eq_n.
  rewrite -> m_eq_n.
  reflexivity.
Qed.

Theorem plus_id_exercise : (forall m n o : nat, n = m -> m = o -> n + m = m + o).
Proof.
  intros m n o.
  intros n_eq_m n_eq_o.
  rewrite -> n_eq_m.
  rewrite <- n_eq_o.
  reflexivity.
Qed.

Theorem mult_S_1 : (forall m n : nat, m = S n -> m * (1 + n) = m * m).
Proof.
  intros n m.
  intros n_eq_Sm.
  simpl.
  rewrite -> n_eq_Sm.
  reflexivity.
Qed.

