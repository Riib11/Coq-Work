Theorem plus_2_3 : (S(S O)) + (S(S(S O))) = (S(S(S(S(S O))))).
Proof.
  exact (eq_refl 5).
Qed.

Theorem plus_O_n : (forall n, O + n = n).
Proof.
  intros n.
  exact (eq_refl n).
Qed.
