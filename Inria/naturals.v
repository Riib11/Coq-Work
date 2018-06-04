Theorem plus_2_3 : 2 + 3 = 5.
Proof.
  simpl.
  exact (eq_refl 5).
Qed.

Theorem plus_O_n : forall n, O + n = n.
Proof.
  intros n.
  simpl.
  exact (eq_refl n).
Qed.

Theorem plus_n_O : forall n, n + O = n.
Proof.
  intros n.
  elim n.
  simpl.
  exact (eq_refl 0).
  intros n'.
  intros IH.
  simpl.
  rewrite IH.
  exact (eq_refl (S n')).
Qed.


Theorem plus_sym : forall m n, m + n = n + m.
Proof.
  intros n m.
  elim n.
    simpl.
    rewrite plus_n_O.
    exact (eq_refl m).

    elim m.
      simpl.
      intros n'.
      rewrite plus_n_O.
      simpl.
      intros np_eq_np.
      exact (eq_refl (S n')).


      intros n'.
      intros IH_n.
      intros m'.
      