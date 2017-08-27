Theorem plus_n_O : (forall n, n + O = n).
Proof.
  intros n.
  elim n.
    exact (eq_refl O).
    intros n' ind_hyp.
    simpl.
    rewrite ind_hyp.
    exact (eq_refl (S n')).
Qed.

Theorem plus_sym : (forall a b, a + b = b + a).
Proof.
  intros a b.
  elim a.
    elim b.
      (* base case foor a *)
      exact (eq_refl (O + O)).
      (* ind case a *)
      intros a' ind_hyp_a.
      simpl.
      rewrite <- ind_hyp_a. (* this makes the substitution on the right side *)
      simpl.
      exact (eq_refl (S a')).
      (* ind case b *)
      intros b' ind_hyp_b.
      simpl.
      rewrite ind_hyp_b. (* this makes the substitution on the left side *)
      elim b.
      (* base case for a *)
        simpl.
        exact (eq_refl (S b')).
        intros a' ind_hyp_a.
        simpl.
        rewrite ind_hyp_a.
        exact (eq_refl (S(a'+S b'))).
Qed.

Theorem plus_sym_again : (forall a b, a + b = b + a).
Proof.
  intros a b.
  elim a.
    elim b.
      (* base case *)
      exact (eq_refl (O+O)).
      (* ind on a *)
      intros a' ind_hyp_a.
      simpl.
      rewrite <- ind_hyp_a.
      simpl.
      exact (eq_refl (S a')).
      (* ind on b *)
      intros b' ind_hyp_b.
      simpl.
      rewrite ind_hyp_b.
      elim b.
        (* base case b' *)
        simpl.
        exact (eq_refl (S b')).
        (* ind on b' *)
        intros a' ind_hyp_a.
        simpl.
        rewrite ind_hyp_a.
        exact (eq_refl (S(a'+S b'))).
Qed.

Theorem minus_is_wierd : (0-1) = (0-2).
Proof.
  simpl.
  exact (eq_refl 0).
Qed.