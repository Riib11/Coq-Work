Lemma equality_commutes
  : forall (a b : bool), a = b -> b = a.
Proof.
  intros.
  subst.
  reflexivity.
Qed.