Lemma and_commutative : forall A B, A /\ B -> B /\ A.
Proof.
  intros.
  elim H.
  split.
  exact H1.
  exact H0.
Qed.

Lemma or_commutative : forall A B, A \/ B -> B \/ A.
Proof.
  intros.
  destruct H.
  right; exact H.
  left; exact H.
Qed.s