Variables A B C : Prop.

Lemma and_commutative : A /\ B -> B /\ A.
Proof.
  intros.
  destruct H.
  exact (conj H0 H).
Qed.

Lemma or_commutative : A \/ B -> B \/ A.
Proof.
  intros.
  destruct H.
    exact (or_intror H).
    exact (or_introl H).
Qed.

Variables a b c : bool.

