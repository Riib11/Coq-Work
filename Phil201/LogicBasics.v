Theorem and_reflexive : forall A B : Prop, A /\ B -> B /\ A.
Proof.
  intros A B A_and_B.
  destruct A_and_B.
  exact (conj H0 H).
Qed.