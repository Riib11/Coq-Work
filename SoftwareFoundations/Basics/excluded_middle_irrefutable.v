Theorem exluded_middle_irrefutable :
  forall P : Prop, ~ ~ (P \/ ~ P).
Proof.
  unfold not.
  intros P H.
  apply H.
  right.
  intro p.
  apply H.
  left.
  exact p.
Qed.

