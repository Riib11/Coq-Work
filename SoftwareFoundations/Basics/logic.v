Theorem modus_ponens
  : forall (P Q : Prop)
  , (P -> Q) -> P -> Q.
Proof.
  intros.
  apply H. exact H0.
Qed.

Theorem modus_tollens
  : forall (P Q : Prop)
  , (P -> Q) -> ~ Q -> ~ P.
Proof.
  unfold not.
  intros.
  pose (H2 := H0 (H H1)).
  exact H2.
Qed.