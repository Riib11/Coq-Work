Lemma leibniz_equality : forall (X : Type) (x y : X),
  x = y -> forall (P : X->Prop), P x -> P y.
Proof.
  intros.
  rewrite H in H0. exact H0.
Qed.
