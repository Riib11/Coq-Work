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

Definition pierce :=
  forall P Q : Prop,
  ((P -> Q) -> P) -> P.

Definition double_negation_elim :=
  forall P : Prop,
  ~ ~ P = P.

Definition de_morgan_not_and_not :=
  forall P Q : Prop,
  ~ (~P /\ ~Q) -> P \/ Q.

Definition implies_to_or :=
  forall P Q : Prop,
  (P -> Q) -> (~P \/ Q).