Theorem forall_exists : (forall P: Set -> Prop, (forall x, ~(P x)) -> ~(exists x, P x)).
Proof.
  intros P.
  intros forall_x_not_Px.
  unfold not.
  intros exists_x_Px.
  destruct exists_x_Px as [ witness proof_Pwitness ].
  pose (not_Pwitness := forall_x_not_Px witness).
  unfold not in not_Pwitness.
  pose (proof_False := not_Pwitness proof_Pwitness).
  case proof_False.
Qed.

Theorem exists_forall : (forall P : Set -> Prop, ~(exists x, P x) -> (forall x, ~(P x))).
Proof.
  intros P.
  intros not_exists_x_Px.
  intros x.
  unfold not.
  intros P_x.
  unfold not in not_exists_x_Px.
  refine (not_exists_x_Px _).
    exact (ex_intro P x P_x).
Qed.