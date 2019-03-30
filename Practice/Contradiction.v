Theorem noncontradiction : forall P : Prop, P /\ ~ P -> False.
Proof.
  intros P pf_P_and_nP.
  unfold not in pf_P_and_nP.
  destruct pf_P_and_nP as (pf_P & pf_nP).
  exact (pf_nP pf_P).
Qed.

Theorem explosion : forall P : Prop, False -> P.
Proof.
  intros P pf_False.
  case pf_False.
Qed.