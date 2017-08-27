Theorem thm_false_imp_true : False -> True.
Proof.
  intros proof_False.
  exact I.
Qed.

Theorem thm_false_imp_false : False -> False.
Proof.
  intros proof_False.
  case proof_False. (* no proofs... *)
Qed.

Theorem thm_true_imp_false : ~(True -> False).
Proof.
  intros T_imp_F. (* assume ~(True->False) *)
  refine (T_imp_F _). (* need a proof of true for this *)
    exact I. (* got a proof of true! *)
Qed.

Theorem absurd2 : forall A C : Prop, A -> ~A -> C.
Proof.
  intros A C.
  intros proof_A unproof_A.
  unfold not in unproof_A.
  pose (proof_False := unproof_A proof_A).
  case proof_False.
Qed.