Theorem forward_huge : (forall A B C : Prop, A -> (A->B) -> (A->B->C) -> C).
Proof.
  intros A B C.
  intros proof_A A_imp_B A_imp_B_imp_C.
  pose (proof_B := A_imp_B proof_A).
  pose (proof_C := A_imp_B_imp_C proof_A proof_B).
  exact proof_C.
Qed.