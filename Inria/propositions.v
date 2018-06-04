Theorem my_first_proof : forall A : Prop, A -> A.
Proof.
  intros A.
  intros proof_A.
  exact proof_A.
Qed.

Theorem forward_small : forall A B : Prop, A -> (A->B) -> B.
Proof.
  intros.
  pose (proof_B := H0 H).
  exact proof_B.
Qed.

Theorem backward_small : forall A B : Prop, A -> (A->B) -> B.
Proof.
  intros.
  refine (H0 _).
    exact H.
Qed.

Theorem backward_large : forall A B C : Prop, A -> (A->B) -> (B->C) -> C.
Proof.
  intros.
  refine (H1 _).
    refine (H0 _).
      exact H.
Qed.

Theorem backward_huge : forall A B C : Prop, A -> (A->B) -> (A->B->C) -> C.
Proof.
  intros.
  refine (H1 _ _).
    exact H.
    refine (H0 _).
      exact H.
Qed.

Theorem forward_huge : forall A B C : Prop, A -> (A->B) -> (A->B->C) -> C.
Proof.
  intros A B C.
  intros pf_A A_imp_B A_imp_B_imp_C.
  pose (pf_B := A_imp_B pf_A).
  pose (pf_C := A_imp_B_imp_C pf_A pf_B).
  exact pf_C.
Qed.