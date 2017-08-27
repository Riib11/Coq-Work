Theorem both_and : (forall A B : Prop, A -> B -> A /\ B).
Proof.
  intros A B.
  intros proof_A proof_B.
  refine (conj _ _).
    exact proof_A.
    exact proof_B.
Qed.

Theorem and_commutes : (forall A B : Prop, A /\ B -> B /\ A).
Proof.
  intros A B.
  intros proof_A_and_B.
  case proof_A_and_B.
    intros proof_A proof_B.
    refine (conj _ _).
      exact proof_B.
      exact proof_A.
Qed.

Theorem and_commutes_again : (forall A B : Prop, A /\ B -> B /\ A).
Proof.
  intros A B.
  intros proof_A_and_B.
  destruct proof_A_and_B as [ proof_A proof_B ].
  refine (conj _ _).
    exact proof_B.
    exact proof_A.
Qed.