Theorem left_or : (forall A B : Prop, A -> A \/ B).
Proof.
  intros A B.
  intros proof_A.
  pose (proof_A_or_B := or_introl proof_A : A \/ B).
  exact proof_A_or_B.
Qed.

Theorem right_or : (forall A B : Prop, B -> A \/ B).
Proof.
  intros A B.
  intros proof_B.
  pose (proof_A_or_B := or_intror proof_B : A \/ B).
  exact proof_A_or_B.
Qed.

Theorem alternative_right_or : (forall A B : Prop, B -> A \/ B).
Proof.
  intros A B.
  intros proof_B.
  refine (or_intror _).
    exact proof_B.
Qed.

Theorem or_commutes : (forall A B : Prop, A \/ B -> B \/ A).
Proof.
  intros A B.
  intros A_or_B.
  case A_or_B.
    (* suppose a is true *)
    intros proof_A.
    refine (or_intror _).
      exact proof_A.
    (* suppose b us true *)
    intros proof_B.
    refine (or_introl _).
      exact proof_B.
Qed.