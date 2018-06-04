Theorem True_provable : True.
Proof.
  exact I.
Qed.

Definition not (A:Prop) := A -> False.

Notation "~ x" := (not x) : type_scope.

Theorem False_unprovable : ~ False.
Proof.
  unfold not.
  intros pf_False.
  exact pf_False.
Qed.

Theorem False_unprovable_again : ~ False.
Proof.
  unfold not.
  intros pf_False.
  case pf_False.
Qed.

Theorem True_not_implies_False : ~ (True -> False).
Proof.
  unfold not.
  intros True_imp_False.
  pose (pf_False := True_imp_False I).
  case pf_False.
Qed.

Theorem False_implies_True : False -> True.
Proof.
  intros pf_False.
  case pf_False.
Qed.

Theorem False_implies_False : False -> False.
Proof.
  intros pf_False.
  case pf_False.
Qed.

Require Import Bool.

Theorem true_is_True : Is_true true.
Proof.
  simpl.
  exact I.
Qed.

Theorem not_true_eqb_false : ~ (Is_true (eqb true false)).
Proof.
  simpl.
  exact False_unprovable.
Qed.

Theorem left_or : forall A B : Prop, A -> A \/ B.
Proof.
  intros A B pf_A.
  pose (pf_A_or_B := or_introl pf_A : A \/ B).
  exact pf_A_or_B.
Qed.

Theorem right_or : forall A B : Prop, B -> A \/ B.
Proof.
  intros A B pf_B.
  pose (pf_A_or_B := or_intror pf_B : A \/ B).
  exact pf_A_or_B.
Qed.

Theorem or_commutes : forall A B, A \/ B -> B \/ A.
Proof.
  intros A B pf_A_or_B.
  case pf_A_or_B.
    (* right *)
    intros pf_A.
    refine (or_intror _).
    exact pf_A.
    (* left *)
    intros pf_B.
    refine (or_introl _).
    exact pf_B.
Qed.

Theorem both_and : forall A B : Prop, A -> B -> A /\ B.
Proof.
  intros A B pf_A pf_B.
  pose (pf_A_and_B := conj pf_A pf_B).
  exact pf_A_and_B.
Qed.

Theorem and_commutes : forall A B : Prop, A /\ B -> B /\ A.
Proof.
  intros A B pf_A_and_B.
  case pf_A_and_B.
  intros pf_A pf_B.
  pose (pf_B_and_A := conj pf_B pf_A).
  exact pf_B_and_A.
Qed.

Theorem and_commutes_1 : forall A B : Prop, A /\ B -> B /\ A.
Proof.
  intros A B pf_A_and_B.
  case pf_A_and_B.
  intros pf_A pf_B.
  refine (conj _ _).
    exact pf_B.
    exact pf_A.
Qed.

Theorem and_commutes_2 : forall A B : Prop, A /\ B -> B /\ A.
Proof.
  intros A B pf_A_and_B.
  destruct pf_A_and_B as [ pf_A pf_B ].
  refine (conj _ _).
    exact pf_B.
    exact pf_A.
Qed.

Theorem orb_is_or : forall a b, Is_true (orb a b) <-> Is_true a \/ Is_true b.
Proof.
  intros a b.
  unfold iff.
  refine (conj _ _).
    (* forward *)
    intros H.
    case a, b.
      simpl.
      exact (or_introl I).
      exact (or_introl I).
      exact (or_intror I).
      simpl in H.
      case H.
    (* backward *)
    intros H.
    case a, b.
      simpl. exact I.
      simpl. exact I.
      simpl.
      case H.
        simpl. exact False_implies_True.
        simpl. intros pf_True. exact I.
      simpl in H.
      case H.
        simpl. exact False_implies_False.
        simpl. exact False_implies_False.
Qed.