Require Import Bool.

Theorem true_is_True : Is_true true.
Proof.
  simpl.
  exact I.
Qed.

Theorem False_is_unprovable : ~False.
Proof.
  intros proof_False.
  case proof_False.
Qed.

Theorem not_eqb_true_false : ~(Is_true (eqb true false)).
Proof.
  simpl.
  exact False_is_unprovable.
Qed.

Theorem eqb_a_a : (forall a : bool, Is_true (eqb a a)).
Proof.
  intros a.
  case a.
    (* suppose a is true *)
    simpl.
    exact I.
    (* suppose a is false. *)
    simpl.
    exact I.
Qed.

Theorem thm_eqb_a_t : (forall a:bool, (Is_true (eqb a true)) -> (Is_true a)).
Proof.
  intros a.
  case a.
    (* suppose a is true *)
    simpl.
    intros proof_True.
    exact I.
    (* suppos a is false *)
    simpl.
    intros proof_False.
    case proof_False.
Qed.

Theorem and_sym : (forall a b, a && b = b && a).
Proof.
  intros a b.
  case a, b.
    exact (eq_refl true).
    exact (eq_refl false).
    exact (eq_refl false).
    exact (eq_refl false).
Qed.

Theorem neg_nega : (forall a, a <> (negb a)).
Proof.
  intros a.
  unfold not.
  case a.
    intros a_eq_nega.
    simpl in a_eq_nega.
    discriminate a_eq_nega.

    intros a_eq_nega.
    simpl in a_eq_nega.
    discriminate a_eq_nega.
Qed.