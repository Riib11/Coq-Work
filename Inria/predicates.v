Require Import Bool.

Definition basic_predicate :=
  (fun a => Is_true (andb a true)).

Theorem exists_basics : ex basic_predicate.
Proof.
  pose (witness := true).
  refine (ex_intro basic_predicate witness _).
    simpl.
    exact I.
Qed.

Theorem exsists_basics : exists a, Is_true (andb a true).
Proof.
  pose (witness := true).
  refine (ex_intro _ witness _).
    simpl.
    exact I.
Qed.

Theorem basic_forall_exists : forall b, exists a, Is_true (eqb a b).
Proof.
  intros b.
  case b.
    (* b = true *)
    pose (witness := true).
    refine (ex_intro _ witness _).
      simpl.
      exact I.
    (* b = false *)
    pose (witness := false).
    refine (ex_intro _ witness _).
      simpl.
      exact I.
Qed.

Theorem forall_exists : forall P : Set -> Prop, (forall x, ~(P x)) -> ~(exists x, P x).
Proof.
  intros P.
  intros fa_x_not_Px.
  unfold not.
  intros ex_x_Px.
  destruct ex_x_Px as [ witness pf_Pwitness ].
  pose (not_Pwitness := fa_x_not_Px witness).
  unfold not in not_Pwitness.
  pose (pf_False := not_Pwitness pf_Pwitness).
  case pf_False.
Qed.

Theorem eq_symetric : forall x y : Set, x = y -> y = x.
Proof.
  intros x y x_eq_y.
  destruct x_eq_y.
  exact (eq_refl x).
Qed.

Theorem eq_transitive : forall x y z : Set, x = y -> y = z -> x = z.
Proof.
  intros x y z x_eq_y y_eq_z.
  destruct x_eq_y.
  destruct y_eq_z.
  exact (eq_refl x).
Qed.

Theorem eq_transitive_1 : forall x y z : Set, x = y -> y = z -> x = z.
Proof.
  intros x y z x_eq_y y_eq_z.
  rewrite x_eq_y.
  rewrite <- y_eq_z.
  exact (eq_refl y).
Qed.

Theorem andb_symmetric : forall a b, a && b = b && a.
Proof.
  intros a b.
  case a, b.
    simpl. exact (eq_refl true).
    simpl. exact (eq_refl false).
    simpl. exact (eq_refl false).
    simpl. exact (eq_refl false).
Qed.

Theorem neq_nega : forall a, a <> negb a.
Proof.
  intros a.
  unfold not.
  case a.
    simpl.
    intros true_eq_false.
    discriminate true_eq_false.
    simpl.
    intros false_eq_true.
    discriminate false_eq_true.
Qed.
