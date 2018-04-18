Load LogicBasics.

Theorem Problem3 : forall A B C : Prop, (A \/ B) /\ C -> (A /\ C) \/ (B /\ C).
Proof.
  intros A B C.
  intros G.
  destruct G.
  case H.
    intros a.
    exact (or_introl (conj a H0)).
    intros b.
    exact (or_intror (conj b H0)).
Qed.


Theorem thm_eq_trans__again : (forall x y z: Set, x = y -> y = z -> x = z).
Proof.
  intros x y z.
  intros x_y y_z.
  rewrite x_y.
  rewrite <- y_z.
  exact (eq_refl y).
Qed.


Theorem Problem4 : forall A B : Prop, ~(A <-> B) -> ~(B <-> A).
Proof.
  intros.
  unfold not in H.
  unfold iff in H.
  case H.
  admit.

Lemma lemma5_1 : forall A B : Prop, A -> A.
Proof.
  intros.
  exact H.
Qed.