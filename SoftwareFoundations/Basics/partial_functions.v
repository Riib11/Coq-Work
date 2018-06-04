Require Import Setoid.

Definition relation (X : Type) := X -> X -> Prop.

Definition partial_function {X : Type} (R : relation X) :=
  forall (x y1 y2 : X), R x y1 -> R x y2 -> y1 = y2.

Inductive next_nat (n : nat) : nat -> Prop :=
  nn : next_nat n (S n).

Theorem next_nat_is_partial : partial_function next_nat.
Proof.
  unfold partial_function.
  intros.
  destruct H.
  destruct H0.
  reflexivity.
Qed.

Theorem le_isnt_partial : ~ (partial_function le).
Proof.
  unfold partial_function.
  unfold not.
  intros.
  pose (H1 := H 1 1 2).
  pose (le_1_1 := le_n 1).
  pose (le_1_2 := le_S 1 1 (le_n 1)).
  pose (H2 := H1 le_1_1 le_1_2).
  inversion H2.
Qed.

Definition reflexive {X : Type} (R : relation X) :=
  forall (a : X), R a a.

Theorem le_reflexive : reflexive le.
Proof.
  unfold reflexive.
  intros.
  exact (le_n a).
Qed.

Definition transitive {X : Type} (R : relation X) :=
  forall (a b c : X), R a b -> R b c -> R a c.

Theorem x : 0 <= 1.
Proof.
  apply le_S.
  apply le_n.

Theorem le_S : forall n m, n <= m -> n <= S m.
Proof.
  intros.
  induction n. induction m.
    apply le_S. apply le_n.
    apply le_S. exact H.
    apply le_S. exact H.
Qed.

Theorem le_O_S : forall n, 0 <= S n -> 0 <= n.
Proof.
Admitted.

Theorem le_implies_le_S : forall n m, S n <= m -> n <= m.
Proof.
Admitted.

Theorem le_transitive : transitive le.
Proof.
  unfold transitive.
  intros.
  induction a. induction b. induction c.
    apply le_n.
    apply H0.
    apply IHb.
    pose (H1 := le_O_S b H).
    apply H1.
    apply le_implies_le_S.
    apply H0.
Admitted.

Theorem le_S_S : forall n m, S n <= S m -> n <= m.
Admitted.

Theorem le_Sn_n_inf : forall n, ~(S n <= n).
Proof.
  unfold not.
  intros.
  induction n.
    inversion H.
    apply IHn.
    pose (H1 := le_S_S (S n) n H).
    apply H1.
Qed.

Definition symmetric {X : Type} (R : relation X) :=
  forall (a b : X), R a b -> R b a.

Theorem le_not_symmetric : ~ symmetric le.
Proof.
  unfold not.
  unfold symmetric.
  intros.
  cut (0 <= 1). intro.
  pose (H2 := H 0 1 H0).
  cut ( ~(0 <= 1) ).
  intro.
  contradiction.
  unfold not.
  intro.
  inversion H2.
  apply le_S.
  apply le_n.
Qed.

Definition antisymmetric {X : Type} (R : relation X) :=
  forall (a b : X), R a b -> R b a -> a = b.

Theorem le_antisymmetric : antisymmetric le.
Proof.
  unfold antisymmetric.
  intros.
  inversion H.
  apply eq_refl.
  inversion H1.
  rewrite H2. rewrite <- H3.
  induction a. induction b.
    reflexivity.
    inversion H0.
Admitted.

Definition equivalence {X : Type} (R : relation X) :=
  reflexive R /\ symmetric R /\ transitive R.

Definition order {X : Type} (R : relation X) :=
  reflexive R /\ antisymmetric R /\ transitive R.

Definition preorder {X : Type} (R : relation X) :=
  reflexive R /\ transitive R.

Theorem le_order : order le.
Proof.
  unfold order.
  refine (conj _ _).
  apply le_reflexive.
  refine (conj _ _).
  apply le_antisymmetric.
  apply le_transitive.
Qed.

Inductive clos_refl_trans {A : Type} (R : relation A) : relation A :=
| rt_step : forall x y, R x y -> clos_refl_trans R x y
| rt_refl : forall x, clos_refl_trans R x x
| rt_trans : forall x y z,
    clos_refl_trans R x y ->
    clos_refl_trans R y z ->
    clos_refl_trans R x z.

Theorem next_nat_closure_is_le : forall n m,
  n <= m <-> (clos_refl_trans next_nat) n m.
Proof.
  intros.
  unfold iff.
  refine (conj _ _).
  intros.
  induction n. induction m.
  exact (rt_refl next_nat 0).