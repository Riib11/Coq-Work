Inductive Nat : Type :=
  | Z : Nat
  | S : Nat -> Nat.

Fixpoint add (m n:Nat) : Nat :=
  match m with
    | Z => n
    | S m' => S (add m' n)
  end.

Notation "m + n" := (add m n).
Notation "0" := Z.
Notation "1" := (S Z).


Lemma s_equality : forall m n:Nat, m = n -> S m = S n.
  intros.
  induction m.
  rewrite H.
  auto.
  rewrite H.
  auto.
Qed.

Lemma add_identity : forall m:Nat, m + 0 = m.
  intros.
  elim m.
  simpl.
  auto.
  simpl.
  intros.
  apply s_equality.
  apply H.
Qed.

Lemma add_s_equality : forall m n:Nat, m + (S n) = S (m + n).
Proof.
  intros.
  induction m.
  simpl.
  reflexivity.
  simpl.
  rewrite IHm.
  reflexivity.
Qed.

Lemma add_s : forall m : Nat, S m = m + (S Z).
Proof.
  intros.
  induction m.
  simpl.
  reflexivity.
  simpl.
  rewrite <- IHm.
  reflexivity.
Qed.

Lemma add_commutative : forall m n:Nat, m + n = n + m.
Proof.
  intros.
  induction m as [ | m IHm ].
  simpl.
  rewrite add_identity.
  reflexivity.
  simpl.
  rewrite add_s_equality.
  rewrite IHm.
  reflexivity.
Qed.

Fixpoint mult (m n : Nat) :=
  match m with
    | Z => Z
    | S m' => n + (mult m' n)
  end.

Notation "m * n" := (mult m n).

Lemma mult_identity : forall m : Nat, m * 1 = m.
Proof.
  intros.
  induction m.
  simpl.
  reflexivity.
  simpl.
  rewrite IHm.
  reflexivity.
Qed.

Lemma mult_zero : forall m : Nat, m * 0 = 0.
Proof.
  intros.
  induction m.
  simpl.
  reflexivity.
  simpl.
  rewrite IHm.
  reflexivity.
Qed.

Lemma add_assoc : forall m n o : Nat, m + (n + o) = (m + n) + o.
Proof.
  intros.
  induction m.
  simpl.
  reflexivity.
  simpl.
  rewrite IHm.
  reflexivity.
Qed.

Lemma mult_distributive : forall m n o : Nat, m * (n + o) = (m * n) + (m * o).
Proof.
Admitted.

Lemma mult_associative : forall m n o : Nat, m * (n * o) = (m * n) * o.
Proof.
Admitted.

Lemma mult_s : forall m n : Nat, m * (S n) = (m * n) + m.
Proof.
Admitted.

Lemma mult_commutative : forall m n : Nat, m * n = n * m.
Proof.
  intros.
  induction m.
  simpl.
  rewrite mult_zero.
  reflexivity.
  simpl.
  rewrite add_s.
  rewrite mult_distributive.
  rewrite mult_identity.
  rewrite IHm.
  rewrite add_commutative.
  reflexivity.
Qed.