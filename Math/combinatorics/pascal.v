Notation Nat := nat.

Fixpoint factorial (n:Nat) : Nat :=
  match n with
  | O   => 1
  | S n => (S n) * factorial n
  end.

Fixpoint eq_nat (n m:Nat) : bool :=
  match n,m with
  | O  ,O   => true
  | S _,O   => false
  | O  ,S _ => false
  | S o,S p => eq_nat o p
  end.

Fixpoint subtract (n m:Nat) : Nat :=
  match n,m with
  | O  ,_   => O
  | S _,O   => n
  | S o,S p => subtract o p
  end.

Inductive Fraction : Set :=
  | frac : forall (n d:Nat), d <> O -> Fraction.

Lemma add_id_right : forall n, n + O = n.
Proof.
  intro n.
  induction n.
  simpl. reflexivity.
  simpl. rewrite IHn. reflexivity.
Qed.

Lemma succ_gt_O : forall n, S n > O.
Proof.
  intro n.
  induction n.
  auto.
  auto.
Qed.

Lemma factorial_gt_O : forall (n:Nat), factorial n > O.
Proof. Admitted.

Lemma product_preserves_gt_O :
  forall (n m:Nat), n > O -> m > O -> n * m > O.
Proof. Admitted.

Lemma gt_O_implies_neq_O : forall n, n > O -> n <> O.
Proof.
  intros n n_gt_O.
  unfold not. intro n_eq_O.
  destruct n_gt_O.
  discriminate.
  discriminate.
Qed.

Definition binomial (n k:Nat) : Fraction.
  refine (frac _ _ _).
  exact (factorial n).
  pose (d := ((factorial (subtract n k)) * (factorial k))).
  cut (d > O). intro d_gt_O.
  apply gt_O_implies_neq_O in d_gt_O.
  apply d_gt_O.
  apply product_preserves_gt_O.
  apply factorial_gt_O.
  apply factorial_gt_O.
Qed.

Compute (binomial 2 1).

Lemma one_neq_O : 1 <> O. Proof. Admitted.

Lemma x : forall n m, binomial n m = frac 1 1 one_neq_O.
  intros.
  simpl. 