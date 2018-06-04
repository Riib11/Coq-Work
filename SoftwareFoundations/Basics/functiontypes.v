Module functionplayground.

Fixpoint factorial (n:nat) : nat :=
  match n with
  | O => 1
  | S O => 1
  | S n' => (S n') * (factorial n')
  end.

Example test_factorial1 : factorial 3 = 6.
Proof. simpl. exact eq_refl. Qed.

Example test_factorial2 : factorial 5 = 10 * 12.
Proof. simpl. exact eq_refl. Qed.

Notation "x !" := (factorial x) (at level 50) : nat_scope.

Theorem andb_true_elim2 : forall b c : bool, andb b c = true -> c = true.
Proof.
  intros b c.
  destruct b, c.
    simpl. reflexivity.
    simpl. discriminate.
    simpl. discriminate.
    simpl. discriminate.
Qed.