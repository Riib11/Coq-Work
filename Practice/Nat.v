Module Nat.

Inductive Nat : Type :=
  | O : Nat
  | S : Nat -> Nat.

Notation "1" := (S O).

Fixpoint pred (n:Nat) : Nat :=
  match n with
  | O    => O
  | S n' => n'
  end.

Inductive Vector : Nat -> Type :=
  | vnil  : Vector O
  | vcons : forall n, Nat -> Vector n -> Vector (S n).

Fixpoint
  is_odd (n:Nat) : bool :=
    match n with
    | O    => false
    | S n' => is_even n'
    end
with
  is_even (n:Nat) : bool :=
    match n with
    | O    => true
    | S n' => is_odd n'
    end.

Lemma succ_pred_0 : forall n, n <> O -> S (pred n) = n.
Proof.
  intros n.
  unfold not.
  destruct n as [|n'].
    (* n = O *)
    intros O_neq_O.
    case (O_neq_O (eq_refl : O = O) : False).
    (* n = S n' *)
    intros H. simpl. reflexivity.
Qed.

Lemma succ_pred : forall n, S (pred (S n)) = S n.
Proof.
  intros n. simpl. reflexivity.
Qed.

Fixpoint add (m n:Nat) : Nat :=
  match m with
  | O    => n
  | S m' => S (add m' n)
  end.

Notation "m + n" := (add m n).

Fixpoint mult (m n:Nat) : Nat :=
  match m with
  | O    => O
  | 1  => n
  | S m' => n + (mult m' n)
  end.

Notation "m * n" := (mult m n).

Lemma add_id_right : forall n, n + O = n.
Proof.
  intro n.
  induction n.
    (* base case: O *)
    simpl. reflexivity.
    (* inductive: S n *)
    simpl. rewrite IHn. reflexivity.
Qed.

Lemma succ_add_one : forall n, n + 1 = S n.
Proof.
  intros n.
  induction n as [|n'].
    simpl. reflexivity.
    simpl. rewrite IHn'. reflexivity.
Qed.

Lemma succ_associative_right : forall n m, S (n + m) = n + S m.
Proof.
  intros n m.
  induction n as [|n'].
    (* base case: n = O *)
    simpl. reflexivity.
    (* inductive: n = S n' *)
    simpl. rewrite IHn'. reflexivity.
Qed.

Lemma succ_associative_left : forall n m, S (n + m) = S n + m.
Proof.
  intros n m.
  induction n as [|n'].
    (* base case: n = O *)
    simpl. reflexivity.
    (* inductive: n = S n' *)
    simpl. rewrite IHn'. reflexivity.
Qed.

Lemma add_commutative : forall n m, n + m = m + n.
Proof.
  intros n m.
  induction n as [|n'].
    (* base case: n = O *)
    simpl. rewrite add_id_right. reflexivity.
    (* inductive: n = S n' *)
    simpl. rewrite IHn'. rewrite succ_associative_right. reflexivity.
Qed.

Lemma add_associative : forall n m o, (n + m) + o = n + (m + o).
Proof.
  intros n m o.
  induction n. induction m. induction o.
    simpl. reflexivity.
    simpl. reflexivity.
    simpl. reflexivity.
    simpl. rewrite IHn. reflexivity.
Qed.

Lemma mult_zero_right : forall n, n * O = O.
Proof.
  intro n.
  induction n.
    (* base case: O *)
    simpl. reflexivity.
    (* induction step: S n *)
    simpl. rewrite IHn. destruct n as [|n].
      simpl. reflexivity.
      simpl. reflexivity.
Qed.

Lemma mult_unit_right : forall n, n * 1 = n.
Proof.
  intro n.
  induction n.
    (* base case: O *)
    simpl. reflexivity.
    (* induction step: S n *)
    simpl. rewrite IHn. destruct n as [|n].
      simpl. reflexivity.
      simpl. reflexivity.
Qed.

Inductive Le (n n':Nat) : Type :=
  | le_b   : S n = n' -> Le n n'
  | le_r   : Le n (pred n') -> Le n n'.

Inductive Leeq (n n':Nat) : Type :=
  | leeq_b : n = n -> Leeq n n'
  | leeq_r : Leeq n (pred n') -> Leeq n n'.

Inductive Gr (n n':Nat) : Type :=
  | gr_b   : n = S n' -> Gr n n'
  | gr_r   : Gr n (S n') -> Gr n n'.

Inductive Greq (n n':Nat) : Type :=
  | greq_b : n = n' -> Greq n n'
  | greq_r : Greq n (S n') -> Greq n n'.

Notation "m <  n" := (Le   m n).
Notation "m <= n" := (Leeq m n).
Notation "m >  n" := (Gr   m n).
Notation "m >= n" := (Greq m n).

Lemma le_transitive : forall m n o, m < n -> n < o -> m < o.
Proof.
  intros m n o.
  intros m_le_n n_le_o.
  induction m.
    induction n.
      induction o.
        discriminate.

Lemma helper : forall n, S n <= pred (S (S n)).
Proof.
  intros n. simpl. exact (leeq_b (S n) (S n) eq_refl).
Qed.

Lemma leeq_succ : forall n, n <= S n.
Proof.
  intro n.
  induction n.
    exact (leeq_r O 1 (leeq_b O O eq_refl)).
    exact (leeq_r (S n) (S (S n)) (helper n)).
Qed.

Lemma leeq_succ_S : forall m n, m <= n -> m <= S n.
Proof.
  intros m n m_leeq_n.
  

Lemma lower_bound_O : forall n, O <= n.
Proof.
  induction n.
    exact (leeq_b O O eq_refl).
    destruct n.
    exact (leeq_succ O). exact (leeq_succ

Lemma add_leeq : forall m n, m <= n -> S m <= S n.
Proof.
  intros m n m_leeq_n.
  induction m.
    induction n.
      exact (leeq_b 1 1 eq_refl).
      exact (IHn ())