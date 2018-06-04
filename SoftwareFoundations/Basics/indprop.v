Import Nat.

Ltac tacRepeat n tac :=
  match n with
  | O => tac
  | S n => n; tacRepeat n tac
  end.

Inductive ev : nat -> Prop :=
  | ev_O  : ev O
  | ev_SS : forall n, ev n -> ev (S (S n)).

Example ev_4 : ev 4.
Proof. apply ev_SS. apply ev_SS. apply ev_O. Qed.

Lemma plus1_is_S : forall n, n + 1 = S n.
Proof.
  intros. induction n.
    simpl. reflexivity.
    simpl. rewrite IHn. reflexivity.
Qed.

Lemma add4 : 4 = 1 + 1 + 1 + 1.
Proof. simpl. reflexivity. Qed.

Lemma n_add4 : forall n, n + 1 + 1 + 1 + 1 = n + 4.
Proof.
  intros. induction n. simpl. reflexivity.
  simpl. rewrite IHn. reflexivity.
Qed.

Lemma S_commutativity : forall m n, m + S n = S (m + n).
Proof.
  intros.
  induction m. destruct n.
    simpl. reflexivity.
    simpl. reflexivity.
    simpl. rewrite IHm. reflexivity.
Qed.

Lemma S_distributivity : forall n, S (S (n + n)) = S n + S n.
Proof.
  intros. simpl. destruct n.
    simpl. reflexivity.
    simpl. rewrite <- S_commutativity. reflexivity.
Qed.

Example ev_plus4 : forall n, ev n -> ev (4 + n).
Proof.
  intros.
  destruct n.
    simpl. apply ev_SS. apply ev_SS. exact H.
    simpl. apply ev_SS. apply ev_SS. exact H.
Qed.

Theorem ev_double : forall n, ev (double n).
Proof.
  intros.
  induction n.
    simpl. exact ev_O.
    unfold double. unfold double in IHn. simpl.
    rewrite S_commutativity.
    apply ev_SS in IHn.
    exact IHn.
Qed.

