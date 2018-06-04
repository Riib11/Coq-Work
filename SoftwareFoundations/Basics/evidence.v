Import Nat.

Inductive ev : nat -> Prop :=
  | ev_O  : ev O
  | ev_SS : forall n, ev n -> ev (S (S n)).

Theorem ev_minus2 : forall n, ev n -> ev (pred (pred n)).
Proof.
  intros.
  inversion H as [| n' H'].
    simpl. exact ev_O.
    simpl. exact H'.
Qed.

Theorem evSS_ev : forall n, ev (S (S n)) -> ev n.
Proof.
  intros.
  inversion H.
    exact H1.
Qed.

Theorem one_not_even : ~ ev 1.
Proof. unfold not. intros H. inversion H. Qed.

Theorem SSSS_ev_even : forall n, ev (S (S (S (S n)))) -> ev n.
Proof.
  intros.
  inversion H.
  apply evSS_ev in H1. exact H1.
Qed.

Theorem even5_nonsense : ev 5 -> 2 + 2 = 9.
Proof.
  intros. inversion H. inversion H1.
  apply one_not_even in H3.
  case H3.
Qed.

Lemma ev_even_firsttry : forall n, ev n -> exists k, n = double k.
Proof.
  intros.
  inversion H as [|n' H'].
    exists O. unfold double. simpl. reflexivity.
    assert (I : (exists k', n' = double k') ->
                (exists k, S (S n') = double k)).
    { intros [k' Hk']. rewrite Hk'. exists (S k'). Admitted.
(*    apply I. (* reduce the original goal to the new one *) *)

Hello