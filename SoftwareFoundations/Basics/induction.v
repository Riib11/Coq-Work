Theorem plus_n_O : forall n : nat, n = n + O.
Proof.
  intros n.
  induction n as [|n' IHn'].
    (* 0 = 0 *)
    reflexivity.
    (* n = S n' *)
    simpl.
    rewrite <- IHn'.
    reflexivity.
Qed.

Theorem minus_diag : forall n : nat, n - n = 0.
Proof.
  intros n.
  induction n as [|n' IHn'].
    (* 0 - 0 = 0*)
    reflexivity.
    (* S n' - S n' = 0 *)
    simpl.
    rewrite IHn'.
    reflexivity.
Qed.

Theorem mult_0_r : forall n : nat, n * 0 = 0.
Proof.
  intros n.
  induction n as [|n' IHn'].
    (* 0 * 0 = 0 *)
    reflexivity.
    (* S n' * 0 = 0 *)
    simpl.
    rewrite IHn'.
    reflexivity.
Qed.

Fixpoint double (n : nat) :=
  match n with
  | O => O
  | S n' => S( S(double n') )
  end.

(* Lemma double_plus : forall n, double n = n + n.
Proof.
  intros.
  induction n as [|n' IHn'].
    (* 0 = 0 *)
    reflexivity.
    (* double Sn' = Sn' + Sn' *)
    simpl.
    rewrite -> IHn'.
    Admitted. *)

Theorem mult_0_plus' : forall m n : nat, (0 + n) * m  = n * m.
Proof.
  intros.
  assert (H: 0 + n = n). { reflexivity. }
  rewrite H.
  reflexivity.
Qed.

Theorem plus_comm : forall m n : nat, n + m = m + n.
Proof.
  intros.
  induction n as [|n' IHn'].
  induction m as [|m' IHm'].
  (* 0 + 0 = 0 + 0 *)
  reflexivity.
  (* 0 + Sm' = Sm' + 0 *)
  simpl.
  rewrite <- IHm'.
  simpl.
  reflexivity.
  (* Sn' + m = m + Sn' *)
  simpl.
  rewrite <- IHn'.
  

Theorem plus_rearrange : forall n m p q, (n+m) + (p+q) = (m+n) + (p+q).
Proof.
  intros.
  assert (H: n + m = m + n).
  { rewrite plus_comm. reflexivity. }
  