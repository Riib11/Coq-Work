Inductive nat : Set :=
  | O : nat
  | S : nat -> nat.

Fixpoint plus (m n : nat) : nat :=
  match m with
    | O => match n with
        | O => O
        | S n' => S n'
      end
    | S m' => match n with
        | O => S m'
        | S n' => S (S (plus m' n'))
      end
  end.

Theorem S_injective : forall m n : nat, S m = S n -> m = n.
  injection 1.
  trivial.
Qed.

Theorem O_left_id : forall m : nat, plus O m = m.
  intros.
  case m.
    (* m = O *)
    simpl.
    trivial.
    (* m = S m' *)
    intros.
    simpl.
    trivial.
Qed.

Theorem O_right_id : forall m : nat, plus m O = m.
    intros.
  case m.
    (* m = O *)
    simpl.
    trivial.
    (* m = S m' *)
    intros.
    simpl.
    trivial.
Qed.

Theorem O_id : forall m : nat, plus O m = m /\ plus m O = m.
  intros.
  refine (conj _ _).
    apply O_left_id.
    apply O_right_id.
Qed.