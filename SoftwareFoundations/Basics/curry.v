Definition add1 : nat -> nat.
  intro n.
  apply S.
  apply n.
Defined.

Definition and_comm'_aux P Q (H : P /\ Q) :=
  match H with
  | conj HP HQ => conj HQ HP
  end.

Definition conj_fact : forall P Q R, P /\ Q -> Q /\ R -> P /\ R.
  intros.
  refine (conj _ _).
    destruct H. apply H.
    destruct H0. apply H1.
Qed.

Definition or_comm : forall P Q, P \/ Q -> Q \/ P.
  intros.
  case H.
    intro pf_P.
    refine (or_intror _). apply pf_P.
    intro pf_Q.
    refine (or_introl _). apply pf_Q.
Qed.

Inductive ev : nat -> Prop :=
  | ev_O  : ev O
  | ev_SS : forall n, ev n -> ev (S (S n)).

Definition some_nat_is_even : exists n, ev n.
  exists O.
  apply ev_O.
Defined.

(* forall (A : Type) (P : A -> Prop) (x : A), P x -> exists y, P y *)

Definition ex_ev_Sn : ex (fun n => ev (S n)).
  exists 1.
  apply (ev_SS O ev_O).
Defined.