(* definition *)
Axiom A : Type.

(* construction *)
Axiom O : A.
Axiom S : A -> A.

(* induction *)
Axiom A_ind
    : forall P : A->Type
    , P O
   -> (forall (a : A), P a -> P (S a))
   -> (forall (a : A), P a).

Axiom P : forall (a : A), Type.
Axiom P_O : P O.
Axiom P_S : forall (a : A), P a -> P (S a).

Theorem P_all_A : forall (a : A), P a.
Proof.
  exact (A_ind P P_O P_S).
Qed.

Axiom T : forall n : nat, Type.
Axiom T' : nat -> Type.

Check T.
Check T'.