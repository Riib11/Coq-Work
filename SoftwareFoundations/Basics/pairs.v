Inductive natprod : Type :=
  | pair : nat -> nat -> natprod.

Notation "( x , y )" := (pair x y).

Definition fst p : nat :=
  match p with | (x,_) => x end.

Definition snd p : nat :=
  match p with | (_,x) => x end.

Definition swap p : natprod :=
  match p with
  | (x,y) => (y,x)
  end.

Ltac pair_simple p := destruct p as [m n]; simpl; reflexivity.

Theorem surjective_pairing : forall p : natprod, p = (fst p, snd p).
Proof.
  intro p. pair_simple p.
Qed.

Theorem snd_fst_is_swap : forall p, swap p = (snd p, fst p).
Proof.
  intro p. pair_simple p.
Qed.

Theorem fst_swap_is_snd : forall p, fst (swap p) = snd p.
Proof.
  intro p. pair_simple p.
Qed.